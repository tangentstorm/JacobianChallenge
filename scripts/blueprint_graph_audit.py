#!/usr/bin/env python3
"""Audit the blueprint dependency graph for connectivity to the challenge API.

The dep graph is encoded in `\\uses{a,b,...}` annotations. The challenge API
root is `thm:challenge-api` (in `tex/sections/10-main-theorem-assembly.tex`).
A statement counts as "connected" if it (transitively) appears as a
dependency of `thm:challenge-api` — i.e. its label is reachable by walking
backwards along `uses`-edges from the root.

Reports:
  * UNREACHABLE labels — statements that don't flow into the challenge API.
  * UNDEFINED references — `\\uses{X}` where X has no `\\label{X}` anywhere.
  * Per-section unreachable counts.

Statements inside the *Orphaned statements* section
(`\\section{...Orphaned statements...}` or `\\label{sec:orphaned-statements}`)
are excluded from the unreachable set — that section exists exactly so that
genuine dead-end material can live somewhere without polluting the graph.

The script exits non-zero when any reachable-from-root invariant fails, so
it can run in CI.
"""
from __future__ import annotations

import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEX_DIRS = [ROOT / "tex" / "sections", ROOT / "tex" / "statements"]

# Statement environments — same set the leanok auditor uses.
STATEMENT_ENVS = ("theorem", "lemma", "definition", "corollary",
                  "proposition", "classicalinput")

# Labels matching this prefix are considered "statement-shaped" and must be
# reachable. Section/subsection labels (sec:, subsec:, fig:, eq:) are
# infrastructure, not statements.
STATEMENT_LABEL_PREFIXES = (
    "thm:", "lem:", "def:", "prop:", "cor:", "input:", "claim:", "fact:",
    "stmt:",
)

# The root we trace backwards from.
ROOT_LABEL = "thm:challenge-api"

# Marker labels for the orphaned-statements section.
ORPHAN_SECTION_LABELS = {"sec:orphaned-statements"}
ORPHAN_SECTION_TITLE_RE = re.compile(
    r'\\section\*?\{[^}]*\bOrphaned statements?\b[^}]*\}', re.IGNORECASE)


def is_statement_label(label: str) -> bool:
    return any(label.startswith(p) for p in STATEMENT_LABEL_PREFIXES)


def parse_blocks(text: str, file_rel: str):
    """Walk through a tex file, locating each statement-style env block and
    each `\\section{...}` boundary. Yield dicts:

        {file, line, env, label, uses (set of label refs),
         in_orphan_section (bool)}

    `in_orphan_section` tracks whether the block lives under an
    `\\section{... Orphaned statements ...}` heading.
    """
    in_orphan = False
    section_starts: list[tuple[int, bool]] = []  # (offset, was_orphan)

    sec_pat = re.compile(r'\\section\*?\{([^}]*)\}|\\label\{([^}]*)\}')

    # First pass: build a sorted list of (offset, "orphan" | "normal")
    # transitions based on `\\section{...}` headings.
    transitions: list[tuple[int, bool]] = [(0, False)]
    for m in re.finditer(r'\\section\*?\{[^}]*\}', text):
        title = m.group()
        is_orph = bool(ORPHAN_SECTION_TITLE_RE.match(title))
        transitions.append((m.start(), is_orph))

    def orphan_at(off: int) -> bool:
        cur = False
        for o, val in transitions:
            if o > off:
                break
            cur = val
        return cur

    env_alt = "|".join(STATEMENT_ENVS)
    pat_begin = re.compile(r'\\begin\{(' + env_alt + r')\}')
    pos = 0
    while True:
        m = pat_begin.search(text, pos)
        if not m:
            break
        env = m.group(1)
        bs = m.start()
        end_pat = re.compile(r'\\end\{' + re.escape(env) + r'\}')
        em = end_pat.search(text, m.end())
        if not em:
            pos = m.end()
            continue
        body = text[m.end():em.start()]
        lab = re.search(r'\\label\{([^}]*)\}', body)
        label = lab.group(1) if lab else None
        uses_set: set[str] = set()
        for um in re.finditer(r'\\uses\{([^}]*)\}', body, re.DOTALL):
            inside = um.group(1)
            for n in inside.split(","):
                n = n.strip()
                if n:
                    uses_set.add(n)
        line = text.count("\n", 0, bs) + 1
        yield {
            "file": file_rel,
            "line": line,
            "env": env,
            "label": label,
            "uses": uses_set,
            "in_orphan_section": orphan_at(bs),
        }
        pos = em.end()


def collect():
    """Walk every tex file. Return:
        blocks_by_label : label -> block dict
        all_labels      : set of every \\label{...} string seen
        blocks          : list of all blocks (in encounter order)
    """
    blocks: list[dict] = []
    all_labels: set[str] = set()
    blocks_by_label: dict[str, dict] = {}

    label_pat = re.compile(r'\\label\{([^}]*)\}')
    for tex_dir in TEX_DIRS:
        if not tex_dir.exists():
            continue
        for tex_path in sorted(tex_dir.glob("*.tex")):
            text = tex_path.read_text(encoding="utf-8")
            file_rel = tex_path.relative_to(ROOT).as_posix()
            for lm in label_pat.finditer(text):
                all_labels.add(lm.group(1))
            for b in parse_blocks(text, file_rel):
                blocks.append(b)
                if b["label"]:
                    blocks_by_label.setdefault(b["label"], b)
    return blocks, blocks_by_label, all_labels


def reachable_from(root: str, blocks_by_label: dict[str, dict]) -> set[str]:
    """Set of labels (transitively) reached by walking forward along
    `uses` from `root`. Labels appearing in `uses` but not having their own
    block are still added (so they're not silently dropped).
    """
    seen: set[str] = set()
    stack = [root]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        block = blocks_by_label.get(cur)
        if block is None:
            continue
        for dep in block["uses"]:
            if dep not in seen:
                stack.append(dep)
    return seen


def main():
    blocks, blocks_by_label, all_labels = collect()

    if ROOT_LABEL not in blocks_by_label:
        print(f"FAIL: root label {ROOT_LABEL!r} not found in any tex block.",
              file=sys.stderr)
        return 2

    reached = reachable_from(ROOT_LABEL, blocks_by_label)

    # 1. Statement blocks whose label is *not* reached and that are *not*
    #    inside the orphaned-statements section.
    unreachable: list[dict] = []
    orphan_section: list[dict] = []
    nolabel: list[dict] = []
    for b in blocks:
        if b["label"] is None:
            nolabel.append(b)
            continue
        if not is_statement_label(b["label"]):
            continue
        if b["in_orphan_section"]:
            orphan_section.append(b)
            continue
        if b["label"] not in reached:
            unreachable.append(b)

    # 2. \uses references with no matching \label anywhere.
    undefined_refs: dict[str, list[tuple[str, int, str]]] = {}
    for b in blocks:
        for dep in b["uses"]:
            if dep not in all_labels:
                undefined_refs.setdefault(dep, []).append(
                    (b["file"], b["line"], b["label"] or "?"))

    # Per-section unreachable counts
    by_file: dict[str, int] = {}
    for b in unreachable:
        by_file[b["file"]] = by_file.get(b["file"], 0) + 1

    print("Blueprint dependency-graph connectivity audit")
    print("=============================================")
    print(f"  Root label:                          {ROOT_LABEL}")
    print(f"  Total tex labels:                    {len(all_labels)}")
    print(f"  Statement-style env blocks:          {len(blocks)}")
    print(f"  Statement blocks without \\label:    {len(nolabel)}")
    print(f"  In orphaned-statements section:      {len(orphan_section)}")
    print(f"  Reachable from {ROOT_LABEL!r}:       "
          f"{sum(1 for b in blocks if b['label'] in reached)}")
    print(f"  UNREACHABLE statement blocks:        {len(unreachable)}")
    print(f"  UNDEFINED \\uses targets:             {len(undefined_refs)}")
    print()

    if by_file:
        print("Per-section unreachable counts:")
        for f, c in sorted(by_file.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"  {c:4d}  {f}")
        print()

    if unreachable:
        print("=== UNREACHABLE statement blocks "
              "(label, file:line) ===")
        for b in unreachable:
            print(f"  {b['file']}:{b['line']}  [{b['env']}]  "
                  f"{b['label']}  uses={sorted(b['uses']) or '∅'}")
        print()

    if nolabel:
        print(f"=== Statement blocks without \\label ({len(nolabel)}) ===")
        for b in nolabel[:20]:
            print(f"  {b['file']}:{b['line']}  [{b['env']}]")
        if len(nolabel) > 20:
            print(f"  ... and {len(nolabel) - 20} more")
        print()

    if undefined_refs:
        print(f"=== UNDEFINED \\uses targets ({len(undefined_refs)}) ===")
        for dep in sorted(undefined_refs):
            sites = undefined_refs[dep]
            print(f"  {dep}  (referenced by {len(sites)} block"
                  f"{'s' if len(sites) != 1 else ''})")
            for f, l, who in sites[:3]:
                print(f"     - {f}:{l}  in {who}")
            if len(sites) > 3:
                print(f"     ... and {len(sites) - 3} more sites")
        print()

    fail = bool(unreachable or undefined_refs or nolabel)
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
