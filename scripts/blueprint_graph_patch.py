#!/usr/bin/env python3
"""Apply curated graph-connectivity edits to the blueprint tex sources.

Each entry of EDITS specifies a `\\label{LABEL}` whose `\\uses{...}` clause
should be extended with the listed dependencies. The patcher:
  - finds the line with the label;
  - locates the `\\uses{...}` in the next few lines (or inserts a new one
    immediately after the label if none exists);
  - merges the missing dependencies into the existing list;
  - leaves files unchanged when nothing needs to be added (idempotent).

Run-once tool: edits are applied in place. The corresponding edges are
also documented in `ref/plans/blueprint-connectivity-edits.md`. Re-running
after the edits is a no-op.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEX_DIRS = [ROOT / "tex" / "sections", ROOT / "tex" / "statements"]

# Label -> list of dependencies to ensure are present in its \uses{...}
EDITS: dict[str, list[str]] = {
    # --- Round-refine edges (auto-discovered by blueprint_graph_connect) ---
    "lem:rk-r5-tail-decay": ["lem:rk-r6"],
    "lem:srt-r10":          ["lem:srt-r11"],
    "lem:dis-r10":          ["lem:dis-r11"],
    "lem:hod-r12":          ["lem:hod-r16"],
    "lem:hod-r13":          ["lem:hod-r21"],
    "lem:hod-r14":          ["lem:hod-r26"],
    "lem:hod-r17":          ["lem:hod-r31"],
    "lem:hod-r22":          ["lem:hod-r36"],
    "lem:hod-r27":          ["lem:hod-r41"],

    # --- Section 12 sub-section overview-stepwise hookups ---
    # Each overview-stepwise lemma is the natural top of its R-section.
    # The corresponding spine `input:*` already pulls in the same leaves
    # the overview pulls in; we add an explicit edge so the dep graph
    # carries them as one connected sub-tree.
    "input:rado-triangulation": [
        "lem:rado-overview-stepwise",
        "lem:rado-pl-assembled-is-2mfd",
        "lem:rado-pl-assembled-realisation-homeo",
        "lem:rado-overview-glued-continuous",
        "lem:rado-overview-glued-bijective",
    ],
    "input:tietze-normal-form": ["lem:tietze-overview-stepwise"],
    "input:de-rham-theorem":    ["lem:deRham-overview-stepwise"],
    "input:hodge-decomposition": [
        "lem:hodge-decomposition-overview-stepwise",
    ],
    "input:hodge-deRham": [
        "lem:hodge-deRham-overview-stepwise",
        "lem:hodge-deRham-deRham-bridge",
        "lem:hodge-deRham-uct-bridge",
        "lem:hodge-deRham-real-of-complex",
    ],
    "input:dolbeault": [
        "lem:dolbeault-overview-stepwise",
        "input:bigraded-forms-complex",
    ],
    "input:riemann-roch": [
        "lem:serre-duality-overview-stepwise",
        "input:rr-squeeze",
        "input:stage-a-closeout",
        "input:banach-data-hone",
    ],
    # The polygonal-model spine theorem in section 5.
    "thm:polygonal-model": [
        "lem:polygonal-model-overview-stepwise",
        "lem:polygonal-model-phase12-word-quotient",
        "lem:polygonal-model-phase3-tietze-normal-form",
        "lem:polygonal-model-phase3-quotient-lift",
        "lem:polygonal-model-apply-tietze",
    ],

    # --- Close the round-10/round-11 hod-chain assembly ---
    # `lem:hod-r49` claims "this is the lemma at the head of chain hod
    # (lem:hodge-orthogonal-decomposition)", so the head should pull r49.
    # `lem:hod-r50` is the closing endpoint; r51..r57 form the
    # Round-11 abstract-Hodge-complex chain — link them via r50 + r51.
    "lem:hodge-orthogonal-decomposition": [
        "lem:hod-r49", "lem:hod-r50", "lem:hod-r51",
    ],
    "lem:hod-r50": ["lem:hod-r51"],
    "lem:hod-r51": ["lem:hod-r52"],
    "lem:hod-r52": ["lem:hod-r53"],
    "lem:hod-r53": ["lem:hod-r54"],
    "lem:hod-r54": ["lem:hod-r55"],
    "lem:hod-r55": ["lem:hod-r56"],
    "lem:hod-r56": ["lem:hod-r57"],

    # --- Sobolev / elliptic R6 infrastructure under input:sobolev-elliptic-regularity ---
    "input:sobolev-elliptic-regularity": [
        "lem:real-harmonic-def",
        "lem:abstract-resolvent-self-adjoint",
        "lem:has-laplace-resolvent-finiteDim",
        "lem:model-symbol-isElliptic",
        "lem:smoothfun-def",
        "lem:l2fun-def",
        "lem:hodge-harmonic-finite-dim-substantive",
        "lem:dolbeault-harmonic-finite-dim-substantive",
        "lem:serre-harmonic-finite-dim-substantive",
    ],

    # --- Section 12 local sub-input parents ---
    "input:bundled-omega-k": ["input:cotangent-alternating-bundle"],

    # --- R9 sub-A round-11+ closing leaves ---
    # The label numbering is sparse (no rN for N in [4..10]); the rounds
    # 11/13/16/20 leaves all hang off the bundled-Omega^k headline.
    "input:cotangent-alternating-bundle": [
        "lem:r9subA-cot-r11", "lem:r9subA-cot-r13",
        "lem:r9subA-exp-r16", "lem:r9subA-closure-round20",
    ],

    # --- srt-r1 (Stokes cut disks) Round 2 chain ---
    # The actual label is `lem:srt-r1-stokes-cut-disks`; the
    # auto-detector misses the parenthetical-suffix pattern.
    "lem:srt-r1-stokes-cut-disks": ["lem:srt-r6"],

    # --- R7 sub-A round-11+ leaves: similarly wire the rounds-11-22 batch ---
    # The leaves r12..r30 are listed under
    # "Refinement rounds 11–22 (substantive Mathlib-typed real carriers)"
    # / "Refinement rounds 23--30 (Frechet-derivative shifts)". They are
    # downstream depth refinements of `lem:r7subA-d-split-partial-dbar`
    # (the headline of the bigraded forms decomposition).
    "lem:r7subA-d-split-partial-dbar": [
        "lem:r7subA-r12", "lem:r7subA-r16", "lem:r7subA-r19",
        "lem:r7subA-r20", "lem:r7subA-r22", "lem:r7subA-r23",
        "lem:r7subA-r24", "lem:r7subA-r25", "lem:r7subA-r28",
        "lem:r7subA-r30",
    ],
}


LABEL_RE = re.compile(r'\\label\{([^}]*)\}')
USES_RE = re.compile(r'\\uses\{([^}]*)\}', re.DOTALL)


def parse_uses(text: str, start: int):
    """Find the next `\\uses{...}` after offset `start` (within ~5 lines).
    Returns (begin, end, inside) or (None, None, None)."""
    region = text[start:start + 800]
    m = USES_RE.search(region)
    if not m:
        return None, None, None
    return start + m.start(), start + m.end(), m.group(1)


def merge(existing: list[str], new: list[str]) -> list[str]:
    seen = set(existing)
    out = list(existing)
    for n in new:
        if n not in seen:
            out.append(n)
            seen.add(n)
    return out


def process_file(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    new_text = text
    edits_applied = 0

    for label, deps in EDITS.items():
        # find \label{label}
        pat = re.compile(re.escape(f"\\label{{{label}}}"))
        m = pat.search(new_text)
        if not m:
            continue
        # find following \uses (within ~5 lines)
        scan_start = m.end()
        u_start, u_end, inside = parse_uses(new_text, scan_start)
        # If a non-uses \begin or \label appears before \uses, treat as no
        # existing \uses (insert one).
        # Heuristic: if the closest \uses{...} is more than 200 chars away
        # *and* a new statement env begins before it, skip the insertion.
        next_begin = re.search(r'\\begin\{', new_text[scan_start:scan_start + 800])
        if u_start is not None and next_begin and u_start > scan_start + next_begin.start():
            u_start = None
        if u_start is not None:
            existing = [s.strip() for s in inside.split(",") if s.strip()]
            merged = merge(existing, deps)
            if merged != existing:
                new_inside = ",".join(merged)
                new_text = (new_text[:u_start]
                            + f"\\uses{{{new_inside}}}"
                            + new_text[u_end:])
                edits_applied += 1
        else:
            # Insert a new \uses{...} on its own line right after \label{...}
            line_end = new_text.find("\n", m.end())
            if line_end == -1:
                line_end = len(new_text)
            insertion = "\n\\uses{" + ",".join(deps) + "}"
            new_text = new_text[:line_end] + insertion + new_text[line_end:]
            edits_applied += 1

    if new_text != text:
        path.write_text(new_text, encoding="utf-8")
    return edits_applied


def main():
    total = 0
    for tex_dir in TEX_DIRS:
        for tex_path in sorted(tex_dir.glob("*.tex")):
            n = process_file(tex_path)
            if n:
                rel = tex_path.relative_to(ROOT).as_posix()
                print(f"  {rel}: {n} edits")
                total += n
    print(f"\nTotal label edits: {total}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
