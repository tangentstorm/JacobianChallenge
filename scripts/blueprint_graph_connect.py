#!/usr/bin/env python3
"""Detect missing `\\uses` edges in `tex/sections/12-classical-analysis-gaps.tex`
that the prose makes clear should exist, and emit the patch.

Scope: this file uses an explicit ``Round N: refine X-rM (...) into Mathlib
(N more passes)'' header convention. Each such header declares that the
following lemmas refine `X-rM`. The first lemma after the header is the
start of the refinement round. So `X-rM` should `\\uses{first-label-of-round}`
to make the connection explicit.

The script is intentionally conservative: it only emits edges suggested by
this convention. Other connectivity gaps (overview-stepwise hooks, bonus
theorems, etc.) are handled manually outside this tool.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
F = ROOT / "tex" / "sections" / "12-classical-analysis-gaps.tex"

# E.g.:
#   "Round 2: refine srt-r1 (Stokes-cut-disks) into Mathlib (5 more passes)"
#   "Round 3: refine hod-r10 into Mathlib (5 more passes)"
#   "Round 4: depth-first refine hod-r12 (self-adjointness gives ...)"
ROUND_RE = re.compile(
    r'\\subsubsection\*\{Round\s+\d+:\s*'
    r'(?:depth-first\s+)?refine\s+'
    r'([a-zA-Z][a-zA-Z0-9-]*-r\d+(?:-[a-zA-Z][a-zA-Z0-9-]*)?)'
    r'[^}]*\}',
    re.IGNORECASE
)
LABEL_RE = re.compile(r'\\label\{([^}]*)\}')


def main():
    text = F.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    # Build (line_no, kind, payload) events
    events: list[tuple[int, str, str]] = []
    for i, line in enumerate(lines, start=1):
        m = ROUND_RE.search(line)
        if m:
            events.append((i, "round", m.group(1)))
        m2 = LABEL_RE.search(line)
        if m2:
            events.append((i, "label", m2.group(1)))

    # For each round event, find next label event (in source order) and
    # propose an edge: refined_label -> first_label_of_round
    proposals: list[tuple[str, str, int]] = []  # (refined, target, header_line)
    for i, (ln, kind, payload) in enumerate(events):
        if kind != "round":
            continue
        refined = "lem:" + payload
        for j in range(i + 1, len(events)):
            ln2, kind2, payload2 = events[j]
            if kind2 == "label" and payload2.startswith("lem:"):
                proposals.append((refined, payload2, ln))
                break

    # Filter out proposals where the edge already exists
    needed: list[tuple[str, str, int]] = []
    for refined, target, ln in proposals:
        # Find the \uses{...} line attached to `refined` (if any). Search
        # for "\label{refined}" then within next 3 lines, look for \uses{...}.
        lab_idx = None
        for k, line in enumerate(lines):
            if f"\\label{{{refined}}}" in line:
                lab_idx = k
                break
        if lab_idx is None:
            continue  # refined label doesn't exist
        uses_text = ""
        for k in range(lab_idx + 1, min(lab_idx + 5, len(lines))):
            if "\\uses{" in lines[k]:
                # Capture across lines until the closing brace
                j2 = k
                buf = []
                start = lines[k].find("\\uses{") + len("\\uses{")
                buf.append(lines[k][start:])
                while "}" not in buf[-1]:
                    j2 += 1
                    if j2 >= len(lines):
                        break
                    buf.append(lines[j2])
                uses_text = "".join(buf)
                uses_text = uses_text[:uses_text.find("}")]
                break
        if target in uses_text.replace(" ", "").replace("\n", "").split(","):
            continue
        needed.append((refined, target, ln))

    print(f"Round-refine edges suggested: {len(needed)} (of {len(proposals)} headers)")
    for refined, target, ln in needed:
        print(f"  L{ln}: {refined} -> {target}")
    return needed


if __name__ == "__main__":
    main()
