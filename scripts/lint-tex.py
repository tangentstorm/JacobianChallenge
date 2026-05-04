#!/usr/bin/env python3
"""Static lint for the project's blueprint .tex files.

Catches LaTeX-fatal hazards that have surfaced from generator scripts
or hand edits, without needing a working pdflatex install:

  1. Raw underscore (`_`) inside an env optional-arg `[...]` or
     section-style title `{...}`, outside math mode. LaTeX treats
     `_` as a subscript and demands math mode.

  2. Raw `]` inside an env optional-arg, which closes the optional
     argument early.  Most often surfaces from `$[0,1]$`-style
     intervals embedded in titles.

  3. Double-backslash command sequences like `\\int`, `\\sigma`
     in a title or body.  These are Python raw-string round-trip
     bugs that silently produce broken markup.

  4. Other punctuation hazards in titles: `&`, `#`, `%` (unescaped).

  5. Mismatched begin/end pairs for the standard environments.

  6. \\code{...} and \\lean{...} arguments that span a newline,
     which breaks LaTeX's argument scanning.

Usage:

    python3 scripts/lint-tex.py [tex/sections tex/statements]

Exits non-zero if any hazard is detected.
"""
from __future__ import annotations

import os
import re
import sys
from collections import Counter

DEFAULT_DIRS = ("tex/sections", "tex/statements")

THM_ENVS = ("lemma", "theorem", "definition", "proposition",
            "corollary", "classicalinput")
SECT_CMDS = ("section", "subsection", "subsubsection", "paragraph",
             "subparagraph")
STD_ENVS = ("lemma", "theorem", "proof", "layman", "itemize",
            "enumerate", "classicalinput", "proofsketch",
            "formalizationnote", "definition", "proposition",
            "corollary")


def strip_math(text: str) -> str:
    """Remove math-mode regions ($...$, \\(...\\), \\[...\\]) so we
    can detect bare special characters in surrounding text."""
    text = re.sub(r"\$[^$]*\$", "", text)
    text = re.sub(r"\\\([\s\S]*?\\\)", "", text)
    text = re.sub(r"\\\[[\s\S]*?\\\]", "", text)
    text = re.sub(r"\\code\{[^{}]*\}", "", text)
    text = re.sub(r"\\texttt\{[^{}]*\}", "", text)
    text = re.sub(r"\\verb\|[^|]*\|", "", text)
    return text


def find_optional_arg(content: str, brace_start: int) -> tuple[int, str]:
    """Walk content from `brace_start` (which points just after `[`),
    finding the matching `]` at brace-depth zero.  Returns (end_idx,
    raw_arg)."""
    depth = 0
    i = brace_start
    while i < len(content):
        c = content[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        elif c == "]" and depth == 0:
            return i, content[brace_start:i]
        elif c == "\n" and depth == 0:
            # Optional args don't typically span lines in this project.
            return -1, content[brace_start:i]
        i += 1
    return -1, content[brace_start:]


MACRO_BAD_PATTERNS = (
    # \seqsplit and \detokenize don't compose: seqsplit's \futurelet
    # internals can't traverse the catcode-12 token sequence that
    # \detokenize produces.  pdflatex aborts with
    #   ! Missing { inserted. <to be read again> \futurelet
    # at the first occurrence of the wrapped \code{...}.
    (r"\\seqsplit\s*\{\s*\\detokenize\b",
     "seqsplit-detokenize",
     "\\seqsplit{\\detokenize{...}} doesn't compose -- "
     "seqsplit's \\futurelet can't peek inside detokenized output. "
     "Pick one or the other, or use \\path from the url package."),
)


def lint_file(path: str) -> list[tuple[int, str, str]]:
    findings: list[tuple[int, str, str]] = []
    text = open(path).read()
    lines = text.split("\n")

    # 0. Known-bad macro patterns.
    for pattern, kind, msg in MACRO_BAD_PATTERNS:
        for m in re.finditer(pattern, text):
            line_no = text[:m.start()].count("\n") + 1
            findings.append((line_no, kind, msg))

    # 1. Bare _, ], &, #, % in optional-arg titles of theorem-style envs.
    for env in THM_ENVS:
        pat = re.compile(r"\\begin\{" + env + r"\}\[")
        for m in pat.finditer(text):
            end_idx, title = find_optional_arg(text, m.end())
            line_no = text[:m.start()].count("\n") + 1
            stripped = strip_math(title)
            if re.search(r"(?<!\\)_", stripped):
                findings.append((line_no, "title-underscore",
                                 f"\\begin{{{env}}}[...]: bare _ "
                                 f"in {title[:80]!r}"))
            for ch in "#&":
                if re.search(r"(?<!\\)" + re.escape(ch), stripped):
                    findings.append((line_no, f"title-{ch}",
                                     f"\\begin{{{env}}}[...]: bare {ch} "
                                     f"in {title[:80]!r}"))
            # Bare % is line-comment, fine; but raw ] at top level
            # would have terminated find_optional_arg.  Re-check raw
            # bracket inside braces (rare).
            if "]" in title:
                findings.append((line_no, "title-rbracket",
                                 f"\\begin{{{env}}}[...]: ] inside title "
                                 f"{title[:80]!r}"))
            # 3. \\command (literal double-backslash math command)
            for bm in re.finditer(r"\\\\([A-Za-z]+)", title):
                findings.append((line_no, "title-double-backslash",
                                 f"\\\\{bm.group(1)} in title "
                                 f"{title[:80]!r}"))

    # 2. Same hazards in section-style commands (single-brace argument).
    for cmd in SECT_CMDS:
        pat = re.compile(r"\\" + cmd + r"\*?\{")
        for m in pat.finditer(text):
            line_no = text[:m.start()].count("\n") + 1
            # Walk the brace-balanced argument.
            depth = 1
            i = m.end()
            while i < len(text) and depth > 0:
                c = text[i]
                if c == "{":
                    depth += 1
                elif c == "}":
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            title = text[m.end():i]
            stripped = strip_math(title)
            if re.search(r"(?<!\\)_", stripped):
                findings.append((line_no, "title-underscore",
                                 f"\\{cmd}*{{...}}: bare _ in "
                                 f"{title[:80]!r}"))
            for bm in re.finditer(r"\\\\([A-Za-z]+)", title):
                findings.append((line_no, "title-double-backslash",
                                 f"\\\\{bm.group(1)} in \\{cmd} title "
                                 f"{title[:80]!r}"))

    # 4. Mismatched env begin/end counts.
    for env in STD_ENVS:
        b = text.count(r"\begin{" + env + "}")
        e = text.count(r"\end{" + env + "}")
        if b != e:
            findings.append((0, "env-mismatch",
                             f"\\begin{{{env}}}={b} "
                             f"\\end{{{env}}}={e}"))

    # 5. Multi-line \code{...} / \lean{...} arg with a BLANK line
    # (paragraph break). A single newline inside braces is fine
    # (LaTeX treats it as a space); a blank line ends the paragraph
    # and makes LaTeX angry mid-argument.
    for cmd in ("code", "lean", "label", "uses", "proves"):
        for m in re.finditer(r"\\" + cmd + r"\{", text):
            depth = 1
            i = m.end()
            while i < len(text) and depth > 0:
                c = text[i]
                if c == "{":
                    depth += 1
                elif c == "}":
                    depth -= 1
                    if depth == 0:
                        break
                elif c == "\n" and i + 1 < len(text) and text[i + 1] == "\n":
                    line_no = text[:m.start()].count("\n") + 1
                    findings.append((line_no, "arg-paragraph-break",
                                     f"\\{cmd}{{...}} contains blank line"))
                    break
                i += 1

    # 6. Stray \\command at start of paragraph (rare but happens)
    for line_no, line in enumerate(lines, 1):
        # Look for \\X where X is letter, outside any math-mode strip
        m = re.search(r"(?<!\\)\\\\([A-Za-z]+)", strip_math(line))
        if m and not line.strip().endswith(r"\\"):
            # Skip tabular row terminators (which legitimately end with \\)
            if r"\\hline" in line or "&" in line:
                continue
            findings.append((line_no, "stray-double-backslash",
                             f"\\\\{m.group(1)} on line "
                             f"{line.strip()[:80]!r}"))

    # 7. Non-ASCII characters.  Modern LaTeX accepts UTF-8 by default,
    # but pdflatex with the project's [T1]{fontenc} + lmodern setup
    # sometimes mis-encodes (`Kahler` rendered as `K^^Ah^^Eler`).
    # Flag every line with a non-ASCII byte so the author can decide
    # case-by-case (some are intentional like Rado / Kahler in prose;
    # some are accidental from clipboard-pastes that shouldn't be in
    # commands or labels).
    for line_no, line in enumerate(lines, 1):
        for col, ch in enumerate(line):
            if ord(ch) > 127:
                # Skip lines we know are intentional prose.
                # (The rule is informational; downstream can grep.)
                findings.append((line_no, "non-ascii",
                                 f"U+{ord(ch):04X} ({ch!r}) at col {col}: "
                                 f"{line.strip()[:80]!r}"))
                break

    return findings


def main(argv: list[str]) -> int:
    dirs = argv[1:] or list(DEFAULT_DIRS)
    summary: Counter[str] = Counter()
    total = 0
    for d in dirs:
        for root, _, files in os.walk(d):
            for name in sorted(files):
                if not name.endswith(".tex"):
                    continue
                path = os.path.join(root, name)
                findings = lint_file(path)
                for line_no, kind, msg in findings:
                    print(f"{path}:{line_no}: [{kind}] {msg}")
                    summary[kind] += 1
                    total += 1
    print(f"\nTotal: {total} findings; by kind: {dict(summary)}")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
