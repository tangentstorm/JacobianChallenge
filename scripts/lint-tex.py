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

# Standard LaTeX / AMS / hyperref command names that the linter trusts
# without needing them defined in macros.tex.  Pragmatic subset; not
# exhaustive.  Add to it when a legitimate command is flagged here.
KNOWN_LATEX = frozenset("""
documentclass usepackage title author date maketitle tableofcontents
section subsection subsubsection paragraph subparagraph
begin end item label ref cite bibliography bibliographystyle pageref
input include includegraphics newpage clearpage noindent par
smallskip medskip bigskip vspace hspace quad qquad newline linebreak
penalty hskip vskip relax futurelet let def edef gdef xdef expandafter
noexpand protect catcode char endcsname csname meaning string
escapechar jobname today TeX LaTeX LaTeXe pdfTeX detokenize
frac sqrt sum prod int iint iiint oint colim cdot cdots ldots dots
vdots ddots infty partial nabla to mapsto rightarrow leftarrow
Rightarrow Leftarrow Leftrightarrow Longleftrightarrow longrightarrow
longmapsto iff implies forall exists in notin ni subset supset
subseteq supseteq cap cup setminus emptyset aleph
leq geq neq equiv approx sim simeq cong propto perp parallel
oplus otimes wedge vee land lor neg lnot star times div pm mp ast
bullet circ diamond triangle bigoplus bigotimes bigwedge bigvee
bigcup bigcap bigsqcup bigsum bigprod hookrightarrow leftrightarrow
mathbb mathbf mathcal mathfrak mathit mathrm mathsf mathtt mathnormal
boldsymbol bm bar overline underline widehat widetilde vec dot ddot
hat tilde check overrightarrow overleftarrow xrightarrow xleftarrow
left right middle big Big bigg Bigg bigl bigr Bigl Bigr
rangle langle lvert rvert lVert rVert lfloor rfloor lceil rceil
mathop operatorname log ln exp sin cos tan sec csc cot
arctan arcsin arccos min max sup inf lim liminf limsup det dim
gcd lcm ker coker hom Hom End Aut Iso image Image Range span Span
mod bmod pmod deg ell le ge ne tfrac dfrac smile text textbackslash
emph textit textbf textsc textsf textsf textsf textsf textnormal textmd
textup itshape bfseries rmfamily sffamily ttfamily texttt textsubscript
underline sout enquote large Large LARGE huge Huge small footnotesize
scriptsize tiny normalsize centering flushleft flushright
alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta
iota kappa varkappa lambda mu nu xi omicron pi varpi rho varrho
sigma varsigma tau upsilon phi varphi chi psi omega
Alpha Beta Gamma Delta Epsilon Zeta Eta Theta Iota Kappa Lambda
Mu Nu Xi Omicron Pi Rho Sigma Tau Upsilon Phi Chi Psi Omega
href url autoref eqref tag nonumber notag intertext
allowdisplaybreaks centering flushleft flushright
qed blacksquare square dagger ddagger copyright pounds S P natural
flat sharp prime dprime tprime complement therefore because
hline cline multicolumn multirow rowcolor arraystretch arrayrulewidth
arraybackslash tabularnewline
fbox framebox parbox makebox newbox setbox box copy wd ht dp
colorbox fcolorbox hbox vbox vcenter hfill vfill hfil vfil
expandafter noexpand protect catcode char let def newif newcommand
renewcommand providecommand DeclareMathOperator DeclareRobustCommand
newtheorem theoremstyle newcounter setcounter stepcounter addtocounter
thelemma thetheorem thesection thesubsection thefigure thetable
thefootnote numberwithin numberless phantom vphantom hphantom smash
hypersetup phantomsection addcontentsline
excludecomment includecomment
thanks address footnote tnote footnotemark footnotetext
texorpdfstring linewidth setlist newenvironment ignorespaces
""".split())

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

    # 5b. \lean{...} arguments are parsed by plastex's blueprint package
    # as a comma-separated list of declarations.  Backslash escapes
    # (\_, \&, \%, etc.) make plastex see a `TeXFragment` rather than
    # a string and crash with
    #   AttributeError: 'TeXFragment' object has no attribute 'strip'
    # The right form is the literal Lean name with raw underscores.
    for m in re.finditer(r"\\lean\{([^{}]*)\}", text):
        arg = m.group(1)
        if re.search(r"\\[_&%#$]", arg):
            line_no = text[:m.start()].count("\n") + 1
            findings.append((line_no, "lean-arg-escaped-special",
                             f"\\lean{{...}} contains a backslash-escaped "
                             f"special char; plastex needs literal forms: "
                             f"{arg[:80]!r}"))

    # 5c. Backtick-quoted Lean code containing project math macros
    # like `\R`, `\Z`, `\C`, `\mathbb{...}`.  Backticks are typeset as
    # text-mode straight characters (LaTeX renders them as opening
    # single quotes); putting math-only macros inside aborts pdflatex
    # with
    #   ! LaTeX Error: \mathbb allowed only in math mode.
    # Either wrap the snippet in \code{...} (which detokenizes) or
    # replace the macro with a Unicode literal (`ℝ`, `ℤ`, ...).
    backtick_math_pat = re.compile(
        r"`(?P<body>[^`\n]*?)`"  # backtick-delimited inline span
    )
    math_only_macro = re.compile(r"\\(?:R|Z|C|N|Q|mathbb|mathcal|mathfrak|"
                                 r"mathrm|mathsf|mathtt|mathbf|mathit)\b")
    for m in backtick_math_pat.finditer(text):
        body = m.group("body")
        if math_only_macro.search(body):
            line_no = text[:m.start()].count("\n") + 1
            findings.append((line_no, "backtick-math-macro",
                             f"backtick-quoted Lean snippet contains a "
                             f"math-only macro; use \\code{{...}} or a "
                             f"Unicode literal: `{body[:80]}`"))

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

    # 7a. Non-ASCII characters in the Latin-1 / Latin-Extended /
    # General-Punctuation range.  pdflatex with [T1]{fontenc} +
    # lmodern handles these (Rado, Kahler, em-dash, en-dash, smart
    # quotes).  Informational only.
    #
    # 7b. Math/arrow/symbol Unicode (U+2190+, U+2200+, U+2900+,
    # U+27F0+, U+2A00+, U+2100+ Letterlike, U+1D400+ Math Alphanumeric)
    # is FATAL outside \code{...} / \texttt{\detokenize{...}} context:
    # pdflatex aborts with "! LaTeX Error: Unicode character X (U+NNNN)
    # not set up for use with LaTeX."  Inside \code{...} the
    # \detokenize neutralizes the chars to bytes that the T1 font
    # silently passes through.
    def fatal_codepoint(o: int) -> bool:
        return (0x2190 <= o <= 0x21FF or  # arrows
                0x2200 <= o <= 0x22FF or  # math operators
                0x2500 <= o <= 0x257F or  # box-drawing (breaks verbatim)
                0x27F0 <= o <= 0x27FF or  # supplemental arrows-A
                0x2900 <= o <= 0x297F or  # supplemental arrows-B
                0x2A00 <= o <= 0x2AFF or  # supplemental math operators
                0x2100 <= o <= 0x214F or  # letterlike symbols
                0x1D400 <= o <= 0x1D7FF)  # math alphanumeric

    # Strip \code{...} regions so the FATAL scan ignores Lean
    # identifiers wrapped in detokenize.
    code_stripped = re.sub(r"\\code\{[^{}]*\}", "", text)
    code_stripped_lines = code_stripped.split("\n")

    for line_no, line in enumerate(lines, 1):
        # Map line position in original to stripped (best-effort,
        # by line index, since strip is line-local).
        stripped_line = (code_stripped_lines[line_no - 1]
                         if line_no - 1 < len(code_stripped_lines) else line)
        # Fatal scan
        for col, ch in enumerate(stripped_line):
            o = ord(ch)
            if o > 127 and fatal_codepoint(o):
                findings.append((line_no, "fatal-unicode",
                                 f"U+{o:04X} ({ch!r}) outside \\code{{...}}: "
                                 f"{stripped_line.strip()[:80]!r}"))
                break
        # Informational scan (any non-ASCII)
        for col, ch in enumerate(line):
            if ord(ch) > 127 and not fatal_codepoint(ord(ch)):
                findings.append((line_no, "non-ascii",
                                 f"U+{ord(ch):04X} ({ch!r}) at col {col}: "
                                 f"{line.strip()[:80]!r}"))
                break

    return findings


def collect_defined_commands() -> set[str]:
    """Read macros.tex (and blueprint macros) for commands the project
    declares.  Combined with KNOWN_LATEX this is the trusted set."""
    defined: set[str] = set(KNOWN_LATEX)
    for p in ("tex/macros.tex",
              "blueprint/src/macros/common.tex",
              "blueprint/src/macros/web.tex",
              "blueprint/src/macros/print.tex"):
        if not os.path.exists(p):
            continue
        text = open(p).read()
        for m in re.finditer(
                r"\\(?:newcommand|renewcommand|providecommand|"
                r"DeclareMathOperator|DeclareRobustCommand)\*?"
                r"\{?\\(\w+)\}?", text):
            defined.add(m.group(1))
        for m in re.finditer(r"\\newtheorem\*?\{(\w+)\}", text):
            defined.add(m.group(1))
        for m in re.finditer(r"\\newif\\if(\w+)", text):
            defined.add("if" + m.group(1))
            defined.add(m.group(1) + "true")
            defined.add(m.group(1) + "false")
    return defined


def lint_undefined_commands(paths: list[str]) -> list[tuple[str, int, str, str]]:
    """Flag uses of \\someCommand that aren't in the defined+known set."""
    defined = collect_defined_commands()
    findings: list[tuple[str, int, str, str]] = []
    for path in paths:
        text = open(path).read()
        # Strip comments
        text = re.sub(r"(?<!\\)%[^\n]*", "", text)
        for m in re.finditer(r"\\([a-zA-Z]+)", text):
            name = m.group(1)
            if name in defined:
                continue
            line_no = text[:m.start()].count("\n") + 1
            findings.append((path, line_no, "undefined-command",
                             f"\\{name} on line {line_no}"))
    return findings


def main(argv: list[str]) -> int:
    dirs = argv[1:] or list(DEFAULT_DIRS)
    summary: Counter[str] = Counter()
    total = 0
    paths: list[str] = []
    for d in dirs:
        for root, _, files in os.walk(d):
            for name in sorted(files):
                if not name.endswith(".tex"):
                    continue
                path = os.path.join(root, name)
                paths.append(path)
                findings = lint_file(path)
                for line_no, kind, msg in findings:
                    print(f"{path}:{line_no}: [{kind}] {msg}")
                    summary[kind] += 1
                    total += 1
    for path, line_no, kind, msg in lint_undefined_commands(paths):
        print(f"{path}:{line_no}: [{kind}] {msg}")
        summary[kind] += 1
        total += 1
    print(f"\nTotal: {total} findings; by kind: {dict(summary)}")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
