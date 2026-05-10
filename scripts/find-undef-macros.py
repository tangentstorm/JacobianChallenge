"""Heuristic: find \\xxx tokens in tex/ that don't match a definition in
tex/macros.tex or a known-LaTeX macro.

False-positive heavy — many real LaTeX macros aren't in our small allow-list.
But useful for spotting Lean-style identifiers like \\analyticOrderAt that
got typed as bare backslash sequences instead of \\code{...} or \\texttt{...}.
"""
import re, glob, os

# Tiny LaTeX core allow-list (lowercase only matters for \w detection)
LATEX_CORE = set('''
section subsection subsubsection paragraph label ref cite input include
title author date today maketitle tableofcontents bibliographystyle bibliography
begin end documentclass usepackage RequirePackage newcommand renewcommand
providecommand newenvironment newtheorem theoremstyle setlist
def let edef gdef long outer global newif iftrue iffalse else fi
csname endcsname expandafter noexpand protect protected detokenize meaning string
textbf textit textsl textsc textrm textsf texttt textnormal textup
underline emph par noindent indent smallskip medskip bigskip newpage clearpage
linebreak nolinebreak vspace hspace newline mbox hbox vbox sbox parbox minipage
left right middle big bigg Big Bigg bigl bigr Bigl Bigr biggl biggr Biggl Biggr
frac dfrac tfrac sqrt root sum prod int oint coint iint iiint infty partial nabla
to mapsto cdot times div pm mp ast star circ bullet ldots cdots dots dotsb dotsc dotsm
le leq ge geq ne neq approx equiv sim cong simeq subset supset in notin subseteq supseteq
cap cup setminus emptyset exists forall implies iff propto
mathbb mathrm mathcal mathfrak mathbf mathit mathsf mathtt mathnormal operatorname
overline overrightarrow widehat widetilde vec dot ddot tilde hat bar acute grave check breve
qquad quad varepsilon epsilon phi varphi psi theta vartheta rho varrho sigma varsigma
tau upsilon omega xi zeta eta iota kappa lambda mu nu pi varpi chi alpha beta gamma delta
Phi Psi Theta Omega Lambda Sigma Pi Xi Gamma Delta Upsilon
item itemize enumerate description center flushleft flushright tabular table figure caption centering hline cline
mathring mathstrut strut phantom vphantom hphantom smash rlap llap clap
displaystyle textstyle scriptstyle scriptscriptstyle
href url autoref nameref pageref eqref
TeX LaTeX LaTeXe BibTeX
verb verbatim lstlisting
typeout immediate write tracingmacros wlog
binom dbinom tbinom choose
mod bmod pmod pod arg det gcd lcm
log ln lg sin cos tan sec csc cot sinh cosh tanh coth
exp sup inf min max lim limsup liminf Pr Re Im
forall exists nexists top bot vdash dashv vDash models because therefore
aleph hbar Bbbk wp varnothing imath jmath ell
overline underline underbrace overbrace underset overset
backslash mid parallel perp angle triangle
rangle langle lceil rceil lfloor rfloor llbracket rrbracket
lbrace rbrace lbrack rbrack
oplus ominus otimes odot
hookrightarrow hookleftarrow rightarrow leftarrow Rightarrow Leftarrow Leftrightarrow longrightarrow longleftarrow longmapsto
xrightarrow xleftarrow
mathbin mathrel mathop mathord mathopen mathclose mathpunct mathinner
boldsymbol pmb stackrel
hline cline rule vrule hrule vfill hfill dotfill
hangindent hangafter parindent parskip parsep itemsep
fbox framebox makebox
matrix pmatrix bmatrix vmatrix Vmatrix Bmatrix smallmatrix array eqalign cases
colorlinks linkcolor citecolor urlcolor
'''.split())

defined = set(LATEX_CORE)

with open('tex/macros.tex', encoding='utf-8') as f:
    text = f.read()
for pat in [
    r'\\newcommand\s*\{?\s*\\(\w+)\s*\}?',
    r'\\renewcommand\s*\{?\s*\\(\w+)\s*\}?',
    r'\\providecommand\s*\{?\s*\\(\w+)\s*\}?',
    r'\\def\s*\\(\w+)',
    r'\\newtheorem\{(\w+)\}',
    r'\\newenvironment\{(\w+)\}',
]:
    for m in re.finditer(pat, text):
        defined.add(m.group(1))

cands = {}
for path in (glob.glob('tex/sections/*.tex') +
             glob.glob('tex/statements/*.tex') +
             ['tex/main.tex','tex/main-with-layman.tex']):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    for m in re.finditer(r'\\([A-Za-z]{2,})', text):
        n = m.group(1)
        if n not in defined:
            cands.setdefault(n, []).append((path, m.start()))

print('Possibly undefined macros (sorted by file count):')
for n in sorted(cands, key=lambda k: -len(cands[k]))[:60]:
    files = sorted({os.path.basename(p) for p, _ in cands[n]})
    print(f'  \\{n}  ({len(cands[n])} uses, files: {files[:3]})')
