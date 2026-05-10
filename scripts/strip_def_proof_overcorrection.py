#!/usr/bin/env python3
"""Strip definition-side `\\begin{proof}\\leanok\\end{proof}` overcorrections.

The proof_leanok.py script added these after definition blocks too, but
definitions don't have proofs — statement-`\\leanok` alone already
renders green-fill for definitions.
"""
import re
import sys
import pathlib

PATTERN = re.compile(
    r'(\\end\{definition\}\r?\n)\\begin\{proof\}\\leanok\\end\{proof\}\r?\n'
)

ROOT = pathlib.Path("C:/ver/JacobianChallenge/tex")

def main() -> int:
    edited = 0
    for path in list(ROOT.glob("sections/*.tex")) + list(ROOT.glob("statements/*.tex")):
        text = path.read_text(encoding="utf-8", newline="")
        new = PATTERN.sub(r"\1", text)
        if new != text:
            path.write_text(new, encoding="utf-8", newline="")
            removed = len(PATTERN.findall(text))
            print(f"{path.relative_to(ROOT.parent).as_posix()}: stripped {removed}")
            edited += removed
    print(f"total: {edited} overcorrections stripped")
    return 0

if __name__ == "__main__":
    sys.exit(main())
