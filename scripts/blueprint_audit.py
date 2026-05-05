#!/usr/bin/env python3
"""Audit blueprint \\leanok annotations against the actual Lean code.

Convention used by this project (per request):

  - Statement-level \\leanok inside a \\begin{theorem|lemma|definition|...}
    means: every Lean declaration named in \\lean{...} actually exists
    as a top-level decl somewhere under Jacobian/. (Sorry in the body
    is OK at this level — the statement signature is what's claimed.)

  - Proof-level \\leanok inside \\begin{proof}...\\end{proof} means: every
    Lean declaration named in \\lean{...} has a sorry-free body.

  - For a definition / instance / structure with no following proof block,
    the env itself is the proof site — i.e. env-level \\leanok = both
    "exists" and "sorry-free body".

External (Mathlib / core Lean) references are ignored (we cannot check them
without Mathlib source). They are reported under a separate header.
"""
from __future__ import annotations

import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEX_DIRS = [ROOT / "tex" / "sections", ROOT / "tex" / "statements"]
LEAN_DIR = ROOT / "Jacobian"

STATEMENT_ENVS = ("theorem", "lemma", "definition", "corollary", "proposition")
DEFINITIONAL_ENVS = ("definition",)

# A name is "project-internal" iff it matches one of these patterns.
PROJECT_PREFIXES = (
    "JacobianChallenge.",
    "Jacobian.",
)
PROJECT_EXACT = {
    "Jacobian", "genus", "genus_eq_zero_iff_homeo",
    "ContMDiff.degree",  # declared as `_root_.ContMDiff.degree` in Challenge.lean
}

# ---- Lean parser ----------------------------------------------------------

DECL_KW_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:noncomputable\s+|private\s+|protected\s+|nonrec\s+|partial\s+|unsafe\s+|mutual\s+)*'
    r'(theorem|lemma|def|abbrev|instance|opaque|axiom|example|structure|class|inductive|coinductive)\b'
    r'(?:\s+([A-Za-z_][A-Za-z0-9_\.À-￿\']*))?'
)

BOUNDARY_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:noncomputable\s+|private\s+|protected\s+|nonrec\s+|partial\s+|unsafe\s+|mutual\s+)*'
    r'(theorem|lemma|def|abbrev|instance|opaque|axiom|example|structure|class|inductive|coinductive|namespace|section|end)\b'
)

NS_RE      = re.compile(r'^\s*namespace\s+([A-Za-z_][\w.À-￿]*)')
SEC_RE     = re.compile(r'^\s*section(?:\s+([A-Za-z_][\w.À-￿]*))?\s*$')
END_RE     = re.compile(r'^\s*end(?:\s+([A-Za-z_][\w.À-￿]*))?\s*$')


def strip_block_comments(text: str) -> str:
    """Replace Lean block comments (/- ... -/, including /-! and /--) with
    blank lines of the same length so line numbers are preserved. Handles
    nesting.
    """
    out = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        if depth == 0 and i + 1 < n and text[i] == '/' and text[i + 1] == '-':
            depth = 1
            out.append('  ')
            i += 2
            continue
        if depth > 0:
            if i + 1 < n and text[i] == '/' and text[i + 1] == '-':
                depth += 1
                out.append('  ')
                i += 2
                continue
            if i + 1 < n and text[i] == '-' and text[i + 1] == '/':
                depth -= 1
                out.append('  ')
                i += 2
                continue
            ch = text[i]
            out.append('\n' if ch == '\n' else ' ')
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def index_lean_decls(lean_dir: Path):
    """Return dict: fully-qualified-name -> list of (file, line_no, body_text).

    Tracks both `namespace` and `section` opens, and pops on `end` only when
    the closing token matches the top of the open stack. Multiple decls with
    the same fully-qualified name (root-level dupes across Solution.lean and
    Challenge.lean, for example) all get recorded.
    """
    index: dict[str, list[tuple[str, int, str]]] = {}
    for lean in sorted(lean_dir.rglob("*.lean")):
        try:
            text = lean.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        text = strip_block_comments(text)
        lines = text.splitlines()
        # stack entries are ("ns", name) or ("sec", name_or_None)
        stack: list[tuple[str, str | None]] = []
        i = 0
        while i < len(lines):
            line = lines[i]
            if (m := NS_RE.match(line)):
                stack.append(("ns", m.group(1)))
                i += 1
                continue
            if (m := SEC_RE.match(line)):
                stack.append(("sec", m.group(1)))
                i += 1
                continue
            if (m := END_RE.match(line)):
                end_name = m.group(1)
                # pop matching frame; if no name, pop whatever is on top.
                if stack:
                    if end_name is None:
                        stack.pop()
                    else:
                        # Find topmost matching frame; if none matches,
                        # pop top anyway (Lean would error but we're lenient).
                        for k in range(len(stack) - 1, -1, -1):
                            if stack[k][1] == end_name:
                                del stack[k:]
                                break
                        else:
                            stack.pop()
                i += 1
                continue
            m = DECL_KW_RE.match(line)
            if m and m.group(2):
                kw = m.group(1)
                decl_name = m.group(2)
                # `_root_.Foo.bar` declares a name in the root namespace
                # regardless of the surrounding `namespace`.
                if decl_name.startswith("_root_."):
                    qualified = decl_name[len("_root_."):]
                else:
                    ns_parts = [n for kind, n in stack if kind == "ns" and n]
                    qualified = (".".join(ns_parts + [decl_name])
                                 if ns_parts else decl_name)
                # find body
                body, _ = extract_body(lines, i, kw)
                index.setdefault(qualified, []).append(
                    (str(lean.relative_to(ROOT)), i + 1, body)
                )
            i += 1
    return index


def extract_body(lines: list[str], start: int, kw: str) -> tuple[str, int]:
    """Walk forward from `start` until we find a `:=` or ` by ` opening the
    body, then collect everything up to the next decl/section/namespace/end
    line. Returns (body_text, end_line_index). For decls with no body
    (structure/class/inductive/axiom/opaque without `:=`), returns the span
    from start to next boundary.
    """
    i = start
    body_start = None
    body_kind = None
    body_col = None
    n = len(lines)
    while i < n:
        L = lines[i]
        # find earliest of `:=` or ` by ` (whole word)
        idx_assign = L.find(":=")
        idx_by = -1
        for mb in re.finditer(r'\bby\b', L):
            idx_by = mb.start()
            break
        cands = []
        if idx_assign >= 0:
            cands.append((idx_assign, ":="))
        if idx_by >= 0:
            cands.append((idx_by, "by"))
        if cands:
            cands.sort()
            body_col, body_kind = cands[0]
            body_start = i
            break
        if i > start and BOUNDARY_RE.match(L):
            kw2_m = BOUNDARY_RE.match(L)
            kw2 = kw2_m.group(1)
            if kw2 not in ("namespace", "section", "end"):
                # next decl reached without finding := or by — no body
                break
        i += 1

    if body_start is None:
        # No body found. For structure/class/inductive/axiom/opaque we still
        # treat the header span as 'body' for sorry-check purposes.
        body_lines = lines[start:i]
        return "\n".join(body_lines), i

    # Collect from body_col onward to next decl/section/namespace/end.
    out = [lines[body_start][body_col + 2:]]
    j = body_start + 1
    while j < n:
        L = lines[j]
        if BOUNDARY_RE.match(L):
            break
        out.append(L)
        j += 1
    return "\n".join(out), j


def body_is_sorry_free(body: str) -> bool:
    cleaned = body
    while True:
        new = re.sub(r'/-.*?-/', '', cleaned, flags=re.DOTALL)
        if new == cleaned:
            break
        cleaned = new
    out_lines = []
    for line in cleaned.splitlines():
        out = []
        i = 0
        n = len(line)
        while i < n:
            if line[i] == '-' and i + 1 < n and line[i + 1] == '-' and (i == 0 or line[i - 1] != '/'):
                break
            out.append(line[i])
            i += 1
        out_lines.append("".join(out))
    cleaned = "\n".join(out_lines)
    return re.search(r'\bsorry\b', cleaned) is None


def is_project_name(name: str) -> bool:
    return (name in PROJECT_EXACT) or any(name.startswith(p) for p in PROJECT_PREFIXES)


# ---- Tex parser ----------------------------------------------------------

def parse_tex_blocks(text: str) -> list[dict]:
    blocks = []
    env_alt = "|".join(STATEMENT_ENVS)
    pat_begin = re.compile(r'\\begin\{(' + env_alt + r')\}')
    pos = 0
    while True:
        m = pat_begin.search(text, pos)
        if not m:
            break
        env = m.group(1)
        bs = m.start()
        pat_end = re.compile(r'\\end\{' + re.escape(env) + r'\}')
        em = pat_end.search(text, m.end())
        if not em:
            pos = m.end()
            continue
        be = em.end()
        body = text[m.end():em.start()]
        block = {
            "env": env,
            "begin_start": bs,
            "begin_end": m.end(),
            "end_start": em.start(),
            "end_end": be,
            "body": body,
        }
        lab = re.search(r'\\label\{([^}]*)\}', body)
        block["label"] = lab.group(1) if lab else None
        lean_m = re.search(r'\\lean\{([^}]*)\}', body, re.DOTALL)
        if lean_m:
            inside = lean_m.group(1)
            inside = re.sub(r'\s+', '', inside)
            names = [n for n in inside.split(",") if n]
            block["lean_names"] = names
        else:
            block["lean_names"] = []
        block["has_stmt_leanok"] = bool(re.search(r'\\leanok\b', body))
        block["has_notready"] = bool(re.search(r'\\notready\b', body))
        # following proof block (skip layman blocks etc.)
        nxt = pat_begin.search(text, be)
        proof_end_search = nxt.start() if nxt else len(text)
        proof_pat = re.compile(r'\\begin\{proof\}(\[[^\]]*\])?', re.DOTALL)
        block["proof"] = None
        pm = proof_pat.search(text, be, proof_end_search)
        if pm:
            arg = pm.group(1) or ""
            ref_m = re.search(r'\\ref\{([^}]*)\}', arg)
            if ref_m and block["label"] is not None and ref_m.group(1) != block["label"]:
                pass
            else:
                pend = re.search(r'\\end\{proof\}', text[pm.end():proof_end_search])
                if pend:
                    pe_start = pm.end()
                    pe_end_start = pm.end() + pend.start()
                    proof_body = text[pe_start:pe_end_start]
                    block["proof"] = {
                        "body": proof_body,
                        "begin_end": pe_start,
                        "end_start": pe_end_start,
                        "has_leanok": bool(re.search(r'\\leanok\b', proof_body)),
                    }
        blocks.append(block)
        pos = be
    return blocks


# ---- Audit driver --------------------------------------------------------

def status_for(name: str, index: dict[str, list]):
    """Return ("INTERNAL", "MISSING"|"HAS_SORRY"|"SORRY_FREE", details)
    or ("EXTERNAL", None, None).
    """
    if not is_project_name(name):
        return ("EXTERNAL", None, None)
    occs = index.get(name)
    if not occs:
        return ("INTERNAL", "MISSING", None)
    # if any occurrence is sorry-free, treat as sorry-free.
    any_sorry_free = False
    for _f, _ln, body in occs:
        if body_is_sorry_free(body):
            any_sorry_free = True
            break
    return ("INTERNAL", "SORRY_FREE" if any_sorry_free else "HAS_SORRY",
            occs)


def main():
    print("Indexing Lean declarations...")
    index = index_lean_decls(LEAN_DIR)
    print(f"  Indexed {len(index)} unique fully-qualified names "
          f"({sum(len(v) for v in index.values())} total decl sites).")
    print()

    issues: dict[str, list] = {}
    counts = {
        "total_blocks": 0, "with_lean": 0, "notready": 0, "ok": 0,
        "external_only": 0,
    }
    external_refs: list[tuple[str, int, str, str]] = []

    for tex_dir in TEX_DIRS:
        if not tex_dir.exists():
            continue
        for tex_path in sorted(tex_dir.glob("*.tex")):
            text = tex_path.read_text(encoding="utf-8")
            blocks = parse_tex_blocks(text)
            for b in blocks:
                counts["total_blocks"] += 1
                if not b["lean_names"]:
                    continue
                counts["with_lean"] += 1
                if b["has_notready"]:
                    counts["notready"] += 1
                    continue
                rel = tex_path.relative_to(ROOT).as_posix()
                line_no = text.count("\n", 0, b["begin_start"]) + 1
                statuses = []
                for n in b["lean_names"]:
                    cls, st, _ = status_for(n, index)
                    statuses.append((n, cls, st))
                    if cls == "EXTERNAL":
                        external_refs.append((rel, line_no, b["label"] or "", n))

                # If every name is external, we cannot judge — track and
                # continue.
                internal = [(n, st) for n, cls, st in statuses
                            if cls == "INTERNAL"]
                if not internal:
                    counts["external_only"] += 1
                    continue

                missing = [n for n, st in internal if st == "MISSING"]
                has_sorry = [n for n, st in internal if st == "HAS_SORRY"]
                sorry_free = [n for n, st in internal if st == "SORRY_FREE"]
                all_exist = not missing
                all_sorry_free = (not missing) and (not has_sorry)

                # Diagnostics
                rec_issues = []

                if b["has_stmt_leanok"] and missing:
                    rec_issues.append(("A:env-leanok-but-decl-missing",
                                       f"missing: {', '.join(missing)}"))
                if all_exist and not b["has_stmt_leanok"]:
                    rec_issues.append(("B:decls-exist-but-no-env-leanok",
                                       f"all decls exist: {', '.join(internal_names_only(internal))}"))
                if b["proof"] is not None and b["proof"]["has_leanok"]:
                    if not all_sorry_free:
                        msg = []
                        if missing:
                            msg.append(f"missing: {', '.join(missing)}")
                        if has_sorry:
                            msg.append(f"sorry: {', '.join(has_sorry)}")
                        rec_issues.append(("C:proof-leanok-but-body-not-sorry-free",
                                           "; ".join(msg)))
                if b["proof"] is not None and not b["proof"]["has_leanok"]:
                    if all_exist and all_sorry_free:
                        rec_issues.append(("D:proof-block-sorry-free-but-no-proof-leanok",
                                           f"all sorry-free: {', '.join(internal_names_only(internal))}"))
                if b["proof"] is None and b["env"] in DEFINITIONAL_ENVS:
                    if b["has_stmt_leanok"] and all_exist and not all_sorry_free:
                        rec_issues.append(("E:def-env-leanok-but-body-has-sorry",
                                           f"sorry: {', '.join(has_sorry)}"))

                if not rec_issues:
                    counts["ok"] += 1
                else:
                    for iss, detail in rec_issues:
                        issues.setdefault(iss, []).append(
                            (rel, line_no, b["env"], b["label"], detail, statuses)
                        )

    print("Summary")
    print("-------")
    print(f"  Total statement-style env blocks: {counts['total_blocks']}")
    print(f"  With \\lean{{...}}: {counts['with_lean']}")
    print(f"  Marked \\notready (skipped): {counts['notready']}")
    print(f"  External-only (Mathlib refs, not flagged): "
          f"{counts['external_only']}")
    print(f"  Clean (no issue): {counts['ok']}")
    for k in sorted(issues):
        print(f"  {k}: {len(issues[k])}")
    print()

    for iss in sorted(issues):
        print(f"=== {iss} ===")
        for rel, line, env, label, detail, statuses in issues[iss]:
            print(f"  {rel}:{line}  [{env}] label={label!r}")
            print(f"    -> {detail}")
        print()

    # Distinct external references
    if external_refs:
        ext_names = sorted({n for _r, _l, _lbl, n in external_refs})
        print(f"=== External refs (Mathlib/core Lean), informational: "
              f"{len(ext_names)} unique ===")
        if "--show-external" in sys.argv:
            for n in ext_names:
                print(f"  {n}")

    return 1 if issues else 0


def internal_names_only(internal: list[tuple[str, str]]) -> list[str]:
    return [n for n, _ in internal]


if __name__ == "__main__":
    sys.exit(main())
