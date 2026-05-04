#!/usr/bin/env python3
"""Scan blueprint .tex sections and add missing proof-leanok annotations
where the Lean target's proof body is locally sorry-free.
"""
from __future__ import annotations
import os
import re
from pathlib import Path
from typing import Optional

ROOT = Path(r"C:/ver/JacobianChallenge")
TEX_DIRS = [ROOT / "tex" / "sections", ROOT / "tex" / "statements"]
LEAN_DIR = ROOT / "Jacobian"
REPORT_PATH = ROOT / "ref" / "plans" / "proof-leanok-additions.md"

# blocks we treat as "statements" that may have a following proof
STATEMENT_ENVS = ("theorem", "lemma", "definition", "corollary", "proposition")

# ---------- Lean side ----------

# Match top-level decls. We collect the body between the start of the body and
# the next top-level decl boundary. We use heuristics: scan line by line.

DECL_KW_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+|protected\s+|nonrec\s+|partial\s+)?'
    r'(theorem|lemma|def|abbrev|instance|opaque|axiom|example|structure|class|inductive|coinductive)\s+'
    r'([A-Za-z_][A-Za-z0-9_\.\']*)'
)

# Decl boundary: a line that begins (possibly after attributes/modifiers) with
# one of these keywords, OR section/namespace/end markers.
BOUNDARY_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:noncomputable\s+|private\s+|protected\s+|nonrec\s+|partial\s+|unsafe\s+|mutual\s+)*'
    r'(theorem|lemma|def|abbrev|instance|opaque|axiom|example|structure|class|inductive|coinductive|namespace|section|end)\b'
)


def find_lean_decl_body(name: str) -> Optional[tuple[str, str, int]]:
    """Return (file_path, body_text, line_no) for declaration `name` if found.
    Body is the raw text from end of header (after `:=` or `by`) up to next
    boundary line. Returns None if not found.
    """
    # name may be fully qualified like "JacobianChallenge.Blueprint.foo".
    # We need to handle that — search for the *short* name within an
    # appropriate `namespace` scope, or for the full name as written.
    parts = name.split(".")
    short = parts[-1]
    full = name

    # Walk every .lean file
    for lean in LEAN_DIR.rglob("*.lean"):
        try:
            text = lean.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        lines = text.splitlines()

        # track namespace stack
        ns_stack: list[str] = []
        i = 0
        while i < len(lines):
            line = lines[i]
            stripped = line.strip()
            # namespace open
            m_ns = re.match(r'^\s*namespace\s+([A-Za-z_][\w\.]*)', line)
            if m_ns:
                ns_stack.append(m_ns.group(1))
                i += 1
                continue
            m_end = re.match(r'^\s*end(?:\s+([A-Za-z_][\w\.]*))?\s*$', line)
            if m_end:
                if ns_stack:
                    ns_stack.pop()
                i += 1
                continue

            # decl line?
            m = DECL_KW_RE.match(line)
            if m:
                decl_name = m.group(2)
                # full qualified name in source
                if ns_stack:
                    qualified = ".".join(ns_stack) + "." + decl_name
                else:
                    qualified = decl_name
                # check if this decl matches the requested name
                # Match if exact qualified == full, or qualified ends with full,
                # or short matches and full is prefix of qualified, or
                # qualified.endswith("." + full)
                matched = False
                if qualified == full:
                    matched = True
                elif qualified.endswith("." + full):
                    matched = True
                elif decl_name == short and (
                    full == short or qualified == full
                ):
                    matched = True
                # Also allow open-namespace style: full has dotted parts that
                # are a suffix path of (ns_stack + decl_name)
                if not matched:
                    full_parts = full.split(".")
                    qual_parts = qualified.split(".")
                    if len(full_parts) <= len(qual_parts) and qual_parts[-len(full_parts):] == full_parts:
                        matched = True

                if matched:
                    # collect body: header may span multiple lines until we
                    # see `:=` or ` by ` (start of body), then body until next
                    # boundary. For `structure`/`inductive`/`class` we may
                    # have no `:=` body; in that case use the whole span.
                    decl_kw = m.group(1)
                    header_start = i
                    j = i
                    body_start_line = None
                    body_start_col = None
                    body_kind = None  # ":=" or "by" or "span"
                    while j < len(lines):
                        L = lines[j]
                        idx_assign = L.find(":=")
                        idx_by_word = -1
                        for m_by in re.finditer(r'\bby\b', L):
                            idx_by_word = m_by.start()
                            break
                        candidates = []
                        if idx_assign >= 0:
                            candidates.append((idx_assign, ":="))
                        if idx_by_word >= 0:
                            candidates.append((idx_by_word, "by"))
                        if candidates:
                            candidates.sort()
                            col, kind = candidates[0]
                            body_start_line = j
                            body_start_col = col
                            body_kind = kind
                            break
                        if j > i:
                            mb = BOUNDARY_RE.match(L)
                            if mb:
                                kw = mb.group(1)
                                if kw not in ("namespace", "section", "end"):
                                    break
                        j += 1
                    if body_start_line is None:
                        # no := or by; for structure/class/inductive/axiom we
                        # use the entire decl span (i..j-1) as the "body" for
                        # sorry-check purposes.
                        if decl_kw in ("structure", "class", "inductive", "coinductive", "axiom"):
                            body_lines = lines[i:j]
                            body_text = "\n".join(body_lines)
                            return (str(lean), body_text, header_start + 1)
                        i = j + 1
                        continue
                    # collect body text from body_start to next boundary
                    body_lines = []
                    first_line = lines[body_start_line]
                    if body_kind == ":=":
                        body_lines.append(first_line[body_start_col + 2:])
                    else:  # "by"
                        body_lines.append(first_line[body_start_col + 2:])
                    k = body_start_line + 1
                    while k < len(lines):
                        L = lines[k]
                        mb = BOUNDARY_RE.match(L)
                        if mb:
                            break
                        body_lines.append(L)
                        k += 1
                    body_text = "\n".join(body_lines)
                    return (str(lean), body_text, header_start + 1)
            i += 1
    return None


def body_is_sorry_free(body: str) -> bool:
    """Return True if `sorry` does not appear as a token in `body` (ignoring
    comments).
    """
    # Strip block comments first (handles both `/- ... -/` and `/-- ... -/`
    # since `/--` starts with `/-`). Repeat until stable to handle nesting
    # superficially.
    cleaned = body
    while True:
        new_cleaned = re.sub(r'/-.*?-/', '', cleaned, flags=re.DOTALL)
        if new_cleaned == cleaned:
            break
        cleaned = new_cleaned
    # Strip line comments. A line comment is `--` not preceded by `/` (which
    # would be a block-comment opener `/--` we should already have removed).
    cleaned_lines = []
    for line in cleaned.splitlines():
        # find `--` not preceded by `/`
        out = []
        i = 0
        n = len(line)
        while i < n:
            if line[i] == '-' and i + 1 < n and line[i + 1] == '-' and (i == 0 or line[i - 1] != '/'):
                # rest of line is comment
                break
            out.append(line[i])
            i += 1
        cleaned_lines.append("".join(out))
    cleaned = "\n".join(cleaned_lines)
    # check for `sorry` as a whole word
    return re.search(r'\bsorry\b', cleaned) is None


# ---------- Tex side ----------


def parse_tex_blocks(text: str) -> list[dict]:
    r"""Find every \begin{ENV}...\end{ENV} block of interest with its label,
    \lean{...}, statement-leanok presence, and any following proof block.
    Returns list of dicts with positions.
    """
    blocks = []
    # find all \begin{env} for relevant envs
    env_alt = "|".join(STATEMENT_ENVS)
    pat_begin = re.compile(r'\\begin\{(' + env_alt + r')\}')
    pos = 0
    while True:
        m = pat_begin.search(text, pos)
        if not m:
            break
        env = m.group(1)
        bs = m.start()
        # find matching \end{env} (assume not nested for these envs)
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
        # extract metadata
        lab = re.search(r'\\label\{([^}]*)\}', body)
        block["label"] = lab.group(1) if lab else None
        lean_m = re.search(r'\\lean\{([^}]*)\}', body)
        if lean_m:
            names = [n.strip() for n in lean_m.group(1).split(",") if n.strip()]
            block["lean_names"] = names
        else:
            block["lean_names"] = []
        block["has_stmt_leanok"] = bool(re.search(r'\\leanok\b', body))
        block["has_notready"] = bool(re.search(r'\\notready\b', body))
        # search for following proof block, possibly preceded by layman blocks
        # or whitespace/comments. Allow `\begin{layman}...\end{layman}` and
        # `\begin{proofsketch}...\end{proofsketch}` interleavings — pick the
        # next \begin{proof}...\end{proof} that appears before the next
        # statement env begin. A proof with `[Proof of Theorem~\ref{LABEL}]`
        # is attributed to LABEL only.
        nxt_stmt = pat_begin.search(text, be)
        proof_search_end = nxt_stmt.start() if nxt_stmt else len(text)
        # match \begin{proof} optionally followed by [...] argument
        proof_pat = re.compile(r'\\begin\{proof\}(\[[^\]]*\])?', re.DOTALL)
        block["proof"] = None
        pm = proof_pat.search(text, be, proof_search_end)
        if pm:
            arg = pm.group(1) or ""
            # if arg references another \ref{LABEL}, check it matches ours
            ref_match = re.search(r'\\ref\{([^}]*)\}', arg)
            if ref_match and block["label"] is not None and ref_match.group(1) != block["label"]:
                # this proof is for a different theorem — skip
                block["proof"] = None
            else:
                pend = re.search(r'\\end\{proof\}', text[pm.end():proof_search_end])
                if pend:
                    proof_abs_start = pm.start()
                    proof_begin_end = pm.end()
                    proof_end_start = pm.end() + pend.start()
                    proof_end_end = pm.end() + pend.end()
                    proof_body = text[proof_begin_end:proof_end_start]
                    block["proof"] = {
                        "begin_start": proof_abs_start,
                        "begin_end": proof_begin_end,
                        "end_start": proof_end_start,
                        "end_end": proof_end_end,
                        "body": proof_body,
                        "has_leanok": bool(re.search(r'\\leanok\b', proof_body)),
                    }
        blocks.append(block)
        pos = be
    return blocks


def main():
    total_blocks = 0
    total_lean_blocks = 0
    already_proof_leanok = 0
    skipped_sorry = []          # (file, label, name)
    skipped_no_decl = []        # (file, label, name)
    skipped_notready = 0
    skipped_no_stmt_leanok = 0
    edited = []                 # (file, label, names, action)

    # Collect edits per file: list of (insert_pos, replacement_pos, kind, text/old/new)
    # We'll just rebuild the file by sorted edit operations.

    file_ops: dict[Path, list] = {}

    for tex_dir in TEX_DIRS:
        if not tex_dir.exists():
            continue
        for tex_path in sorted(tex_dir.glob("*.tex")):
            with open(tex_path, "r", encoding="utf-8", newline="") as f:
                text = f.read()
            blocks = parse_tex_blocks(text)
            total_blocks += len(blocks)
            for b in blocks:
                if not b["lean_names"]:
                    continue
                total_lean_blocks += 1
                if b["has_notready"]:
                    skipped_notready += 1
                    continue
                if not b["has_stmt_leanok"]:
                    skipped_no_stmt_leanok += 1
                    continue
                # already proof-leanok'd?
                if b["proof"] and b["proof"]["has_leanok"]:
                    already_proof_leanok += 1
                    continue
                # check every lean name's body
                all_ok = True
                any_sorry = False
                missing_decl = False
                for name in b["lean_names"]:
                    res = find_lean_decl_body(name)
                    if res is None:
                        missing_decl = True
                        skipped_no_decl.append((str(tex_path), b["label"], name))
                        all_ok = False
                        break
                    _, body, _ = res
                    if not body_is_sorry_free(body):
                        any_sorry = True
                        skipped_sorry.append((str(tex_path), b["label"], name))
                        all_ok = False
                        break
                if not all_ok:
                    continue
                # apply edit
                if b["proof"]:
                    # add \leanok inside existing proof block
                    # insert at proof begin end
                    op = ("insert_in_proof", b["proof"]["begin_end"])
                    file_ops.setdefault(tex_path, []).append(op)
                    edited.append((str(tex_path), b["label"], b["lean_names"], "added_leanok_to_existing_proof"))
                else:
                    # insert new \begin{proof}\leanok\end{proof} after \end{env}
                    op = ("insert_proof_block", b["end_end"])
                    file_ops.setdefault(tex_path, []).append(op)
                    edited.append((str(tex_path), b["label"], b["lean_names"], "inserted_new_proof_block"))

    # Apply edits — sort by pos descending so offsets stay valid.
    # Read+write in binary-equivalent mode (newline='') to preserve original
    # line endings (LF vs CRLF) of each file.
    for path, ops in file_ops.items():
        with open(path, "r", encoding="utf-8", newline="") as f:
            text = f.read()
        # detect dominant line ending in this file
        nl = "\r\n" if "\r\n" in text else "\n"
        ops_sorted = sorted(ops, key=lambda o: o[1], reverse=True)
        for kind, pos in ops_sorted:
            if kind == "insert_in_proof":
                text = text[:pos] + "\\leanok" + text[pos:]
            elif kind == "insert_proof_block":
                insertion = nl + "\\begin{proof}\\leanok\\end{proof}"
                text = text[:pos] + insertion + text[pos:]
        with open(path, "w", encoding="utf-8", newline="") as f:
            f.write(text)

    # Write report
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    lines = []
    lines.append("# Proof-leanok additions")
    lines.append("")
    lines.append(f"- Total statement blocks scanned: {total_blocks}")
    lines.append(f"- Blocks with `\\lean{{...}}` annotation: {total_lean_blocks}")
    lines.append(f"- Blocks already proof-leanok'd (skipped): {already_proof_leanok}")
    lines.append(f"- Blocks marked `\\notready` (skipped): {skipped_notready}")
    lines.append(f"- Blocks lacking statement-`\\leanok` (skipped): {skipped_no_stmt_leanok}")
    lines.append(f"- Blocks where Lean decl body still has `sorry` (skipped): {len(skipped_sorry)}")
    lines.append(f"- Blocks where Lean decl could not be located (skipped, flagged): {len(skipped_no_decl)}")
    lines.append(f"- Blocks edited: {len(edited)}")
    lines.append("")
    if edited:
        lines.append("## Edits applied")
        lines.append("")
        for f, lbl, names, act in edited:
            rel = os.path.relpath(f, ROOT).replace("\\", "/")
            lines.append(f"- `{rel}` — label `{lbl}` — names `{names}` — {act}")
        lines.append("")
    if skipped_sorry:
        lines.append("## Skipped: Lean decl body contains `sorry`")
        lines.append("")
        for f, lbl, name in skipped_sorry:
            rel = os.path.relpath(f, ROOT).replace("\\", "/")
            lines.append(f"- `{rel}` — label `{lbl}` — name `{name}`")
        lines.append("")
    if skipped_no_decl:
        lines.append("## Flagged: Lean decl could not be located")
        lines.append("")
        for f, lbl, name in skipped_no_decl:
            rel = os.path.relpath(f, ROOT).replace("\\", "/")
            lines.append(f"- `{rel}` — label `{lbl}` — name `{name}`")
        lines.append("")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print("Report written:", REPORT_PATH)
    print(f"Edits applied: {len(edited)}")


if __name__ == "__main__":
    main()
