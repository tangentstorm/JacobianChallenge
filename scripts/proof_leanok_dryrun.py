#!/usr/bin/env python3
"""Dry-run mode of proof_leanok.py — shows what WOULD be edited and why,
without modifying any files."""
import sys
sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent))
import proof_leanok as M
from pathlib import Path
import re, os

ROOT = M.ROOT
TEX_DIRS = M.TEX_DIRS

def main():
    edits = []
    skips_sorry = []
    skips_nodecl = []
    skips_already = []
    skips_no_stmt_leanok = []
    notready = []
    total = 0
    lean_total = 0

    for tex_dir in TEX_DIRS:
        if not tex_dir.exists():
            continue
        for tex_path in sorted(tex_dir.glob("*.tex")):
            with open(tex_path, "r", encoding="utf-8", newline="") as f:
                text = f.read()
            blocks = M.parse_tex_blocks(text)
            total += len(blocks)
            for b in blocks:
                if not b["lean_names"]:
                    continue
                lean_total += 1
                if b["has_notready"]:
                    notready.append((tex_path.name, b["label"]))
                    continue
                if not b["has_stmt_leanok"]:
                    skips_no_stmt_leanok.append((tex_path.name, b["label"], b["lean_names"]))
                    continue
                if b["proof"] and b["proof"]["has_leanok"]:
                    skips_already.append((tex_path.name, b["label"]))
                    continue
                # examine each lean name
                outcomes = []
                for name in b["lean_names"]:
                    res = M.find_lean_decl_body(name)
                    if res is None:
                        outcomes.append((name, "NO_DECL"))
                    else:
                        _, body, _ = res
                        if M.body_is_sorry_free(body):
                            outcomes.append((name, "OK"))
                        else:
                            outcomes.append((name, "HAS_SORRY"))
                if any(o[1] == "NO_DECL" for o in outcomes):
                    skips_nodecl.append((tex_path.name, b["label"], outcomes))
                elif any(o[1] == "HAS_SORRY" for o in outcomes):
                    skips_sorry.append((tex_path.name, b["label"], outcomes))
                else:
                    has_proof = b["proof"] is not None
                    edits.append((tex_path.name, b["label"], b["lean_names"], "in_existing_proof" if has_proof else "new_proof_block"))

    print(f"Total blocks: {total}, with \\lean: {lean_total}")
    print(f"Already proof-leanok'd: {len(skips_already)}")
    print(f"\\notready: {len(notready)}")
    print(f"No statement-\\leanok: {len(skips_no_stmt_leanok)}")
    print(f"Skipped (no decl): {len(skips_nodecl)}")
    print(f"Skipped (has sorry): {len(skips_sorry)}")
    print(f"Edits: {len(edits)}")
    print()
    print("--- Edits ---")
    for e in edits:
        print(" ", e)
    print()
    print("--- Skipped (sorry) ---")
    for s in skips_sorry:
        print(" ", s)
    print()
    print("--- Skipped (no decl) ---")
    for s in skips_nodecl:
        print(" ", s)

if __name__ == "__main__":
    main()
