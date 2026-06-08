#!/usr/bin/env python3
import json
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import depgraph_states as dgs

DB_FILE = "sorries.jsonl"
DB_VER = 1

# Define exact column order and header labels
SCHEMA = [
    ("@ver", DB_VER),
    ("i", "ID"),
    ("f", "File"),
    ("k", "Keyword"),
    ("s", "Statement"),
    ("n", "Num Sorries"),
    ("o", "Obligations"),
    ("r", "Reachable (0|1)"),
    ("e", "Effort [1..10]"),
    ("u", "Upstream IDs"),
    ("d", "Downstream IDs"),
    ("a", "Assignee"),
    ("c", "Status"),
    ("b", "Blueprint Ref"),
    ("t", "Type")
]

DEFAULTS = {
    "e": None,
    "u": [],
    "d": [],
    "a": "",
    "c": "open",
    "b": "",
    "t": ""
}

def load_db():
    header = {k: v for k, v in SCHEMA}
    db = {}
    max_id = 0
    if os.path.exists(DB_FILE):
        with open(DB_FILE, "r") as f:
            for i, line in enumerate(f):
                if not line.strip(): continue
                obj = json.loads(line)
                if i == 0 and obj.get("i") == "ID":
                    header.update(obj)
                    header["@ver"] = header.get("@ver", 0)
                    continue
                db[(obj["f"], obj["s"])] = obj
                if isinstance(obj.get("i"), int) and obj["i"] > max_id:
                    max_id = obj["i"]
    return header, db, max_id

def get_current():
    cmd = ["python3", "scripts/list-sorries.py"]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=sys.stderr, text=True)
    curr = {}
    for line in proc.stdout:
        if line.startswith("{"):
            obj = json.loads(line)
            curr[(obj["f"], obj["s"])] = obj
    proc.wait()
    if proc.returncode != 0:
        print("Error: list-sorries.py failed.", file=sys.stderr)
        sys.exit(1)
    return curr

def format_row(obj, is_header=False):
    row = {}
    for k, default_val in SCHEMA:
        if k == "@ver" and not is_header:
            continue
        if is_header:
            if k == "@ver":
                row[k] = DB_VER # always bump to latest version
            else:
                row[k] = default_val
        else:
            if k in obj:
                row[k] = obj[k]
            elif k in DEFAULTS:
                row[k] = DEFAULTS[k]
            else:
                row[k] = None
    return json.dumps(row, separators=(',', ':'))

def blueprint_data():
    """Inspect the current blueprint tex. Returns:
      labels      — set of every \\label{} that currently exists in the tex
      nodes       — {(file, decl): "label1,label2,..."} for each blueprint node
                    that has a project \\lean{} decl. A decl cited by several
                    blueprint statements (12 of them) maps to ALL their labels,
                    comma-joined, so every citing node gets coloured (one row per
                    decl, `b` holds the label set). load_states splits on comma.
    Reuses blueprint_audit's parser so the node rule lives in one place."""
    import blueprint_audit as ba
    labels = set()
    # Aggregate labels by DECL NAME (not (file, decl)) so a decl cited from
    # several tex files still gets all its labels merged.
    decl_labels: dict[str, set] = {}
    decl_file: dict[str, str] = {}
    label_re = re.compile(r"\\label\{([^}]+)\}")
    for tex_dir in ba.TEX_DIRS:
        for tex in sorted(tex_dir.glob("*.tex")):
            text = tex.read_text(encoding="utf-8")
            labels.update(label_re.findall(text))
            for b in ba.parse_tex_blocks(text):
                label = b.get("label")
                if not label:
                    continue
                for n in b.get("lean_names", []):
                    if ba.is_project_name(n):
                        decl_labels.setdefault(n, set()).add(label)
                        decl_file.setdefault(n, str(tex.relative_to(ba.ROOT)))
    nodes = {(decl_file[n], n): ",".join(sorted(labs))
             for n, labs in decl_labels.items()}
    return labels, nodes


def main():
    header, db, max_id = load_db()
    curr = get_current()

    # 0. Collapse pre-existing duplicate rows for the same Lean decl. The old
    #    sync-blueprint-db keyed rows by (tex_file, decl) while list-sorries keys
    #    by (lean_file, decl), so a public decl can have several rows. Keep one
    #    per decl (lowest id), merging their blueprint refs and taking the
    #    max sorry count, so colouring and label attachment are unambiguous.
    by_decl: dict[str, tuple] = {}
    for key, r in list(db.items()):
        decl = r.get("s")
        if not decl:
            continue
        if decl in by_decl:
            keep_key, keep = by_decl[decl]
            # merge blueprint refs
            refs = set(filter(None, (keep.get("b", "").split(",") + r.get("b", "").split(","))))
            keep["b"] = ",".join(sorted(refs))
            keep["n"] = max(keep.get("n", 0) or 0, r.get("n", 0) or 0)
            if r.get("i", 1e9) < keep.get("i", 1e9):
                keep["i"] = r["i"]
            del db[key]
        else:
            by_decl[decl] = (key, r)

    # 1. Refresh sorry rows from list-sorries.py.
    for key, curr_obj in curr.items():
        if key in db:
            db_obj = db[key]
            db_obj["n"] = curr_obj["n"]
            db_obj["o"] = curr_obj.get("o", 0)
            db_obj["r"] = curr_obj.get("r", 0)
            db_obj["k"] = curr_obj.get("k", "unknown")
        else:
            max_id += 1
            new_obj = curr_obj.copy()
            new_obj["i"] = max_id
            for dk, dv in DEFAULTS.items():
                if dk not in new_obj:
                    new_obj[dk] = dv
            db[key] = new_obj

    bp_labels, bp_nodes = blueprint_data()

    # 2. Prune stale blueprint references. The blueprint tex is edited over
    #    time (sections deleted, labels renamed), leaving rows whose `b` points
    #    at a label that no longer exists. For each such row:
    #      * if it is a real sorry (n>0) or names a real Lean decl, keep the row
    #        but clear the dangling `b`;
    #      * otherwise it is a pure placeholder for a deleted blueprint label
    #        (no decl, no sorry) — drop the row entirely.
    # `b` may hold several comma-joined labels (a decl cited by multiple
    # blueprint statements). A row is stale only if NONE of its labels still
    # exists in the tex.
    def live_labels(b):
        return [l for l in (b or "").split(",") if l and l in bp_labels]

    cleared = dropped = 0
    for key in list(db.keys()):
        r = db[key]
        b = r.get("b")
        if b and not live_labels(b):
            if r.get("n", 0) or (key in curr):
                r["b"] = ""
                cleared += 1
            else:
                del db[key]
                dropped += 1

    # 3. Ensure every current blueprint \lean{} node has a row, keyed by the
    #    Lean decl (so it coincides with the decl's sorry row when there is one).
    #    `b` is set to the comma-joined label set so a decl backing several
    #    blueprint statements colours all of them.
    decl_to_key = {decl: k for k in db for (_f, decl) in [k]}
    for (f, decl), labelset in bp_nodes.items():
        key = decl_to_key.get(decl, (f, decl))
        if key in db:
            db[key]["b"] = labelset
        else:
            max_id += 1
            obj = dict(DEFAULTS)
            obj.update({"i": max_id, "f": f, "k": "blueprint", "s": decl,
                        "n": 0, "o": 0, "r": 0, "b": labelset})
            db[key] = obj
            decl_to_key[decl] = key

    # 4. Colour every row by the REAL Lean dependency state (DepGraph walk),
    #    written into the `c` / Status field:
    #      done | sorry | sorry-dep | unformalized
    #    `done` keeps its existing meaning (proven) for the other scripts that
    #    test `c == "done"`; the three non-done values all satisfy `!= "done"`.
    try:
        recs = dgs.run_depgraph(os.environ.get("DEPGRAPH_FILE"))
        states = dgs.decl_states(recs)
        # DepGraph keys are fully-qualified (JacobianChallenge.…); list-sorries
        # sometimes reports a short/unqualified `s`. Build a suffix index so we
        # can still resolve those.
        suffix = {}
        for n, st in states.items():
            suffix.setdefault(n.split(".")[-1], n)
        for db_obj in db.values():
            s = db_obj.get("s", "")
            if s in states:
                st = states[s]
            elif s.split(".")[-1] in suffix:
                st = states[suffix[s.split(".")[-1]]]
            else:
                st = "unformalized"
            # A row that itself carries a sorry is at least `sorry`, regardless
            # of whether DepGraph (Solution's closure) could resolve its name.
            if db_obj.get("n", 0) and st in ("done", "unformalized"):
                st = "sorry"
            db_obj["c"] = st
        coloured = True
    except Exception as exc:
        print(f"warning: skipping graph colouring ({exc})", file=sys.stderr)
        # Fall back to the old binary so the DB is still consistent.
        for key, db_obj in db.items():
            db_obj["c"] = "done" if key not in curr else "open"
        coloured = False

    # Write back to DB_FILE with precise column order
    with open(DB_FILE, "w") as f:
        f.write(format_row(header, is_header=True) + "\n")
        for obj in sorted(db.values(), key=lambda x: x.get("i") or 0):
            f.write(format_row(obj) + "\n")

    print(f"Successfully fixed/updated {DB_FILE} with {len(db)} records"
          + (" (graph-coloured)" if coloured else " (colouring skipped)")
          + f"; pruned {dropped} stale rows, cleared {cleared} dangling blueprint refs.")

if __name__ == "__main__":
    main()
