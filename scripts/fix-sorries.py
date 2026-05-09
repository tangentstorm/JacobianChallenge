#!/usr/bin/env python3
import json
import os
import subprocess
import sys

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

def main():
    header, db, max_id = load_db()
    curr = get_current()

    # Update existing and add new
    for key, curr_obj in curr.items():
        if key in db:
            db_obj = db[key]
            db_obj["n"] = curr_obj["n"]
            db_obj["o"] = curr_obj.get("o", 0)
            db_obj["r"] = curr_obj.get("r", 0)
            db_obj["k"] = curr_obj.get("k", "unknown")
            if db_obj.get("c") == "done":
                db_obj["c"] = "open"
        else:
            max_id += 1
            new_obj = curr_obj.copy()
            new_obj["i"] = max_id
            for dk, dv in DEFAULTS.items():
                if dk not in new_obj:
                    new_obj[dk] = dv
            db[key] = new_obj

    # Mark missing ones as done
    for key, db_obj in db.items():
        if key not in curr:
            db_obj["c"] = "done"

    # Write back to DB_FILE with precise column order
    with open(DB_FILE, "w") as f:
        f.write(format_row(header, is_header=True) + "\n")
        for obj in sorted(db.values(), key=lambda x: x.get("i", 0)):
            f.write(format_row(obj) + "\n")

    print(f"Successfully fixed/updated {DB_FILE} with {len(db)} records.")

if __name__ == "__main__":
    main()
