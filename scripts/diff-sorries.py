#!/usr/bin/env python3
import json
import subprocess
import sys
import argparse

def load_db(filepath="sorries.jsonl"):
    db = {}
    try:
        with open(filepath, "r") as f:
            for line in f:
                if not line.strip(): continue
                obj = json.loads(line)
                if obj.get("i") == "ID": continue # skip header
                db[(obj["f"], obj["s"])] = obj
    except FileNotFoundError:
        print(f"Error: {filepath} not found.", file=sys.stderr)
        sys.exit(1)
    return db

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

def main():
    parser = argparse.ArgumentParser(description="Diff the current sorries against the tracking database.")
    parser.add_argument("--text", action="store_true", help="Output in plain text format instead of JSON.")
    args = parser.parse_args()

    db = load_db()
    curr = get_current()

    db_keys = set(db.keys())
    curr_keys = set(curr.keys())

    # Only consider it "removed" if it is missing from current codebase AND was "open" in DB
    removed_keys = {k for k in db_keys - curr_keys if db[k].get("c", "open") == "open"}
    added_keys = curr_keys - db_keys

    # Check for changes in 'n' (number of sorries), 'o' (obligations) and 'r' (reachable)
    common = db_keys & curr_keys
    changed_n_keys = []
    changed_o_keys = []
    changed_r_keys = []
    for k in common:
        if db[k]["n"] != curr[k]["n"]:
            changed_n_keys.append((k, db[k]["n"], curr[k]["n"]))

        # 'o' might not be in old db
        db_o = db[k].get("o")
        curr_o = curr[k].get("o")
        if db_o is not None and curr_o is not None and db_o != curr_o:
            changed_o_keys.append((k, db_o, curr_o))

        # db[k].get("r") handles cases where it might be null or missing
        db_r = db[k].get("r")
        curr_r = curr[k].get("r")
        if db_r is not None and curr_r is not None and db_r != curr_r:
            changed_r_keys.append((k, db_r, curr_r))

    if args.text:
        if not removed_keys and not added_keys and not changed_n_keys and not changed_o_keys and not changed_r_keys:
            print("No sorries were added, removed, or changed in count/reachability.")
            return

        if removed_keys:
            print("--- REMOVED SORRIES ---")
            for k in sorted(removed_keys):
                print(f"- [{(db[k].get('k') or 'unknown')}] {k[0]} : {k[1]} (was {db[k]['n']} sorries)")
            print()

        if added_keys:
            print("+++ ADDED SORRIES +++")
            for k in sorted(added_keys):
                l_str = f"line: {curr[k].get('l', '?')}, "
                print(f"+ [{(curr[k].get('k') or 'unknown')}] {k[0]} : {k[1]} ({l_str}{curr[k]['n']} sorries ({(curr[k].get('o') or '?')} obligations), reachable: {(curr[k].get('r') or 'unknown')})")
            print()

        if changed_n_keys:
            print("~~~ CHANGED COUNT ~~~")
            for k, old_n, new_n in sorted(changed_n_keys):
                l_str = f" (line {curr[k].get('l', '?')})"
                print(f"~ [{(curr[k].get('k') or 'unknown')}] {k[0]} : {k[1]}{l_str} ({old_n} -> {new_n})")
            print()

        if changed_o_keys:
            print("~~~ CHANGED OBLIGATIONS ~~~")
            for k, old_o, new_o in sorted(changed_o_keys):
                l_str = f" (line {curr[k].get('l', '?')})"
                print(f"~ [{(curr[k].get('k') or 'unknown')}] {k[0]} : {k[1]}{l_str} obligations: ({old_o} -> {new_o})")
            print()

        if changed_r_keys:
            print("~~~ CHANGED REACHABILITY ~~~")
            for k, old_r, new_r in sorted(changed_r_keys):
                l_str = f" (line {curr[k].get('l', '?')})"
                print(f"~ [{(curr[k].get('k') or 'unknown')}] {k[0]} : {k[1]}{l_str} (reachable: {old_r} -> {new_r})")
            print()
    else:
        # JSON Output
        out = {
            "removed": [{"f": k[0], "s": k[1], "n": db[k]["n"]} for k in sorted(removed_keys)],
            "added": [{"f": k[0], "l": curr[k].get("l"), "k": curr[k].get("k"), "s": k[1], "n": curr[k]["n"], "o": curr[k].get("o"), "r": curr[k].get("r")} for k in sorted(added_keys)],
            "changed_n": [{"f": k[0], "l": curr[k].get("l"), "k": curr[k].get("k"), "s": k[1], "old_n": o, "new_n": n} for k, o, n in sorted(changed_n_keys)],
            "changed_o": [{"f": k[0], "l": curr[k].get("l"), "k": curr[k].get("k"), "s": k[1], "old_o": o, "new_o": n} for k, o, n in sorted(changed_o_keys)],
            "changed_r": [{"f": k[0], "l": curr[k].get("l"), "k": curr[k].get("k"), "s": k[1], "old_r": o, "new_r": n} for k, o, n in sorted(changed_r_keys)]
        }
        print(json.dumps(out, indent=2))
if __name__ == "__main__":
    main()
