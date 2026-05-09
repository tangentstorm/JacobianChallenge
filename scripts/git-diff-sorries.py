#!/usr/bin/env python3
import json
import sys

def load_db(filepath):
    db = {}
    try:
        with open(filepath, "r") as f:
            for line in f:
                if not line.strip(): continue
                obj = json.loads(line)
                if obj.get("i") == "ID": continue
                db[(obj["f"], obj["s"])] = obj
    except FileNotFoundError:
        pass
    except json.JSONDecodeError:
        pass
    return db

def main():
    if len(sys.argv) < 6:
        print("Usage: git-diff-sorries <path> <old-file> <old-hex> <old-mode> <new-file> <new-hex> <new-mode>")
        sys.exit(1)
        
    path = sys.argv[1]
    old_file = sys.argv[2]
    new_file = sys.argv[5]
    
    old_db = load_db(old_file)
    new_db = load_db(new_file)
    
    old_keys = set(old_db.keys())
    new_keys = set(new_db.keys())
    
    removed = old_keys - new_keys
    added = new_keys - old_keys
    
    common = old_keys & new_keys
    changed = []
    
    for k in common:
        old_val = old_db[k]
        new_val = new_db[k]
        diffs = []
        for field in ["n", "o", "r", "c", "e", "a", "u", "d", "b", "t", "k"]:
            if old_val.get(field) != new_val.get(field):
                diffs.append(f"{field}: {old_val.get(field)} -> {new_val.get(field)}")
        if diffs:
            changed.append((k, diffs))
            
    print(f"--- a/{path}")
    print(f"+++ b/{path}")
    
    if not removed and not added and not changed:
        print("  (No semantic changes detected)")
        return
        
    if removed:
        print("  REMOVED FROM DB:")
        for k in sorted(removed):
            print(f"  - [{old_db[k].get('k', 'unknown')}] {k[0]} : {k[1]}")
    
    if added:
        print("  ADDED TO DB:")
        for k in sorted(added):
            print(f"  + [{new_db[k].get('k', 'unknown')}] {k[0]} : {k[1]} (status: {new_db[k].get('c', 'open')})")
            
    if changed:
        print("  CHANGED:")
        for k, diffs in sorted(changed):
            print(f"  ~ [{new_db[k].get('k', 'unknown')}] {k[0]} : {k[1]}")
            for d in diffs:
                print(f"      {d}")

if __name__ == "__main__":
    main()