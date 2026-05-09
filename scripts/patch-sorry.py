#!/usr/bin/env python3
import json
import sys
import os

DB_FILE = "sorries.jsonl"

# Strict column order
SCHEMA_KEYS = ["@ver", "i", "f", "k", "s", "n", "o", "r", "e", "u", "d", "a", "c", "b", "t"]

def parse_val(k, v):
    if v.lower() == "null" or v.lower() == "none":
        return None
    if k in ["n", "o", "r", "e", "i"]:
        return int(v)
    if k in ["u", "d"]:
        # expect comma-separated list of ints
        if not v: return []
        return [int(x.strip()) for x in v.split(',')]
    return v

def main():
    if len(sys.argv) < 3:
        print("Usage: scripts/patch-sorry.py <ID> <key>=<value> ...")
        sys.exit(1)
        
    try:
        target_id = int(sys.argv[1])
    except ValueError:
        print("Error: ID must be an integer.")
        sys.exit(1)
        
    updates = {}
    for arg in sys.argv[2:]:
        if '=' not in arg:
            print(f"Error: Invalid update format '{arg}'. Expected key=value.")
            sys.exit(1)
        k, v = arg.split('=', 1)
        if k not in SCHEMA_KEYS:
            print(f"Error: Unknown key '{k}'. Valid keys: {SCHEMA_KEYS}")
            sys.exit(1)
        updates[k] = parse_val(k, v)
        
    lines = []
    found = False
    
    if not os.path.exists(DB_FILE):
        print(f"Error: Database {DB_FILE} not found.")
        sys.exit(1)
        
    with open(DB_FILE, "r") as f:
        for line in f:
            if not line.strip(): continue
            obj = json.loads(line)
            
            # Check if this is the target row
            if obj.get("i") == target_id:
                obj.update(updates)
                found = True
            
            # Reorder keys to preserve strict schema formatting
            row = {}
            for key in SCHEMA_KEYS:
                if key in obj:
                    row[key] = obj[key]
            # append any unexpected keys at the end just in case
            for key in obj:
                if key not in row:
                    row[key] = obj[key]
            
            lines.append(json.dumps(row, separators=(',', ':')))
            
    if not found:
        print(f"Error: Sorry with ID {target_id} not found.")
        sys.exit(1)
        
    with open(DB_FILE, "w") as f:
        f.write("\n".join(lines) + "\n")
        
    print(f"Successfully patched sorry {target_id}.")

if __name__ == "__main__":
    main()