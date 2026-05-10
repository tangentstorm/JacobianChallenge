#!/usr/bin/env python3
import re
import os
import json

# 1. Parse TeX files for \label and \uses
label_uses = {}

for root, _, files in os.walk("tex"):
    for file in files:
        if file.endswith(".tex"):
            with open(os.path.join(root, file)) as f:
                content = f.read()
                envs = re.findall(r"\\begin\{[^}]+\}(.*?)\\end\{[^}]+\}", content, re.DOTALL)
                for env in envs:
                    labels = re.findall(r"\\label\{([^}]+)\}", env)
                    if not labels: continue
                    label = labels[0]
                    
                    uses_lists = re.findall(r"\\uses\{([^}]+)\}", env)
                    used_labels = []
                    for u_str in uses_lists:
                        for u in u_str.split(","):
                            u = u.strip()
                            if u: used_labels.append(u)
                    
                    if used_labels:
                        label_uses[label] = list(set(used_labels))

print(f"Found dependencies for {len(label_uses)} blueprint labels.")

# 2. Load sorries database and map labels to IDs
db_items = []
header = None
label_to_ids = {}

# Blacklist labels that create circular dependencies or conflict with code structure
BLACKLIST = {
    "thm:challenge-api",
    "def:analytic-jacobian",
    "def:abel-jacobi",
    "thm:push-pull-functoriality",
    "thm:genus-zero-classification"
}

with open("sorries.jsonl", "r") as f:
    for i, line in enumerate(f):
        if not line.strip(): continue
        obj = json.loads(line)
        if i == 0 and obj.get("i") == "ID":
            header = obj
            continue
        
        db_items.append(obj)
        b = obj.get("b")
        if b:
            if b not in label_to_ids:
                label_to_ids[b] = []
            label_to_ids[b].append(obj["i"])

# 3. Calculate 'u' (upstream/leafward) and build 'd' (downstream/rootward) inverses
# Refinement Flow: Root (Goal) -> Leaf (Axiom/Mathlib)
# Truth Flow: Leaf (Source) -> Root (Goal/Sink)
# convention: u (Upstream) is closer to the Leaves. d (Downstream) is closer to the Root.
id_to_u = {obj["i"]: set() for obj in db_items}
id_to_d = {obj["i"]: set() for obj in db_items}

for obj in db_items:
    b = obj.get("b")
    if not b or b not in label_uses or b in BLACKLIST: continue
    
    # "uses" in TeX means "depends on for proof" (Leafward)
    leafward_labels = label_uses[b]
    for leaf_label in leafward_labels:
        if leaf_label in label_to_ids and leaf_label not in BLACKLIST:
            leaf_ids = label_to_ids[leaf_label]
            for lid in leaf_ids:
                if lid != obj["i"]: # no self edges
                    # obj depends on lid, so lid is UPSTREAM of obj
                    id_to_u[obj["i"]].add(lid)
                    # lid feeds into obj, so obj is DOWNSTREAM of lid
                    id_to_d[lid].add(obj["i"])

# 4. Update objects
updates = 0
for obj in db_items:
    i = obj["i"]
    # Merge existing sets with new ones
    current_u = set(obj.get("u", []))
    current_d = set(obj.get("d", []))
    
    merged_u = sorted(list(current_u | id_to_u[i]))
    merged_d = sorted(list(current_d | id_to_d[i]))
    
    if obj.get("u") != merged_u or obj.get("d") != merged_d:
        obj["u"] = merged_u
        obj["d"] = merged_d
        updates += 1

# 5. Write back maintaining exact schema order
SCHEMA_KEYS = ["@ver", "i", "f", "k", "s", "n", "o", "r", "e", "u", "d", "a", "c", "b", "t"]

with open("sorries.jsonl", "w") as f:
    f.write(json.dumps(header, separators=(',', ':')) + "\n")
    for obj in db_items:
        row = {}
        for k in SCHEMA_KEYS:
            if k in obj: row[k] = obj[k]
        for k in obj:
            if k not in row: row[k] = obj[k]
        f.write(json.dumps(row, separators=(',', ':')) + "\n")

print(f"Updated upstream/downstream edges for {updates} tracking records.")
