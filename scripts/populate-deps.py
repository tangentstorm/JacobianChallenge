#!/usr/bin/env python3
import re
import os
import json

# 1. Parse TeX files for \label, \uses, and \lean
label_uses = {}
lean_to_label = {}
all_labels = set()

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
                    all_labels.add(label)
                    
                    # Capture \lean mapping
                    leans = re.findall(r"\\lean\{([^}]+)\}", env)
                    for l_str in leans:
                        for l_name in l_str.split(","):
                            l_name = l_name.strip()
                            if l_name:
                                # Map full name and suffixes
                                lean_to_label[l_name] = label
                                parts = l_name.split(".")
                                for j in range(1, len(parts) + 1):
                                    suffix = ".".join(parts[-j:])
                                    lean_to_label[suffix] = label

                    uses_lists = re.findall(r"\\uses\{([^}]+)\}", env)
                    used_labels = []
                    for u_str in uses_lists:
                        for u in u_str.split(","):
                            u = u.strip()
                            if u: used_labels.append(u)
                    if used_labels:
                        label_uses[label] = list(set(used_labels))

# 2. Load sorries database
db_items = []
header = None
with open("sorries.jsonl", "r") as f:
    for i, line in enumerate(f):
        if not line.strip(): continue
        obj = json.loads(line)
        if i == 0 and obj.get("i") == "ID":
            header = obj
            continue
        # Auto-update label mapping
        if obj["s"] in lean_to_label:
            obj["b"] = lean_to_label[obj["s"]]
        db_items.append(obj)

label_to_ids = {}
for obj in db_items:
    if obj.get("b"):
        if obj["b"] not in label_to_ids: label_to_ids[obj["b"]] = []
        label_to_ids[obj["b"]].append(obj["i"])

# 3. Calculate dependencies
# REFINEMENT FLOW: Root (Goal) -> Leaf (Mathlib)
# u = parent (closer to Goal), d = child (closer to Leaf)
id_to_u = {obj["i"]: set() for obj in db_items}
id_to_d = {obj["i"]: set() for obj in db_items}

for obj in db_items:
    b = obj.get("b")
    if not b or b not in label_uses: continue
    
    # TeX "\uses{X}" means "this node refines into X"
    # So X is DOWNSTREAM (d) of this node.
    for leaf_label in label_uses[b]:
        if leaf_label in label_to_ids:
            for lid in label_to_ids[leaf_label]:
                if lid != obj["i"]:
                    id_to_d[obj["i"]].add(lid)
                    id_to_u[lid].add(obj["i"])

# 4. Write back maintaining order
SCHEMA_KEYS = ["@ver", "i", "f", "k", "s", "n", "o", "r", "e", "u", "d", "a", "c", "b", "t"]
with open("sorries.jsonl", "w") as f:
    f.write(json.dumps(header, separators=(',', ':')) + "\n")
    for obj in db_items:
        i = obj["i"]
        obj["u"] = sorted(list(id_to_u[i]))
        obj["d"] = sorted(list(id_to_d[i]))
        row = {k: obj.get(k) for k in SCHEMA_KEYS}
        f.write(json.dumps(row, separators=(",", ":")) + "\n")

print(f"Graph fully synchronized: u=Goalward (Roots), d=Leafward (Frontier).")
