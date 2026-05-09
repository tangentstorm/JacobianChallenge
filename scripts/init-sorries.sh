#!/usr/bin/env bash
set -e

DB_FILE="sorries.jsonl"

echo "Initializing $DB_FILE..."

# Write schema header
echo '{"i":"ID","f":"File","s":"Statement","n":"Num Sorries","r":"Reachable (0|1)","e":"Effort [1..10]","u":"Upstream IDs","d":"Downstream IDs","a":"Assignee","c":"Status","b":"Blueprint Ref","t":"Type"}' > "$DB_FILE"

# Run list-sorries.py and enrich the output with jq
python3 scripts/list-sorries.py | jq -c -s '
  to_entries | map(.value + {
    i: (.key + 1),
    e: null,
    u: [],
    d: [],
    a: "",
    c: "open",
    b: "",
    t: ""
  }) | map({
    i: .i,
    f: .f,
    s: .s,
    n: .n,
    r: .r,
    e: .e,
    u: .u,
    d: .d,
    a: .a,
    c: .c,
    b: .b,
    t: .t
  }) | .[]
' >> "$DB_FILE"

# Count the number of records added (excluding header)
COUNT=$(($(wc -l < "$DB_FILE") - 1))
echo "Successfully created $DB_FILE with $COUNT records."
