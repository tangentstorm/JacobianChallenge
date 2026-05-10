#!/bin/bash
# scripts/work-buckets.sh
# Categorizes open work into three types: Active, Leaves, and Planned Internal.

JSONL_FILE=${1:-sorries.jsonl}
if [ ! -f "$JSONL_FILE" ]; then
    JSONL_FILE="$(git rev-parse --show-toplevel 2>/dev/null)/sorries.jsonl"
fi

echo "--- WORK PLANNER REPORT ---"
echo "Processing: $JSONL_FILE"
echo ""

jq -s '
  (map(select(.i | type == "number")) | reduce .[] as $item ({}; .[$item.i | tostring] = $item)) as $index |
  
  # Filter for OPEN nodes with obligations
  [ .[] | select((.i | type == "number") and .c == "open" and .o > 0) ] as $open_nodes |

  # BUCKET 2: LEAVES (No upstream dependencies) - Defined first to keep others disjoint
  {
    "type": "2. LEAF NODES (Ready to Implement, u=[])",
    "items": [
      $open_nodes[] | select(.u | length == 0) |
      {id: .i, statement: .s, reachable: (.r == 1), file: .f}
    ]
  } as $bucket2 |
  ($bucket2.items | map(.id)) as $leaf_ids |

  # BUCKET 1: ACTIVE WORK (Reachable and Open, not a leaf)
  {
    "type": "1. ACTIVE INTERNAL (In Build, r=1, u!= [])",
    "items": [
      $open_nodes[] | select(.r == 1 and (.u | length > 0)) |
      {id: .i, statement: .s, file: .f}
    ]
  },

  # Output Bucket 2
  $bucket2,

  # BUCKET 3: PLANNED INTERNAL (Not yet reachable, not a leaf)
  {
    "type": "3. PLANNED INTERNAL (Blueprint Scaffolding, r=0, u!= [])",
    "items": [
      $open_nodes[] | select(.r == 0 and (.u | length > 0)) |
      {id: .i, statement: .s, deps_count: (.u | length), file: .f}
    ]
  }
' "$JSONL_FILE"
