#!/usr/bin/env python3
"""Audit the sorries dependency graph.

The graph in ``sorries.jsonl`` is intended to be a DAG.  Each row has:

* ``u``: upstream dependencies used by this node
* ``d``: downstream dependents of this node

This script treats ``u`` as the primary edge set and checks that:

* dependency IDs exist
* no node lists itself in ``u`` or ``d``
* the upstream dependency graph contains no directed cycle
* ``u`` and ``d`` agree as inverse adjacency lists
* the ``d`` adjacency contains no directed cycle
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Iterable
from pathlib import Path


def load_sorries(path: Path) -> tuple[dict[int, dict], list[tuple[str, dict | None]]]:
    nodes: dict[int, dict] = {}
    lines: list[tuple[str, dict | None]] = []
    with path.open(encoding="utf-8") as f:
        for line_no, line in enumerate(f, 1):
            raw_line = line.rstrip("\n")
            stripped = raw_line.strip()
            if not stripped:
                lines.append((raw_line, None))
                continue
            try:
                row = json.loads(stripped)
            except json.JSONDecodeError as ex:
                raise SystemExit(f"{path}:{line_no}: invalid JSON: {ex}") from ex
            lines.append((raw_line, row))

            row_id = row.get("i")
            if row_id == "ID":
                continue
            if not isinstance(row_id, int):
                raise SystemExit(f"{path}:{line_no}: row has non-integer id {row_id!r}")
            if row_id in nodes:
                raise SystemExit(f"{path}:{line_no}: duplicate id {row_id}")
            nodes[row_id] = row
    return nodes, lines


def id_list(row: dict, field: str) -> list[int]:
    values = row.get(field, [])
    if values is None:
        return []
    if not isinstance(values, list):
        raise ValueError(f"id {row.get('i')}: field {field!r} is not a list")
    result: list[int] = []
    for value in values:
        if not isinstance(value, int):
            raise ValueError(f"id {row.get('i')}: field {field!r} has non-integer value {value!r}")
        result.append(value)
    return result


def fmt_node(nodes: dict[int, dict], node_id: int) -> str:
    row = nodes.get(node_id)
    if row is None:
        return str(node_id)
    statement = row.get("s") or "?"
    return f"{node_id} ({statement})"


def canonical_cycle(cycle: list[int]) -> tuple[int, ...]:
    """Return a rotation-invariant key for a cycle ending with its start."""
    body = cycle[:-1]
    rotations = [tuple(body[i:] + body[:i]) for i in range(len(body))]
    best = min(rotations)
    return best + (best[0],)


def find_cycles(edges: dict[int, list[int]]) -> list[list[int]]:
    color = {node: 0 for node in edges}
    stack: list[int] = []
    stack_index: dict[int, int] = {}
    seen: set[tuple[int, ...]] = set()
    cycles: list[list[int]] = []

    sys.setrecursionlimit(max(1000, len(edges) * 2 + 100))

    def visit(node: int) -> None:
        color[node] = 1
        stack_index[node] = len(stack)
        stack.append(node)

        for dep in edges.get(node, []):
            if dep not in edges:
                continue
            dep_color = color.get(dep, 0)
            if dep_color == 0:
                visit(dep)
            elif dep_color == 1:
                cycle = stack[stack_index[dep] :] + [dep]
                key = canonical_cycle(cycle)
                if key not in seen:
                    seen.add(key)
                    cycles.append(list(key))

        stack.pop()
        stack_index.pop(node, None)
        color[node] = 2

    for node in sorted(edges):
        if color[node] == 0:
            visit(node)
    return cycles


def print_list(title: str, values: Iterable[str]) -> int:
    values = list(values)
    if not values:
        return 0
    print(title)
    for value in values:
        print(f"  {value}")
    return len(values)


def derived_downstream(nodes: dict[int, dict], upstream: dict[int, list[int]]) -> dict[int, list[int]]:
    downstream = {node_id: [] for node_id in nodes}
    for node_id in sorted(nodes):
        for up_id in upstream.get(node_id, []):
            if up_id in downstream:
                downstream[up_id].append(node_id)
    return {node_id: sorted(values) for node_id, values in downstream.items()}


def write_with_downstream(
    path: Path,
    lines: list[tuple[str, dict | None]],
    derived: dict[int, list[int]],
) -> int:
    changed = 0
    output: list[str] = []
    for raw_line, row in lines:
        if row is None or row.get("i") == "ID":
            output.append(raw_line)
            continue
        node_id = row["i"]
        new_d = derived[node_id]
        if row.get("d", []) != new_d:
            row["d"] = new_d
            changed += 1
            output.append(json.dumps(row, ensure_ascii=True, separators=(",", ":")))
        else:
            output.append(raw_line)
    path.write_text("\n".join(output) + "\n", encoding="utf-8")
    return changed


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit sorries.jsonl dependency graph.")
    parser.add_argument("path", nargs="?", default="sorries.jsonl", type=Path)
    parser.add_argument(
        "--max-cycles",
        type=int,
        default=20,
        help="maximum cycles to print per adjacency direction",
    )
    parser.add_argument(
        "--no-strict-inverse",
        action="store_true",
        help="do not require u and d to be exact inverse adjacency lists",
    )
    parser.add_argument(
        "--no-check-downstream-cycles",
        action="store_true",
        help="do not search for cycles following d edges",
    )
    parser.add_argument(
        "--fix-derived-downstream",
        action="store_true",
        help="rewrite d lists as the exact inverse of u lists before auditing",
    )
    args = parser.parse_args()

    nodes, lines = load_sorries(args.path)

    upstream: dict[int, list[int]] = {}
    downstream: dict[int, list[int]] = {}
    errors: list[str] = []

    for node_id, row in sorted(nodes.items()):
        try:
            upstream[node_id] = id_list(row, "u")
            downstream[node_id] = id_list(row, "d")
        except ValueError as ex:
            errors.append(str(ex))
            upstream[node_id] = []
            downstream[node_id] = []

    if args.fix_derived_downstream:
        downstream = derived_downstream(nodes, upstream)
        changed = write_with_downstream(args.path, lines, downstream)
        print(f"Rewrote downstream lists for {changed} node(s).")

    for node_id in sorted(nodes):
        for field, edges in (("u", upstream), ("d", downstream)):
            values = edges[node_id]
            missing = sorted({value for value in values if value not in nodes})
            if missing:
                errors.append(f"{fmt_node(nodes, node_id)} has unknown {field} IDs: {missing}")
            if node_id in values:
                errors.append(f"{fmt_node(nodes, node_id)} lists itself in {field}")
            duplicates = sorted({value for value in values if values.count(value) > 1})
            if duplicates:
                errors.append(f"{fmt_node(nodes, node_id)} has duplicate {field} IDs: {duplicates}")

    if not args.no_strict_inverse:
        for node_id, ups in sorted(upstream.items()):
            for up_id in ups:
                if up_id in nodes and node_id not in downstream.get(up_id, []):
                    errors.append(
                        f"{fmt_node(nodes, node_id)} lists upstream {fmt_node(nodes, up_id)}, "
                        "but the upstream node does not list it downstream"
                    )

        for node_id, downs in sorted(downstream.items()):
            for down_id in downs:
                if down_id in nodes and node_id not in upstream.get(down_id, []):
                    errors.append(
                        f"{fmt_node(nodes, node_id)} lists downstream {fmt_node(nodes, down_id)}, "
                        "but the downstream node does not list it upstream"
                    )

    check_downstream_cycles = not args.no_check_downstream_cycles
    upstream_cycles = find_cycles(upstream)
    downstream_cycles = find_cycles(downstream) if check_downstream_cycles else []

    print(f"Nodes: {len(nodes)}")
    print(f"Upstream edges: {sum(len(v) for v in upstream.values())}")
    print(f"Downstream edges: {sum(len(v) for v in downstream.values())}")

    issue_count = 0
    issue_count += print_list("Structural issues:", errors)

    if upstream_cycles:
        print(f"Upstream cycles: {len(upstream_cycles)}")
        for cycle in upstream_cycles[: args.max_cycles]:
            print("  " + " -> ".join(fmt_node(nodes, node_id) for node_id in cycle))
        issue_count += len(upstream_cycles)
    else:
        print("Upstream cycles: 0")

    if check_downstream_cycles and downstream_cycles:
        print(f"Downstream cycles: {len(downstream_cycles)}")
        for cycle in downstream_cycles[: args.max_cycles]:
            print("  " + " -> ".join(fmt_node(nodes, node_id) for node_id in cycle))
        issue_count += len(downstream_cycles)
    elif check_downstream_cycles:
        print("Downstream cycles: 0")

    if issue_count:
        print(f"Audit failed: {issue_count} issue(s).", file=sys.stderr)
        return 1

    print("Audit passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
