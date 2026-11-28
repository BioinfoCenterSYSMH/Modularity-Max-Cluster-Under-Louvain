"""Compare exported resolution intervals with an independent exact point solver."""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path

from seurat_point import fixed_point


def set_partitions(n):
    """Enumerate canonical partitions of a graph small enough for exhaustive tests."""
    partitions = [(0,)]
    for _ in range(1, n):
        partitions = [p + (label,) for p in partitions for label in range(max(p) + 2)]
    return partitions


def critical_points(n, edges, modularity, limit):
    degree = [Fraction(0)] * n
    for a, b, weight in edges:
        degree[a] += weight
        degree[b] += weight
    total = sum(degree)
    volume = degree if modularity == 1 else [Fraction(1)] * n
    penalty_scale = 1 / total if modularity == 1 else 1
    lines = set()
    for p in set_partitions(n):
        internal = 2 * sum(weight for a, b, weight in edges if p[a] == p[b])
        group_volume = [Fraction(0)] * (max(p) + 1)
        for label, weight in zip(p, volume):
            group_volume[label] += weight
        lines.add((internal, penalty_scale * sum(weight * weight for weight in group_volume)))

    critical = {Fraction(0)}
    if limit is not None:
        critical.add(limit)
    for (a, b), (c, d) in combinations(lines, 2):
        if b == d:
            continue
        root = (a - c) / (b - d)
        if root >= 0 and (limit is None or root <= limit):
            critical.add(root)
    return critical


def canonical(labels):
    seen = {}
    return tuple(seen.setdefault(label, len(seen) + 1) for label in labels)


def parse_interval(row):
    return (
        Fraction(str(row["lower"])),
        None if row["upper"] == "Inf" else Fraction(str(row["upper"])),
        row["lower_closed"],
        row["upper_closed"],
        str(row["partition"]),
    )


def hits(interval, point):
    lower, upper, lower_closed, upper_closed, _ = interval
    return (point > lower or (point == lower and lower_closed)) and (
        upper is None or point < upper or (point == upper and upper_closed)
    )


def check_case(case):
    n = case["n"]
    edges = [(a, b, Fraction(str(weight))) for a, b, weight in case["edges"]]
    controls = case["controls"]
    limit = None if case["r_max"] == "Inf" else Fraction(str(case["r_max"]))
    partition_labels = case["partitions"]
    intervals = [parse_interval(row) for row in case["intervals"]]
    critical = critical_points(n, edges, controls.get("modularity", 1), limit)
    points = critical | {i[0] for i in intervals} | {i[1] for i in intervals if i[1] is not None}
    ordered = sorted(points)
    if ordered[0] != 0 or (limit is not None and ordered[-1] != limit):
        raise ValueError(f"{case['name']}: interval bounds exceed the requested domain")
    points.update((a + b) / 2 for a, b in zip(ordered, ordered[1:]))
    if limit is None:
        points.add(ordered[-1] + 1)

    seen = set()
    for r in sorted(points):
        matches = [i[4] for i in intervals if hits(i, r)]
        if len(matches) != 1:
            raise ValueError(f"{case['name']} at r={r}: found {len(matches)} covering intervals")
        partition = matches[0]
        seen.add(partition)
        actual = canonical(partition_labels[partition])
        expected = fixed_point(n, edges, r, **controls)
        if actual != expected:
            raise ValueError(f"{case['name']} at r={r}: package {actual}, independent solver {expected}")
    if seen != set(partition_labels):
        raise ValueError(f"{case['name']}: partition table contains unreferenced results")
    return len(points)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", type=Path, help="Uncapped raw membership paths in JSON")
    args = parser.parse_args()
    cases = json.loads(args.paths.read_text(encoding="utf-8"))
    counts = {case["name"]: check_case(case) for case in cases}
    print(json.dumps({"paths": len(counts), "probes": sum(counts.values()), "by_case": counts}))


if __name__ == "__main__":
    main()
