"""Independent fixed-resolution oracle for the Seurat 5.5 Louvain flow.

Compare complete candidate partitions on the original graph with exact integer
scores. This reference never constructs a parametric path or uses its cuts.
"""

from collections import Counter
from fractions import Fraction
from math import gcd


class _JavaRandom:
    _multiplier = 0x5DEECE66D
    _mask = (1 << 48) - 1

    def __init__(self, seed):
        self._state = (seed ^ self._multiplier) & self._mask

    def _next_31(self):
        self._state = (self._state * self._multiplier + 11) & self._mask
        return self._state >> 17

    def _below(self, bound):
        if bound & (bound - 1) == 0:
            return bound * self._next_31() >> 31
        while True:
            bits = self._next_31()
            residue = bits % bound
            if bits - residue + bound - 1 < 1 << 31:
                return residue

    def order(self, size):
        order = list(range(size))
        for i in range(size):
            j = self._below(size)
            order[i], order[j] = order[j], order[i]
        return order


class _Quality:
    def __init__(self, n, edges, r, modularity):
        self.n = n
        exact = [(u, v, Fraction(w)) for u, v, w in edges if u != v and w != 0]
        if not exact or any(not (0 <= u < n and 0 <= v < n and w > 0) for u, v, w in exact):
            raise ValueError("The oracle requires positive off-diagonal graph data")
        scale = 1
        for _, _, weight in exact:
            scale *= weight.denominator // gcd(scale, weight.denominator)
        self.edges = [(u, v, w.numerator * (scale // w.denominator)) for u, v, w in exact]
        degrees = [0] * n
        for u, v, w in self.edges:
            degrees[u] += w
            degrees[v] += w
        if modularity == 1:
            self.volume = degrees
            self.edge_factor = sum(degrees) * r.denominator
            self.volume_factor = r.numerator
        else:
            self.volume = [1] * n
            self.edge_factor = r.denominator
            self.volume_factor = scale * r.numerator

    def lift(self, units, labels):
        partition = [0] * self.n
        for unit, label in zip(units, labels):
            for vertex in unit:
                partition[vertex] = label
        return partition

    def score(self, partition):
        internal = sum(w for u, v, w in self.edges if partition[u] == partition[v])
        volumes = [0] * self.n
        for vertex, cluster in enumerate(partition):
            volumes[cluster] += self.volume[vertex]
        return 2 * internal * self.edge_factor - self.volume_factor * sum(v * v for v in volumes)

    def neighbors(self, units):
        unit_map = self.lift(units, range(len(units)))
        adjacent = [set() for _ in units]
        for u, v, _ in self.edges:
            i, j = unit_map[u], unit_map[v]
            if i != j:
                adjacent[i].add(j)
                adjacent[j].add(i)
        return adjacent


def _compact(labels):
    remap = {label: i for i, label in enumerate(sorted(set(labels)))}
    return [remap[label] for label in labels]


def _local_move(quality, units, labels, rng):
    size = len(units)
    if size == 1:
        return labels, False
    counts = Counter(labels)
    unused = [i for i in range(size) if counts[i] == 0]
    adjacent = quality.neighbors(units)
    ordering = rng.order(size)
    partition = quality.lift(units, labels)
    labels = labels.copy()
    cursor = 0
    stable = 0
    changed = False
    while stable < size:
        i = ordering[cursor]
        cursor = (cursor + 1) % size
        source = labels[i]
        counts[source] -= 1
        if counts[source] == 0:
            unused.append(source)
        singleton_label = unused[-1]
        for vertex in units[i]:
            partition[vertex] = singleton_label
        score_best = quality.score(partition)
        best = singleton_label
        for target in sorted({labels[j] for j in adjacent[i]}):
            for vertex in units[i]:
                partition[vertex] = target
            score_target = quality.score(partition)
            # Sorted live labels implement tie priority. The empty label wins
            # whenever no live insertion improves upon the singleton choice.
            if score_target > score_best:
                score_best, best = score_target, target
        if best == singleton_label:
            unused.pop()
        for vertex in units[i]:
            partition[vertex] = best
        labels[i] = best
        counts[best] += 1
        if best == source:
            stable += 1
        else:
            stable = 1
            changed = True
    return _compact(labels), changed


def _louvain(quality, units, labels, rng, algorithm):
    labels, changed = _local_move(quality, units, labels, rng)
    cluster_count = max(labels) + 1
    if cluster_count < len(units):
        new_units = [[] for _ in range(cluster_count)]
        for unit, label in zip(units, labels):
            new_units[label].extend(unit)
        coarse, coarse_changed = _louvain(
            quality, new_units, list(range(cluster_count)), rng, algorithm
        )
        if coarse_changed:
            labels = [coarse[label] for label in labels]
            changed = True
            if algorithm == 2:
                labels, _ = _local_move(quality, units, labels, rng)
    return labels, changed


def _canonical(labels):
    remap = {}
    return tuple(remap.setdefault(label, len(remap) + 1) for label in labels)


def _point_runs(n, edges, r, algorithm, modularity, n_start, n_iter, seed):
    if algorithm not in (1, 2) or modularity not in (1, 2) or n_start < 1 or n_iter < 1:
        raise ValueError("Expected Louvain algorithm/modularity 1 or 2 and positive n_start/n_iter")
    r = Fraction(str(r))
    if r < 0 or (modularity == 2 and r > 1):
        raise ValueError("Resolution outside the oracle's nonnegative Seurat domain")
    quality = _Quality(n, edges, r, modularity)
    rng = _JavaRandom(seed)
    original_units = [(i,) for i in range(n)]
    for _ in range(n_start):
        labels = list(range(n))
        for _ in range(n_iter):
            labels, changed = _louvain(quality, original_units, labels, rng, algorithm)
            if not changed:
                break
        yield quality.score(labels), _canonical(labels)


def fixed_point(n, edges, r, *, algorithm=1, modularity=1, n_start=10, n_iter=10, seed=0):
    """Return the raw Seurat-rule partition as first-appearance 1-based labels."""
    runs = _point_runs(n, edges, r, algorithm, modularity, n_start, n_iter, seed)
    return max(runs, key=lambda run: run[0])[1]


def restart_partitions(n, edges, r, *, algorithm=1, modularity=1, n_start=10, n_iter=10, seed=0):
    """Return raw partitions from every start, in Seurat restart order."""
    return tuple(
        groups for _, groups in _point_runs(n, edges, r, algorithm, modularity, n_start, n_iter, seed)
    )
