"""Independent point evaluator of Seurat 5.5 Louvain; no calls to MML.

The local gain is recomputed from the dense matrix and current assignments at
each visit. All comparisons are cross-multiplied integers. The output ranks
clusters by size, with old optimizer label as the tie-breaker, starting at 0.
Control flow follows Waltman and van Eck's Modularity Optimizer v1.3.0
(Seurat 5.5.0, src/ModularityOptimizer.cpp and RModularityOptimizer.cpp).
"""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from math import lcm


class JavaRandom:
    def __init__(self, seed):
        self.state = (seed ^ 0x5DEECE66D) % 2**48

    def bounded(self, n):
        while True:
            self.state = (self.state * 0x5DEECE66D + 11) % 2**48
            v = self.state >> 17
            if n & (n - 1) == 0:
                return n * v >> 31
            if v - v % n + n - 1 < 2**31:
                return v % n

    def visits(self, n):
        order = list(range(n))
        for i in range(n):
            j = self.bounded(n)
            order[i], order[j] = order[j], order[i]
        return order


@dataclass
class Start:
    labels: tuple
    internal: int
    squares: int


class Graph:
    def __init__(self, n, edges):
        edges = [(i, j, Fraction(w)) for i, j, w in edges]
        self.scale = lcm(*(w.denominator for i, j, w in edges))
        self.adj = [[0] * n for _ in range(n)]
        for i, j, w in edges:
            assert i < j and w > 0 and self.adj[i][j] == 0
            self.adj[i][j] = self.adj[j][i] = int(w * self.scale)
        self.degree = list(map(sum, self.adj))
        self.total = sum(self.degree)

    def evaluate(self, r, algorithm=1, fxn=1, starts=3, iters=3, seed=0, record=False):
        """Return winner, each restart's affine coefficients, and optional full move tape."""
        n = len(self.adj)
        if self.total == 0:
            return tuple(range(n)), [], ()
        assert fxn in (1, 2) and algorithm in (1, 2)
        r = Fraction(r)
        assert r >= 0 and (fxn == 1 or r <= 1)
        rng = JavaRandom(seed)
        trace = []
        masses = self.degree if fxn == 1 else [1] * n
        penalty = r / self.total if fxn == 1 else r * self.scale
        pn, pd = penalty.numerator, penalty.denominator

        def move(matrix, mass, labels):
            m = len(labels)
            if m == 1:
                return False
            order = rng.visits(m)
            if record:
                trace.append(('visit', tuple(order), tuple(labels)))
            empty = [i for i in range(m) if i not in labels]
            stable = index = 0
            changed = False
            while stable < m:
                u = order[index % m]
                index += 1
                previous = labels[u]
                labels[u] = -1
                if previous not in labels:
                    empty.append(previous)
                candidates = {labels[v] for v, w in enumerate(matrix[u]) if v != u and w > 0}
                best_gain, selected = 0, -1
                for g in candidates:
                    members = [v for v, a in enumerate(labels) if a == g]
                    links = sum(matrix[u][v] for v in members)
                    group_mass = sum(mass[v] for v in members)
                    gain = pd * links - pn * mass[u] * group_mass
                    if gain > best_gain or (gain == best_gain and g < selected):
                        best_gain, selected = gain, g
                if best_gain == 0:
                    selected = empty.pop()
                labels[u] = selected
                if record:
                    trace.append((u, previous, selected))
                if selected == previous:
                    stable += 1
                else:
                    stable = 1
                    changed = True
            remap = {v: i for i, v in enumerate(sorted(set(labels)))}
            labels[:] = [remap[v] for v in labels]
            return changed

        def hierarchy(matrix, mass, labels):
            changed = move(matrix, mass, labels)
            k = max(labels) + 1
            if k < len(labels):
                parts = [[i for i, v in enumerate(labels) if v == g] for g in range(k)]
                reduced = [[sum(matrix[i][j] for i in a for j in b) if a != b else 0
                            for b in parts] for a in parts]
                reduced_mass = [sum(mass[i] for i in a) for a in parts]
                coarse = list(range(k))
                if hierarchy(reduced, reduced_mass, coarse):
                    changed = True
                    labels[:] = [coarse[v] for v in labels]
                    if algorithm == 2:
                        move(matrix, mass, labels)
            return changed

        candidates = []
        for _ in range(starts):
            labels = list(range(n))
            for _ in range(iters):
                if not hierarchy(self.adj, masses, labels):
                    break
            sizes = Counter(labels)
            ranked = sorted(sizes, key=lambda g: (-sizes[g], g))
            groups = tuple(ranked.index(g) for g in labels)
            internal = sum(w for i, row in enumerate(self.adj) for j, w in enumerate(row)
                           if labels[i] == labels[j])
            squares = sum(sum(masses[v] for v, a in enumerate(labels) if a == g)**2
                          for g in sizes)
            candidates.append(Start(groups, internal, squares))
        winning = max(candidates, key=lambda x: pd * x.internal - pn * x.squares)
        return winning.labels, candidates, tuple(trace)
