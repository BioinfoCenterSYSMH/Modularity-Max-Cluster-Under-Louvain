"""Small weighted graphs, control settings and critical points for independent tests."""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations


@dataclass(frozen=True)
class Case:
    name: str
    n: int
    edges: tuple
    algorithm: int = 1
    fxn: int = 1
    starts: int = 3
    iters: int = 2
    seed: int = 0
    group: bool = False
    jaccard: bool = False
    complete: bool = False


def cases():
    small = ((0, 1, 2), (0, 2, 1), (1, 2, 1), (2, 3, 2), (3, 4, 3), (2, 4, 1))
    crossing = ((0,1,4),(0,3,1),(0,5,4),(0,6,1),(1,4,4),(2,3,2),(2,4,4),
                (2,5,2),(2,6,2),(3,5,1),(3,6,1))
    rounding = ((0,1,3),(0,2,1),(0,3,3),(0,4,3),(1,2,3),(1,3,2),(1,4,1),
                (1,5,4),(2,3,4),(3,4,4))
    refinement = ((0,1,4),(0,2,2),(0,4,5),(0,7,4),(0,9,3),(1,3,4),(1,4,4),
                  (2,3,3),(2,4,3),(2,6,2),(2,8,3),(2,9,2),(3,4,2),(3,5,2),
                  (3,6,1),(3,7,5),(3,8,3),(3,9,1),(5,6,3),(5,7,2),(5,9,1),
                  (6,7,2),(7,8,2))
    # Submatrix on the first seven barcodes of PBMC3k trial 001, k=20.
    # Source: MML_pbmc_coverage/results/trials/001/audit.rds, edges$overlap.
    overlaps = (15,12,11,16,11,10,13,11,12,10,12,10,12,10,17,16,17,10,12,11,12)
    pairs = [(i,j) for j in range(1,7) for i in range(j)]
    pbmc = tuple((i,j,F(h,40-h)) for (i,j), h in zip(pairs, overlaps))
    result = [Case(f"complete_a{a}_m{f}", 5, small, algorithm=a, fxn=f,
                   complete=True, group=a==2, seed=19)
              for a in (1,2) for f in (1,2)]
    result += [Case("start_switch", 7, crossing, starts=4),
               Case("rounding", 6, rounding, starts=1),
               Case("dyadic_rounding", 2, ((0,1,F(49,64)),), starts=1),
               Case("edgeless", 4, (), group=True, starts=1),
               Case("disconnected", 6, ((0,1,1),(2,3,2),(3,4,1)), group=True),
               Case("clique", 4, tuple((i,j,1) for i,j in combinations(range(4),2)),
                    group=True, complete=True),
               Case("refinement_1", 10, refinement, starts=1, iters=1),
               Case("refinement_2", 10, refinement, algorithm=2, starts=1,iters=1),
               Case("pbmc_a1", 7, pbmc, jaccard=True, starts=4, seed=23),
               Case("pbmc_a2", 7, pbmc, algorithm=2, fxn=2, jaccard=True, starts=4,
                    seed=23)]
    return result


def partitions(n):
    def extend(labels):
        if len(labels) == n:
            yield labels
            return
        for group in range(max(labels) + 2):
            yield from extend(labels + (group,))
    yield from extend((0,))


def algebraic_crossings(graph, fxn):
    """All partition-quality line crossings, used only on four/five-cell fixtures.

    A move comparing two destinations compares two partitions of the original
    vertices. The same applies after contraction and when choosing a restart.
    """
    n = len(graph.adj)
    masses = graph.degree if fxn == 1 else [1] * n
    lines = set()
    for labels in partitions(n):
        observed = sum(w for i, row in enumerate(graph.adj) for j, w in enumerate(row)
                       if labels[i] == labels[j])
        squares = sum(sum(masses[i] for i,c in enumerate(labels) if c == k)**2
                      for k in set(labels))
        lines.add((observed, squares))
    points = {F(0)}
    for (a,b),(c,d) in combinations(lines, 2):
        if b == d:
            continue
        x = F(a-c,b-d) * (graph.total if fxn == 1 else F(1,graph.scale))
        if x >= 0 and (fxn == 1 or x <= 1):
            points.add(x)
    if fxn == 2:
        points.add(F(1))
    return points
