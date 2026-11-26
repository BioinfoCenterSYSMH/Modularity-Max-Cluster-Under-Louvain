# MML — Maximum Modularity in Louvain

**English** · **[简体中文](README.zh-CN.md)**

**MML enumerates the partitions. Researchers choose how to evaluate them.** On a Jaccard shared nearest-neighbor (SNN) graph with fixed neighbor count $k$, fix the Louvain visit order, move, contraction and tie rules, and vary only the resolution $r$. MML lists in polynomial time every distinct final partition reachable at any real $r\geq 0$, including those reached at a single critical value.

Define a score for your research question and apply it to every eligible partition. You can compare assignments by several criteria or select the best for a particular criterion using the same output. Classical Newman–Girvan modularity $Q$ is one optional metric. Its scores are included in the R package.

[Download MML v0.3.0](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/tag/v0.3.0) · [Mathematical proof](docs/MATHEMATICAL_PROOF.md) · [Lean proofs](lean/)

## MML covers every reachable partition

At any step of Louvain, each candidate move has a gain that is affine in $r$. MML traces the decisions from $r=0$ to the next value where a challenger can overtake the chosen move. It checks the crossing itself and the decisions immediately to its right, following the same logic through community contractions. Once no further crossing can change a decision, the current trajectory covers the rest of the half-line. This use of score crossings was inspired by work on single-parameter greedy algorithms. [Gupta & Roughgarden, 2017, §§3.3.3–3.3.4](https://doi.org/10.1137/15M1050276)

### Lean proves completeness and a polynomial operation bound

Let $S$ be an $n$-cell Jaccard SNN graph constructed from equal-sized neighbor sets of size $k>0$ and a symmetric pruning mask. Let $E(S)$ be the finite set enumerated by MML. Write $L_S(r)$ for the canonical final partition returned by the specified deterministic Louvain procedure at resolution $r$, starting from singleton cells.

1. **Exact coverage and uniqueness.** For every partition $P$,

   $$P\in E(S) \quad\Longleftrightarrow\quad \exists\,r\in[0,\infty)\; L_S(r)=P.$$

   For every real $r$, the run terminates with exactly one canonical final partition. The equivalence covers partitions attained on intervals and those attained only at a single endpoint. [`louvain_enumeration_exact`](lean/RawJaccard.lean#L153) · [`raw_total_unique`](lean/RawJaccard.lean#L159)

2. **Polynomial operation bound.** For every fixed positive integer $k$ there exists a constant $C(k)$ such that, for every $n>0$ and every such $S$, the dense reference algorithm uses at most $C(k)n^{14}$ unit-cost exact arithmetic and random-access operations. This covers constructing the input graph, enumerating and deduplicating the reachable partitions, computing the built-in classical modularity scores and collecting all maximizers. ROGUE, SCCAF and Silhouette are calculated separately on the returned partitions. Each adds the cost of its own scoring procedure. [`arithmetic_n14`](lean/ArithmeticBound.lean#L99) · [Cost model and build instructions](lean/README.md)

3. **Exact classical modularity scores and all maximizers.** For positive total edge weight, let $Q_S(P)$ be classical modularity on the original graph. The scored output contains each $P\in E(S)$ once with score $Q_S(P)$. The set of winning partitions is exactly

   $$\{P\in E(S)\mid \forall P'\in E(S),\;Q_S(P')\le Q_S(P)\}.$$

   This guarantees that all ties are returned when the researcher chooses this metric. [`scores_raw_exact`](lean/ScoredPath.lean#L37) · [`distinct_scores`](lean/ScoredPath.lean#L42) · [`best_exact`](lean/JaccardProgram.lean#L102)

## Bounded average SNN degree gives a sparse operation bound of $O_k(n^7)$

Single-cell workflows can store the pruned SNN as a sparse graph and scan its nonzero edges directly. Let $m$ count undirected edges between distinct cells. If $m\le c n$ for a constant $c$ independent of cell count, the average SNN degree is bounded. For fixed $k$, $c$ and a fixed number of initial search intervals, the sparse algorithm then enumerates all reachable partitions in $O(n^7)$ unit-cost arithmetic operations. The HESC graph has 14,224 edges across 498 cells, an average degree of 57.1.

<details>
<summary>Derivation of the sparse bound</summary>

1. **Count the possible boundaries.** With fixed $k$, clearing the Jaccard denominators gives an integer weight per edge bounded by a constant depending only on $k$. Thus the sum of the scaled weighted degrees is $T=O_k(m)$. For $T>0$, a scaled partition score is $Ta-rb$, where $a$ and $b$ are integers with $0\le a\le T$ and $0\le b\le T^2$. Every isolated crossing has the form $T\Delta a/\Delta b$, so there are $O(T^3)$ candidate boundaries. Checking each point and its right-hand limit gives $O(T^3)$ trajectories. [Crossing count](lean/BreakpointCount.lean)
2. **Count the work per trajectory.** Each accepted move advances among $O(T^3)$ coefficient pairs, with slope breaking equal-score ties in a right-limit trace. Contraction preserves the score, and each of at most $n$ levels adds at most one sweep with unchanged assignments. Therefore a trajectory uses $O(T^3+n)$ sweeps. Visiting only stored edges and the neighboring candidate communities costs $O(n+m)$ per sweep. With $m=O(n)$ this gives $O_k(n^3)\times O_k(n^3)\times O(n)=O_k(n^7)$ for all sweeps. [Move loop](SUNLouvainPath/src/path.cpp#L60)
3. **Include contraction and output.** For $B=O(T^3)$ outputs before deduplication, even pairwise comparisons of $n$-cell membership vectors cost at most $O(nB^2)=O_k(n^7)$. Scoring the distinct outputs by classical modularity adds $O(B(n+m))$. In the C++ implementation, sweeps iterate over an adjacency map and accumulate candidate weights in indexed arrays. Ordered-map insertions during a contraction can cost $O(m\log n+n)$ per level. Over at most $n$ levels per trajectory this contributes at most $O_k(n^5\log n)$ in the sparse case. The ordered map for partition keys needs at most $O(nB\log(B+1))$ comparisons of cell labels. Both terms fit within the stated operation bound. [Contraction](SUNLouvainPath/src/path.cpp#L125) · [Partition indexing](SUNLouvainPath/src/path.cpp#L312)

</details>

## The choice of metric determines which HESC partition scores highest

MML found **975 distinct partitions** across 992 resolution intervals for 498 cells from human embryonic stem cell differentiation ($k=20$). Each row selects the highest-scoring partition among the candidates eligible for that metric. [HESC data, GEO GSE85066](https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE85066)

| Evaluation criterion | Maximizing partition | Clusters | Score | Scored out of 975 | Example resolution $r$ |
| --- | --- | ---: | ---: | ---: | ---: |
| ROGUE | P12 | 9 | 0.999789 | 60 | 4 |
| SCCAF self-projection accuracy | P1 | 3 | 1.000000 | 73 | 0 |
| Mean Silhouette width | P6 | 8 | 0.521489 | 974 | 1 |
| Adjusted Rand index (ARI) | P8 | 9 | 0.973899 | 975 | 2.9 |
| Classical modularity | P6 | 8 | 0.863349 | 975 | 1 |

ROGUE measures within-cluster expression homogeneity using gene read-count estimates from recount3. SCCAF measures how well gene expression predicts held-out cluster labels. Silhouette measures separation in the ten principal components used to build the graph. ARI measures agreement with the nine reference classes. [Scoring rules and reproducible code](docs/hesc/methods.md)

[Download scores for all 975 partitions (CSV)](docs/hesc/partition-scores.csv) · [Cluster assignments for the winning partitions](docs/hesc/winning-memberships.csv)

## MML is distributed as an R package

MML is distributed as the R package `SUNLouvainPath`. Run the installation block for your platform.

**64-bit x86 Windows, R 4.6.x.** Install the precompiled binary in R.

```r
install.packages(c("Matrix", "parallelly", "Rcpp", "SeuratObject"))
release_url <- "https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.0"
install.packages(paste0(release_url, "/SUNLouvainPath_0.3.0.zip"),
                 repos = NULL, type = "win.binary")
```

**Linux, macOS, or a source build on Windows.** The source package requires R ≥ 4.2 and a C++17 toolchain.

```r
install.packages(c("Matrix", "parallelly", "Rcpp", "SeuratObject", "BH"))
release_url <- "https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.0"
install.packages(paste0(release_url, "/SUNLouvainPath_0.3.0.tar.gz"),
                 repos = NULL, type = "source")
```

## The HESC example reproduces the partitions for custom scoring

The bundled example reruns the enumeration and checks cell assignments, exact interval endpoints, modularity scores and the recommendation against the reference results. Each row of `mml$partitions` represents a cell. Each column beginning with `P` gives the cluster labels for one partition.

```r
library(SUNLouvainPath)
hesc <- VerifyLouvainExample("hesc")
mml <- SeuratObject::Tool(hesc, slot = "SUNLouvainPath")
mml$partitions[1:5, c("cell", "P6", "P8")]
```

To run the ARI example, install `mclust` once with `install.packages("mclust")`. The function below compares every candidate with the HESC reference annotation. Replace `score_partition()` to use your own criterion. The last line retrieves the built-in classical modularity result for comparison.

```r
partitions <- mml$partitions
reference <- hesc$reference_annotation[match(partitions$cell, colnames(hesc))]
score_partition <- function(groups) mclust::adjustedRandIndex(groups, reference)

candidates <- partitions[setdiff(names(partitions), "cell")]
scores <- vapply(candidates, score_partition, numeric(1))
scores[scores == max(scores)]
#        P8
# 0.9738988

mml$scores[mml$scores$is_max, c("partition", "n_clusters", "modularity")]
# P6    8    0.8633487
```

For your own SNN graph, use `EnumerateLouvain()`. Its default range is $[0,\infty)$. Set `workers = 1L` for sequential execution or use `workers` and `split_points` to distribute intervals across threads. With a finite `r_max`, the candidates cover the selected range. [R package and parallel options](SUNLouvainPath/)

## Authors

- **Junbo Wang (王俊博)** · [1124315977@qq.com](mailto:1124315977@qq.com)
- **Jianyou Liao (廖建友)** · [liaojy3@mail.sysu.edu.cn](mailto:liaojy3@mail.sysu.edu.cn)

Junbo Wang and Jianyou Liao developed MML with assistance from GPT-6.2 Astra. Both authors take joint responsibility for the reported results. **A manuscript is in preparation. Please contact the authors before citing this work.**

[Louvain algorithm · Blondel et al., 2008](https://doi.org/10.1088/1742-5468/2008/10/P10008) · [Classical modularity · Newman & Girvan, 2004](https://doi.org/10.1103/PhysRevE.69.026113) · [Resolution parameter · Reichardt & Bornholdt, 2006](https://doi.org/10.1103/PhysRevE.74.016110)

[Archived project homepage](docs/archive/README-before-MML.md) · [Original page with working historical links](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/168f96cf690151580b91c99a59655e68d2cabcf1/README.md) · [Repository license](LICENSE) · [R package license](SUNLouvainPath/DESCRIPTION)
