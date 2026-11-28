# MML Beta 4 · Exact Louvain resolution paths for Seurat

[简体中文](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/README.zh-CN.md)

MML enumerates the cell partitions that Louvain can return on a fixed shared nearest-neighbor (SNN) graph as resolution varies. Beta 4 adds an exact-arithmetic implementation of Seurat 5.5’s Louvain algorithms, including changes in which random start wins. Each retained partition has exact resolution boundaries, including results that occur at a single point. Classical modularity is supplied as an optional score. Users can apply their own metrics to the cell memberships.

## Install version 0.3.1.9004

Run this in x64 R 4.6.x on Windows. A source installation on other platforms requires a C++17 toolchain and the R package `BH` in addition to the dependencies below. [Windows binary](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9004-beta.4/SUNLouvainPath_0.3.1.9004.zip) · [Source archive](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9004-beta.4/SUNLouvainPath_0.3.1.9004.tar.gz) · [SHA256 checksums](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9004-beta.4/SHA256SUMS)

```r
deps <- c("Matrix", "parallelly", "Rcpp", "SeuratObject", "withr")
missing <- deps[!vapply(deps, requireNamespace, logical(1), quietly = TRUE)]
if (length(missing)) install.packages(missing, repos = "https://cloud.r-project.org")

pkg <- file.path(tempdir(), "SUNLouvainPath_0.3.1.9004.zip")
download.file(
  "https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9004-beta.4/SUNLouvainPath_0.3.1.9004.zip",
  pkg, mode = "wb"
)
install.packages(pkg, repos = NULL, type = "win.binary")
library(SUNLouvainPath)
```

## Enumerate a Seurat graph and query specific resolutions

Given a Seurat object `obj` containing `RNA_snn`, this example enumerates the continuous interval `[0,1]` and queries two exact fractions. `queries` reports each query’s status, `query_idents` its final labels, and `raw$partitions` the optimizer assignments before singleton handling.

```r
obj <- EnumerateLouvain(
  obj, graph = "RNA_snn", louvain_engine = "seurat", r_max = 1,
  seurat.control = list(algorithm = 2L, n.start = 10L, random.seed = 0L,
                        resolution = c("1/2", "4/5"))
)
out <- SeuratObject::Tool(obj, slot = "SUNLouvainPath")
out$queries
out$query_idents
out$intervals
out$raw$partitions
```

- **Simple engine.** The default call `EnumerateLouvain(obj, graph = "RNA_snn")` uses `louvain_engine = "simple"`, `max_clusters = 101` and `r_max = Inf`. To include every cluster count, set `max_clusters = Inf`. The finite cluster cap permits graph-certified pruning. Set `workers = 1L` for a single thread.
- **Seurat engine.** `algorithm = 1L` selects original Louvain and `2L` adds multilevel refinement. A fixed `random.seed`, `n.start` and `n.iter` define the optimizer run. Objective 1 scans the requested range, while `modularity.fxn = 2L` caps the upper resolution at 1. The cluster cap applies after singleton handling. With `group.singletons = TRUE`, MML retains individual cells when all groups are singletons. SLM and Leiden are outside this engine’s scope. [Full controls, output fields and native comparisons](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/SUNLouvainPath/README.md#english)

## Validation and formal proof

- **HESC.** On 498 cells, Simple returned 303 partitions across 312 intervals with the default cap. The unrestricted path had 975 partitions. Every retained membership, exact modularity score and resolution boundary agreed with the unrestricted reference. [HESC results](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/validation/cluster-limits.tsv)
- **Seurat 5.5.** The engine matched an independent exact reference at 1,067 probes across 14 graph and parameter configurations. On a 50-cell PBMC graph, native Seurat matched cell memberships at all 501 comparison resolutions from 0 to 5. In a separate 108-query native-double test focused on critical points, rounding changed memberships twice. [Exact reference](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/validation/seurat-oracle.md) · [PBMC results](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/validation/seurat-pbmc-results.tsv) · [Native differences](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/validation/seurat-native-differences.tsv)
- **Lean 4.** For the original deterministic Simple model on a fixed Jaccard SNN, the proof identifies precisely the partitions reachable at any nonnegative real resolution, including endpoint-only results. For fixed neighbor count, the formal dense enumeration and scoring algorithm has an `O(n^14)` arithmetic-operation upper bound for `n` cells. The new Seurat engine is covered by the separate validation above. [Lean proof archive](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9004-beta.4/Louvain_Lean_proof.zip)

A separate Windows-binary check tested raw optimizer memberships on five small graphs under nine configurations, using one thread and an unlimited cluster count. At all 3,485 exact probes, precisely one output interval covered the query and its cell membership matched the independent solver. [Test results and reference code](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/tree/v0.3.1.9004-beta.4/validation/independent)

## Authors

Junbo Wang and Jianyou Liao developed MML with assistance from GPT-6.2 Astra. Both authors take joint responsibility for the reported results. The manuscript is in preparation. Please contact the authors before citing this work. [Junbo Wang · 1124315977@qq.com](mailto:1124315977@qq.com) · [Jianyou Liao · liaojy3@mail.sysu.edu.cn](mailto:liaojy3@mail.sysu.edu.cn)
