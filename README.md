# MML Beta 1 · 0.3.1.9001

[English](README.md) · [简体中文](README.zh-CN.md)

[Beta release and installation](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/tag/v0.3.1.9001-beta.1) · [Stable release v0.3.0](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/tag/v0.3.0)

[Windows R 4.6.x x64](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9001-beta.1/SUNLouvainPath_0.3.1.9001.zip) · [R source / R 源码](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9001-beta.1/SUNLouvainPath_0.3.1.9001.tar.gz) · [Lean](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9001-beta.1/Louvain_Lean_proof.zip) · [SHA-256](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9001-beta.1/SHA256SUMS)

MML enumerates every distinct final partition returned by its deterministic Louvain rule as resolution varies over the requested range, including partitions confined to one exact endpoint. Researchers can score those partitions using their preferred metric. The package supplies classical modularity, all tied maxima and the earliest maximizing resolution. If only an open infimum exists, the recommendation includes an attainable representative.

This beta detects connected components, preserves the original cell order and graph-wide weight scale, and directly solves isolated cells, independent pairs and the all-singleton tail. For the remaining search it reuses certified moves across adjacent resolutions and evaluates ambiguous endpoints separately. The R interface and the four result tables are compatible with version 0.3.0.

Use the first example below on a Seurat object with an SNN graph. The default covers all nonnegative resolutions with splits at 0.5, 1 and 2 and uses up to four available cores. Use `workers = 1L, split_points = numeric(0)` for a serial, unsplit search, or set an inclusive exact maximum such as `r_max = "3/2"`. Query `out$settings$search_plan` for the chosen route, component sizes, edge count and the exact start of the singleton tail. The second example below checks the two bundled datasets against independent references.

Junbo Wang and Jianyou Liao developed MML with assistance from GPT-6.2 Astra. Both authors take joint responsibility for the reported results. The manuscript is in preparation. Please contact the authors before citing. [Junbo Wang](mailto:1124315977@qq.com) · [Jianyou Liao](mailto:liaojy3@mail.sysu.edu.cn)

```r
library(SUNLouvainPath)
obj <- EnumerateLouvain(obj, graph = "RNA_snn", k = 20, workers = 1L)
out <- SeuratObject::Tool(obj, slot = "SUNLouvainPath")
out$settings$search_plan
out$partitions
out$intervals
out$scores
out$recommendation
```

```r
ten <- VerifyLouvainExample("ten_cells")
hesc <- VerifyLouvainExample("hesc")
```
