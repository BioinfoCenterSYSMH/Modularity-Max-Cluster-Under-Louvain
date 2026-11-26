# MML — Maximum Modularity in Louvain

**MML 穷举分群方案，研究者选择评价指标。** 对近邻数 $k$ 固定的 Jaccard 共享近邻图（SNN），固定 Louvain 的细胞访问顺序、移动、收缩与平局规则，只改变分辨率 $r$。MML 能在多项式时间内列出 $r$ 从零到正无穷时可得到的每一种最终划分，包括只在单个临界点出现的划分。

研究者可以根据自己的问题定义评分函数，对穷举出的每种划分逐一计算，比较得分并选出符合该标准的方案。换一个指标，可以直接使用同一份分群结果，无须重新运行 Louvain 或手动调节分辨率。**经典模块度 $Q$ 是可选指标之一**，R 包已提供它的得分。

**MML enumerates the partitions. Researchers choose how to evaluate them.** On a fixed-$k$ Jaccard shared nearest-neighbor (SNN) graph, fix the Louvain visit order, move, contraction and tie rules, and vary only the resolution $r$. MML enumerates every distinct final partition reachable at any real $r\geq 0$ in polynomial time, including partitions reached at a single critical value.

Define a score for your research question and apply it to each enumerated partition. You can rank the candidates again under a different criterion using the same output, without rerunning Louvain or tuning the resolution by hand. **Classical modularity $Q$ is one optional metric** for which the R package supplies scores.

[Download MML v0.3.0 · 下载](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/tag/v0.3.0) · [Mathematical proof · 数学推导](docs/MATHEMATICAL_PROOF.md) · [Lean proofs · 形式化证明](lean/)

## Why enumeration is complete · 为什么能无遗漏穷举

固定每一步的候选移动后，其增益是 $r$ 的一次函数。MML 从 $r=0$ 出发，找出下一处可能改变选择的交点，在交点本身和紧邻它的右侧分别追踪 Louvain 的所有移动与收缩。如果后面再无交点，当前轨迹就覆盖直到正无穷的剩余区间。这个思路受到 Gupta 与 Roughgarden 关于单参数贪心算法的启发。[Gupta & Roughgarden, 2017, §§3.3.3–3.3.4](https://doi.org/10.1137/15M1050276)

Each candidate move has a gain that is affine in $r$. MML follows the decisions to the next crossing and evaluates the crossing itself as well as its right-hand limit. When no further crossing can change a decision, the same trajectory covers the rest of the half-line.

- **Coverage · 无遗漏。** Lean proves that a partition is in the finite output set **if and only if** some nonnegative real resolution returns it. 这同时保证每个列出的划分都能取得，每个能取得的划分都被列出。[Completeness theorem](lean/RawJaccard.lean#L153)
- **Complexity · 多项式时间。** For a fixed positive $k$ and $n>0$ cells, Lean proves a worst-case bound of $C(k)n^{14}$ operations for the dense reference algorithm, including enumeration, deduplication and the built-in classical modularity calculation and selection. 上界按单位成本的精确算术与随机访问计数，常数只依赖 $k$。自定义指标的额外计算时间取决于其评分函数。[Arithmetic bound](lean/ArithmeticBound.lean#L99) · [Cost model and build instructions](lean/README.md)
- **Built-in score · 包内评分。** For graphs of positive total edge weight, Lean also verifies the supplied classical modularity scores and all ties for their maximum. 研究者可直接取出每种划分的细胞标签，按其他标准评分。[Exact scores](lean/ScoredPath.lean#L37) · [Maximizers](lean/JaccardProgram.lean)

## HESC · 以人胚胎干细胞分化数据为例

MML 在 498 个细胞的 HESC 图（$k=20$）上穷举出 **975 种不同划分**，覆盖 992 个分辨率段。如果研究问题是“哪个划分最接近已有的 9 类注释”，可以用调整兰德指数（ARI）给全部 975 种划分打分。得分最高的是 **P8，9 群，ARI = 0.973899**。如果关心图上的经典模块度，同一批候选中得分最高的是 **P6，8 群，$Q = 0.863348742$**。

The 498-cell HESC graph yielded **975 distinct partitions** across 992 resolution intervals. Scoring all 975 by adjusted Rand index (ARI) against the nine reference classes selects **P8, with 9 clusters and ARI = 0.973899**. Scoring the same candidates by classical modularity selects **P6, with 8 clusters and $Q = 0.863348742$**. [HESC data · GEO GSE85066](https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE85066)

### Install and reproduce · 安装与复现

MML 的 R 包名为 `SUNLouvainPath`。以下命令在 64 位 x86 Windows 的 R 4.6.x 安装二进制包。The release also provides a source package for R ≥ 4.2 with a C++17 toolchain. [Source installation · 源码安装](SUNLouvainPath/README.md)

```r
install.packages(c("Matrix", "parallelly", "Rcpp", "SeuratObject"))
release_url <- "https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.0"
install.packages(paste0(release_url, "/SUNLouvainPath_0.3.0.zip"),
                 repos = NULL, type = "win.binary")

library(SUNLouvainPath)
hesc <- VerifyLouvainExample("hesc")
mml <- SeuratObject::Tool(hesc, slot = "SUNLouvainPath")
mml$partitions[1:5, c("cell", "P6", "P8")]
```

### Score the candidates with your own function · 用自己的指标评价分群

`mml$partitions` 的每一行是一个细胞，每个 `P` 列是一种划分。下例用 ARI 衡量与 HESC 已有注释的一致性。换用自己的指标时，替换 `score_partition()` 即可。Each candidate column contains one cluster assignment per cell. Here the scoring function uses the reference labels and returns a higher value for closer agreement.

```r
# For this ARI example, install mclust once with install.packages("mclust").
partitions <- mml$partitions
reference <- hesc$reference_annotation[match(partitions$cell, colnames(hesc))]
score_partition <- function(groups) mclust::adjustedRandIndex(groups, reference)

candidates <- partitions[setdiff(names(partitions), "cell")]
scores <- vapply(candidates, score_partition, numeric(1))
scores[scores == max(scores)]
#        P8
# 0.9738988
```

`VerifyLouvainExample("hesc")` reruns MML and checks cell memberships, exact interval endpoints, scores and the recommendation against the bundled reference. The default search covers the whole half-line. Set `workers = 1L` in `EnumerateLouvain()` to run sequentially, or use `workers` and `split_points` to distribute intervals across threads. 设置有限的 `r_max` 后，可评价的候选集覆盖所选范围。[R package and parallel options · R 包与并行参数](SUNLouvainPath/)

## Authors · 作者

- **Junbo Wang（王俊博）** · [1124315977@qq.com](mailto:1124315977@qq.com)
- **Jianyou Liao（廖建友）** · [liaojy3@mail.sysu.edu.cn](mailto:liaojy3@mail.sysu.edu.cn)

王俊博、廖建友共同开发 MML，开发过程中使用了 GPT-6.2 Astra 辅助。两位作者对本项目报告的结果共同负责。**论文正在写作中，引用前请联系作者。**

Junbo Wang and Jianyou Liao developed MML with assistance from GPT-6.2 Astra. Both authors take joint responsibility for the reported results. **A manuscript is in preparation. Please contact the authors before citing this work.**

[Louvain · Blondel et al., 2008](https://doi.org/10.1088/1742-5468/2008/10/P10008) · [Classical modularity · Newman & Girvan, 2004](https://doi.org/10.1103/PhysRevE.69.026113) · [Resolution parameter · Reichardt & Bornholdt, 2006](https://doi.org/10.1103/PhysRevE.74.016110)

[Previous README · 旧首页原文](docs/archive/README-before-MML.md) · [Old page with its original links · 按当时版本浏览](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/168f96cf690151580b91c99a59655e68d2cabcf1/README.md) · [Repository license](LICENSE) · [R package license](SUNLouvainPath/DESCRIPTION)
