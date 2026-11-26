# MML — Maximum Modularity in Louvain

**固定一张细胞图，只改变分辨率 $r$，Louvain 到底能给出哪些分群？** MML 能在多项式时间内列出所有可能的最终划分，覆盖从零到正无穷的全部非负实数分辨率，包括只在某一个临界点出现的划分。它给每种划分计算同一个经典 Newman–Girvan 模块度 $Q$，并列出全部最高分方案。如果目标是从这些可达划分中取得经典模块度或其他分群评价指标的最大值，就无须人工调节分辨率。MML 直接给出经典模块度的最大值。对于其他指标，可以按同一标准给每个可达划分评分，再取最大值。

**Which partitions can Louvain return if only the resolution changes?** MML enumerates every distinct final partition attainable at any real resolution $r\geq 0$ in polynomial time, including partitions attained at a single critical value. It scores each partition by the same classical Newman–Girvan modularity $Q$ and returns every maximizer. If the goal is to maximize classical modularity or another clustering evaluation metric over these reachable partitions, there is no need to tune the resolution by hand. For another metric, score each enumerated partition by that metric and take the maximum.

这个结论适用于近邻数 $k$ 固定的 Jaccard 共享近邻图（SNN）。给定同一张图，从每个细胞各自成群出发，固定细胞访问顺序、移动与收缩规则、平局规则，只接受严格改善目标的移动。经典 $Q$ 的比较要求图的总边权为正。

The result applies to fixed-$k$ Jaccard shared nearest-neighbor (SNN) graphs. The specified deterministic Louvain procedure starts from singletons, fixes the visit order, move, contraction and tie rules, and accepts only strictly improving moves. Classical modularity is evaluated on a graph of positive total edge weight.

[Download MML v0.3.0 · 下载](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/tag/v0.3.0) · [Mathematical proof · 数学推导](docs/MATHEMATICAL_PROOF.md) · [Lean proofs · 形式化证明](lean/)

## Why enumeration is complete · 为什么能无遗漏穷举

固定每一步的候选移动后，其增益是 $r$ 的一次函数。MML 从 $r=0$ 出发，找出下一处可能改变选择的交点，在交点本身和紧邻它的右侧分别追踪 Louvain 的所有移动与收缩。如果后面再无交点，当前轨迹就覆盖直到正无穷的剩余区间。这个思路受到 Gupta 与 Roughgarden 关于单参数贪心算法的启发。[Gupta & Roughgarden, 2017, §§3.3.3–3.3.4](https://doi.org/10.1137/15M1050276)

Each candidate move has a gain that is affine in $r$. MML follows the decisions to the next crossing and evaluates the crossing itself as well as its right-hand limit. When no further crossing can change a decision, the same trajectory covers the rest of the half-line.

- **Coverage · 无遗漏。** Lean proves that a partition is in the finite output set **if and only if** some nonnegative real resolution returns it. 这同时保证每个列出的划分都能取得，每个能取得的划分都被列出。[Completeness theorem](lean/RawJaccard.lean#L153)
- **Complexity · 多项式时间。** For a fixed positive $k$ and $n>0$ cells, Lean proves a worst-case bound of $C(k)n^{14}$ operations for the dense reference algorithm, including enumeration, deduplication, scoring and selection. 上界按单位成本的精确算术与随机访问计数，常数只依赖 $k$。R/C++ 包使用稀疏数据结构，运行结果可用下方示例独立核验。[Arithmetic bound](lean/ArithmeticBound.lean#L99) · [Cost model and build instructions](lean/README.md)
- **Scoring · 经典模块度。** The score of each row is its classical $Q$ on the original graph. The proof also identifies all ties for the highest score. 搜索时改变 $r$，比较最终方案时统一用经典 $Q$（评分分辨率为 1）。[Exact scores](lean/ScoredPath.lean#L37) · [Maximizers](lean/JaccardProgram.lean)

## HESC · 以人胚胎干细胞分化数据为例

498 个细胞，近邻数 $k=20$。沿全部非负分辨率，MML 找到 **975 种不同划分**，分布在 992 个分辨率段。唯一最高分方案把细胞分成 **8 群**，经典 $Q\approx 0.863348742$，首次出现于 $r\approx 0.053519965$。与原有的 9 类注释事后比较，调整兰德指数（ARI）为 **0.930963**。

On the 498-cell HESC graph, MML found **975 distinct partitions** across 992 resolution intervals. The unique winner had **8 clusters**, with classical $Q\approx 0.863348742$. Its adjusted Rand index against the nine reference classes was **0.930963**. The reference labels were used only after selection. [HESC data · GEO GSE85066](https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE85066)

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
mml$scores[mml$scores$is_max, ]
mml$recommendation
```

`VerifyLouvainExample("hesc")` reruns MML and checks cell memberships, exact interval endpoints, scores and the recommendation against the bundled reference. The default search covers the whole half-line. Set `workers = 1L` in `EnumerateLouvain()` to run sequentially, or use `workers` and `split_points` to distribute intervals across threads. 设置有限的 `r_max` 后，返回的最优方案只针对选定范围。[R package and parallel options · R 包与并行参数](SUNLouvainPath/)

## Authors · 作者

- **Junbo Wang（王俊博）** · [1124315977@qq.com](mailto:1124315977@qq.com)
- **Jianyou Liao（廖建友）** · [liaojy3@mail.sysu.edu.cn](mailto:liaojy3@mail.sysu.edu.cn)

王俊博、廖建友共同开发 MML，开发过程中使用了 GPT-6.2 Astra 辅助。两位作者对本项目报告的结果共同负责。**论文正在写作中，引用前请联系作者。**

Junbo Wang and Jianyou Liao developed MML with assistance from GPT-6.2 Astra. Both authors take joint responsibility for the reported results. **A manuscript is in preparation. Please contact the authors before citing this work.**

[Louvain · Blondel et al., 2008](https://doi.org/10.1088/1742-5468/2008/10/P10008) · [Classical modularity · Newman & Girvan, 2004](https://doi.org/10.1103/PhysRevE.69.026113) · [Resolution parameter · Reichardt & Bornholdt, 2006](https://doi.org/10.1103/PhysRevE.74.016110)

[Previous README · 旧首页原文](docs/archive/README-before-MML.md) · [Old page with its original links · 按当时版本浏览](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/168f96cf690151580b91c99a59655e68d2cabcf1/README.md) · [Repository license](LICENSE) · [R package license](SUNLouvainPath/DESCRIPTION)
