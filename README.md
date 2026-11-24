# Modularity-Max-Cluster-Under-Louvain

本项目由王俊博、廖建友共同开发，开发过程中使用了 GPT-6.2 Astra 辅助。两位作者对本项目报告的结果共同负责。

Junbo Wang and Jianyou Liao developed this project with assistance from GPT-6.2 Astra. Both authors take joint responsibility for the results reported in this project.

**Manuscript in preparation. Please contact the authors before citing this work.**  
**论文正在写作中。引用本工作前，请先联系作者。**

**Contact the authors · 联系作者**

- 王俊博 (Junbo Wang) · [1124315977@qq.com](mailto:1124315977@qq.com)
- 廖建友 (Jianyou Liao) · [liaojy3@mail.sysu.edu.cn](mailto:liaojy3@mail.sysu.edu.cn)

[GitHub Issues · 项目讨论](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/issues/new)

**如果唯一目标是在 Louvain 能返回的分群中取得最高经典模块度 $Q$，那么，对本文定义的确定性 Louvain 算法，在分辨率以外的条件全部固定后，人工调节分辨率的时代就彻底结束了。** 无论手动选哪个非负分辨率，它给出的划分都已包含在一个多项式算法的枚举结果中。直接比较这些划分的经典模块度，就能找出全部并列最优方案。对近邻数 $k$ 固定、总边权为正的 Jaccard SNN 图，Lean 已证明所定义的算法枚举无遗漏，返回全部经典模块度最高的方案，并在单位成本精确算术模型下至多使用 $O(n^{14})$ 次运算。结合下文的位长分析可得 **“给定有理阈值 $q$，是否存在某个非负分辨率，使 Louvain 返回的划分满足经典模块度 $Q\ge q$？”这一判定问题属于 P。**

**For the deterministic Louvain algorithm defined here, the era of manual resolution tuning is over when all other conditions are fixed and the sole objective is to maximize classical modularity $Q$ among the partitions Louvain can return.** Every partition obtainable by choosing a nonnegative resolution by hand is already in the enumeration. Comparing their classical modularity scores identifies every maximizer. For Jaccard SNN graphs with fixed neighbor count $k$ and positive total edge weight, Lean proves that the algorithm enumerates every reachable output, returns all classical modularity maximizers and uses at most $O(n^{14})$ operations on a unit-cost exact arithmetic RAM. The bit-length argument below gives the corresponding decision result. **Given a rational threshold $q$, deciding whether any nonnegative resolution returns a partition with classical modularity $Q\ge q$ is in P.**

## What the package computes · 这个包计算什么

On a fixed-$k$ Jaccard shared nearest-neighbor (SNN) graph with $n$ cells, `SUNLouvainPath` uses a **polynomial-time algorithm** to enumerate every final partition the specified deterministic Louvain procedure can return across all nonnegative real resolutions, including partitions attained at a single endpoint. Lean verifies a conservative worst-case bound for the dense local-gain algorithm of **$O(n^{14})$ exact arithmetic operations**. The package ranks the partitions by classical Newman–Girvan modularity (scoring resolution 1) and reports all maximizers. It returns the earliest maximizing resolution when attained, or the infimum and an attainable representative when the first maximizing interval is open on the left. [How the bound is obtained](#complexity)

给定 $n$ 个细胞构成的 Jaccard SNN 图，近邻数 $k$ 固定，细胞顺序、移动和平局规则也固定。**我们的算法能在多项式时间内枚举 Louvain 在全部非负分辨率下可返回的最终划分，包括只在单个临界点出现的划分。** Lean 已验证证明包中稠密局部增益算法的保守最坏情形上界为 **$O(n^{14})$ 次精确算术运算**。本包逐一计算各方案的经典模块度，列出全部最高分方案，并给出达到最高分的最小分辨率。如果最早的最高分区间为左开区间，则给出下确界和一个能实际取得最高分的分辨率。[复杂度推导](#complexity)

本包的评分和搜索分别有其来源。Newman 与 Girvan 定义了评价划分的经典模块度；Reichardt 与 Bornholdt 研究了带分辨率参数的目标，在保持节点期望度的零模型下取 $r=1$ 即对应经典模块度。Blondel 等提出 Louvain，通过局部移动和群收缩寻找高模块度划分。

We use the classical Newman–Girvan score to rank outputs, the Reichardt–Bornholdt resolution parameter to vary the objective during search, and Blondel et al.’s multilevel Louvain procedure as the starting point. [Newman & Girvan, 2004](https://doi.org/10.1103/PhysRevE.69.026113) · [Reichardt & Bornholdt, 2006](https://doi.org/10.1103/PhysRevE.74.016110) · [Blondel et al., 2008](https://doi.org/10.1088/1742-5468/2008/10/P10008)

## Why we follow the greedy comparisons · 单参数贪心算法给我们的启示

Gupta 与 Roughgarden（2017）给了我们一个出发点：在他们研究的一类单参数贪心算法中，参数虽然连续，只要每一步候选项的得分排序保持不变，整次运行就会作出相同选择。§3.3.3 说明，当每个对象可能出现的属性值个数、每对得分曲线的交点数和单次运行时间都有多项式上界，且相关比较和交点可以高效求出时，在给定样本上选出表现最好的参数可以在多项式时间内完成。§3.3.4 还讨论了这一思路向局部搜索的扩展。[Gupta & Roughgarden, *A PAC Approach to Application-Specific Algorithm Selection*, SIAM Journal on Computing](https://doi.org/10.1137/15M1050276) · [§§3.3.3–3.3.4 原文，第 1001 页](https://theory.stanford.edu/~tim/papers/features.pdf#page=10)

Gupta and Roughgarden showed how to optimize a parameter over a sample for a class of single-parameter greedy heuristics. The trajectory stays fixed while all relevant score comparisons have the same outcome. Their polynomial-time result requires polynomial bounds on the number of attainable attribute values per object, the crossings per score pair and the time per run, together with efficient identification of comparisons and computation of crossings.

Balcan、Dick 与 Lang（2020）在层次聚类中给出了具体先例。他们用执行树记录各参数区间的合并序列，在叶节点评价所得聚类。

Their *Learning to Link* enumerates the merge sequences of a linkage family on a fixed input and evaluates the loss at each leaf. [Balcan, Dick & Lang, *Learning to Link*, ICLR 2020](https://iclr.cc/virtual_2020/poster_S1eRbANtDB.html) · [§4 and Algorithms 2–3](https://www.cs.cmu.edu/~ninamf/papers/learn-link.pdf)

**我们从中借鉴的是追踪比较交点的思路。** 对 Louvain，要追踪的是“当前节点移入哪个相邻群的增益最大”。代码分别检查增益相等的分辨率本身及其右侧，并在每次群收缩后继续追踪。本文为固定 $k$ 的 Jaccard SNN 图证明了这套具体规则覆盖所有可达划分，给出了相应的多项式界。

**Our Louvain result** follows the crossings of candidate move gains, checks ties at the boundary itself, and follows the choices through contraction. The completeness proof and the fixed-$k$ polynomial bound for this procedure are developed here. [Lean 主定理 · Louvain completeness theorem](lean/RawJaccard.lean#L153) · [Complexity](#complexity)

## Install · 安装

With R 4.6.x on 64-bit x86 Windows, run the following in R. 在 64 位 x86 Windows 的 R 4.6.x 中可直接运行以下代码安装二进制包。

```r
install.packages(c("Matrix", "Rcpp", "SeuratObject"))
base_url <- "https://raw.githubusercontent.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/main/downloads"
install.packages(paste0(base_url, "/SUNLouvainPath_0.2.1.zip"),
                 repos = NULL, type = "win.binary")
```

For a source installation, use R ≥ 4.2, a C++17 toolchain and the BH headers. 源码安装需要 R ≥ 4.2、C++17 编译工具和 BH 头文件。

```r
install.packages(c("Matrix", "Rcpp", "SeuratObject", "BH"))
base_url <- "https://raw.githubusercontent.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/main/downloads"
install.packages(paste0(base_url, "/SUNLouvainPath_0.2.1.tar.gz"),
                 repos = NULL, type = "source")
```

## Verify both examples · 运行两个验证示例

Both input graphs and their reference results ship inside the package. Installation is the only step that needs a download. Each call reconstructs the graph in the original cell order, runs the public enumerator, checks every membership column, exact interval endpoint, boundary inclusion, exact modularity score and recommendation, and independently recomputes the winning score from the graph edges. A mismatch stops the call with an error.

两个示例都随包安装，可离线运行。函数从邻居重叠数还原图，重新分群，并与单独保存的参考结果逐项核对。返回值是 Seurat 对象，可直接查看分群表、区间表、评分和推荐结果。示例使用单行占位表达矩阵，计算输入是随包提供的 SNN 图。

```r
library(SUNLouvainPath)
ten  <- VerifyLouvainExample("ten_cells")
hesc <- VerifyLouvainExample("hesc")

out <- SeuratObject::Tool(hesc, slot = "SUNLouvainPath")
out$scores[out$scores$is_max, ]
out$recommendation
best <- out$recommendation$representative_partition
table(reference = hesc$reference_annotation, cluster = out$partitions[[best]])
```

- **Ten cells · 10 细胞** — A demonstration graph with 19 edges and $k=3$. Expect **12 distinct partitions in 12 intervals**. P5 has 3 clusters and wins with exact $Q=5369/13122$. Its first resolution is `81/92`. The saved output is a regression reference. 这是快速验证安装与计算结果的示例。
- **HESC · 人胚胎干细胞分化数据** — The original ordered SNN graph for 498 cells has 14,224 undirected off-diagonal edges and $k=20$. Expect **975 distinct partitions in 992 intervals**. P6 has 8 clusters, with $Q\approx 0.863348742$ and first resolution $r\approx 0.053519965$. Several intervals can return the same partition. The 9 reference classes give an adjusted Rand index of 0.930962584 against P6. HESC 的逐细胞划分、精确区间和评分来自先于本 R 包实现的独立计算。原注释用于事后比较，未参与模块度择优。[HESC dataset · 数据来源，GEO GSE85066](https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE85066)

## Use your own graph · 分析自己的图

```r
obj <- EnumerateLouvain(obj, graph = "RNA_snn", k = 20)
out <- SeuratObject::Tool(obj, slot = "SUNLouvainPath")
names(out)
out$partitions[1:3, 1:2, drop = FALSE]
head(out$intervals)
out$scores[out$scores$is_max %in% TRUE, , drop = FALSE]
out$recommendation
```

Use the neighbor count used to construct your graph. Cell order and tie rules are part of the algorithm definition. Seurat's default random starts or singleton postprocessing can produce other partitions. The optimum reported here is over the outputs reachable by this deterministic algorithm on the supplied graph. 请将示例的 20 替换为实际建图近邻数。最高分的范围限于该确定性算法在输入图上可达的划分。[R package and detailed behavior · R 包说明](SUNLouvainPath/)

## Formal proof · Lean 形式化证明

The main Lean theorem equates membership in the finite enumerated set with being the final output of the specified Louvain procedure at some real resolution $r\geq 0$. For Jaccard SNN graphs with fixed neighbor count $k$, Lean also proves a uniform arithmetic operation bound for computing all distinct partitions, their classical modularity scores and all ties for the maximum. The code and documentation distinguish the mathematical proof from tests of the R/C++ implementation.

Lean 主定理证明了枚举结果与所有非负实数分辨率下的可达终态完全一致，并覆盖仅在临界点出现的分群。固定近邻数时，形式化的 $O(n^{14})$ 单位成本算术上界覆盖建图、枚举、去重、评分和选出全部最高分方案。R 包可用上面的两个示例直接核验。[Proof and build instructions · 证明与构建说明](lean/) · [Main theorem · 主定理](lean/RawJaccard.lean#L153) · [Download proof · 下载证明包](downloads/Louvain_Lean_proof.zip)

## Complexity

Brandes 等证明，在一般图的全部划分中，判定是否存在经典模块度达到给定阈值的划分是强 NP 完全问题。本文的 P 结论限定在固定 $k$ 的 Jaccard SNN 图上，对指定 Louvain 只改变分辨率所能返回的划分进行判定。

Brandes et al. proved strong NP-completeness of the unrestricted modularity threshold problem. Our decision problem ranges over the outputs reachable by the specified Louvain procedure on the fixed-$k$ graph family. [Brandes et al., *On Modularity Clustering*, 2008](https://doi.org/10.1109/TKDE.2007.190689) · [Theorem 4.4, author copy](https://www.algo.rwth-aachen.de/team/hoefer/papers/Brandes07ModularityJ.pdf)

固定 $k$ 后，为什么能得到 $O(n^{14})$？下述计数针对证明包中使用稠密表缓存连边权重、按细胞累加局部增益的算法。设 $T$ 为清除 Jaccard 权重分母后的加权度总和。每条边的整数权重有一个只依赖 $k$ 的上界，所以 $T=O(n^2)$。一个划分在分辨率 $r$ 处的目标值乘以公共因子后可以写为 $Ta-rb$，其中 $a$ 是群内边权总和（每条无向边按两个方向计），$b$ 是各群加权度总和的平方和，即 $b=\sum_C \mathrm{vol}(C)^2$。整数系数满足 $0\le a\le T$ 和 $0\le b\le T^2$。[Lean 中的目标函数](lean/Graph.lean#L29-L38) · [Jaccard 权重与搜索上界](lean/Jaccard.lean#L56-L77)

1. **最多 $O(n^6)$ 个临界点。** 两种候选移动得分线的孤立交点位于 $r=T\Delta a/\Delta b$，其中 $\Delta b\ne0$。固定输入图后 $T$ 是常数，可能出现的整数差值对至多有 $(2T+1)(2T^2+1)$ 种。从零开始，每轮分别检查当前点及其右侧紧邻区间，然后前进到下一个临界点。
2. **每次运行至多 $O(n^6)$ 轮扫描。** 整个分群过程至多有 $(T+1)(T^2+1)$ 种目标系数对 $(a,b)$。每次接受移动都严格提高目标值，收缩时保留原划分的系数。右极限遇到同分时按斜率排序，同样严格前进。故跨越全部层级，也只能有这么多次严格改进。每层至多再做一轮无移动扫描，层数至多为 $n$。[移动规则](lean/Graph.lean#L78) · [收缩规则](lean/Graph.lean#L176)
3. **每轮 $O(n^2)$ 次算术运算。** 逐节点累加邻边并比较相邻候选群，每轮最多处理 $O(n^2)$ 个邻接项。三项相乘给出 $O(n^6\cdot n^6\cdot n^2)=O(n^{14})$。每个不同输出可用 $O(n^2)$ 次运算计算经典模块度。Lean 单独验证了各层缓存的构建成本，并证明输出去重、评分和收集全部最高分方案合计至多需要 $O(n^{13})$ 次运算。固定 $k$ 时，这些整数和临界分数的分子、分母都只有 $O(\log(n+1))$ 位。与以二进制输入的有理阈值 $q$ 作精确比较，其位运算代价也是输入长度的多项式。

For fixed $k$, scaling the weights to integers gives total weighted degree $T=O(n^2)$. Each partition has a scaled objective $Ta-rb$ with integer coefficients $0\le a\le T$ and $0\le b\le T^2$. There are $O(T^3)$ possible critical resolutions because each is determined by the two integer differences in $T\Delta a/\Delta b$. At each boundary the algorithm traces both the point and its right-hand limit. Each trace makes at most $O(T^3)$ improving moves across all levels, since the score strictly increases among the available coefficient pairs and contraction preserves the score. The same argument holds on the right using slope to break score ties. Each level adds at most one unchanged sweep. Scanning adjacency entries and candidate communities takes $O(n^2)$ arithmetic operations per sweep. Including level preparation, one point or right-limit trajectory costs $O(n^8)$ operations. Deduplicating, scoring and retaining all tied maximizers costs $O(n^{13})$ in total. The resulting end-to-end bound is $O(n^{14})$ arithmetic RAM operations. Intermediate integers have $O(\log(n+1))$ bits, and the final comparison with the binary-encoded rational threshold takes polynomial bit time.

**Lean 证明的成本模型。** 对每个固定的正整数 $k$，存在只依赖于 $k$ 的常数 $C(k)$，使任一 $n>0$ 的输入都满足 $\mathrm{steps}\le C(k)n^{14}$。计数起于等长近邻集合和对称剪枝掩码，止于可达划分的去重评分表和全部最高分方案。模型将精确标量运算、比较和随机访问计为单位成本，并计入表的构造成本。上述位长分析给出通常意义下的多项式判定时间。端到端位运算成本及 R/C++ 二进制实现的运行成本仍有待单独形式化。[成本模型](lean/MeteredTables.lean) · [算术上界](lean/ArithmeticBound.lean) · [原图上的经典模块度](lean/ScoredPath.lean)

**Formal cost model.** For each fixed positive $k$, Lean proves a uniform worst-case bound $C(k)n^{14}$ for the charged operations of the dense arithmetic RAM algorithm, including table construction. It also proves that the scores on the original unscaled graph are exact. The polynomial bit-time conclusion uses the separate bit-length argument above. The R/C++ package uses sparse data structures and is checked against the two bundled examples. [Arithmetic bound](lean/ArithmeticBound.lean) · [Output and scoring theorem](lean/ScoredPath.lean)

## Related resolution searches · 相关的分辨率搜索方法

Bettinelli 等（2012）给出了追踪参数化模块度全局最优解的精确方法。Weir 等（2017）的 CHAMP 以给定的候选划分为输入，找出每个候选在哪些参数范围内取得最高分。Arimiyaw 等（2026）则在实际应用中对 0.5 至 1.5 的 11 个 Louvain 分辨率逐点评分（表 2）。本文所枚举的集合由另一个问题定义：给定这张图和确定性运行规则，哪些划分确实能在某个分辨率被返回？

Bettinelli et al. traced global optima of a parametric modularity objective. CHAMP compared an input set of partitions across parameter values. Arimiyaw et al. reported Louvain results on an eleven-point resolution grid. Our enumeration follows the final partitions returned by a specified run as resolution varies continuously. [Bettinelli, Hansen & Liberti, 2012](https://doi.org/10.1103/PhysRevE.86.016107) · [Weir et al., CHAMP, 2017](https://doi.org/10.3390/a10030093) · [Arimiyaw et al., 2026, Table 2](https://doi.org/10.1016/j.tust.2026.107708)

## Downloads and licenses · 下载与许可

[GitHub Release v0.2.1](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/tag/v0.2.1) · [Windows binary](downloads/SUNLouvainPath_0.2.1.zip) · [R source archive](downloads/SUNLouvainPath_0.2.1.tar.gz) · [SHA-256 checksums](downloads/SHA256SUMS)

The repository includes its original MIT license. The R package declares GPL-3 in its DESCRIPTION and includes the GPL text. 仓库保留原有 MIT 许可文件，R 包的 DESCRIPTION 单独声明 GPL-3。[Repository license](LICENSE) · [R package metadata](SUNLouvainPath/DESCRIPTION) · [R package license text](SUNLouvainPath/inst/COPYING)

