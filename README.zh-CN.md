# MML — Maximum Modularity in Louvain

**[English](README.md)** · **简体中文**

**MML 穷举分群方案，研究者选择评价指标。** 给定近邻数 $k$ 固定的 Jaccard 共享近邻图（SNN），固定 Louvain 的细胞访问顺序、移动规则、收缩规则和平局规则，只改变分辨率 $r$。MML 能在多项式时间内列出所有非负实数分辨率下可得到的不同最终划分，包括只在单个临界点出现的划分。

研究者可以根据自己的问题定义评分函数，对每个满足该指标适用条件的划分计算得分。使用同一批候选，就能比较不同指标给出的结果，或找出某个指标下得分最优的划分。经典 Newman–Girvan 模块度 $Q$ 是可选指标之一，R 包已提供它的得分。

[下载 MML v0.3.0](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/tag/v0.3.0) · [数学推导](docs/MATHEMATICAL_PROOF.md) · [Lean 形式化证明](lean/)

## MML 覆盖全部可达划分

在 Louvain 的每一步，候选移动的增益都是 $r$ 的一次函数。MML 从 $r=0$ 出发，追踪到下一个可能改变选择的交点，分别检查交点本身与紧邻它右侧的选择，并在群收缩后继续追踪。最后一条轨迹覆盖从最后一个临界点右侧直至正无穷的整个区间。追踪评分交点的思路来自对单参数贪心算法的研究。[Gupta 与 Roughgarden，2017，§§3.3.3–3.3.4](https://doi.org/10.1137/15M1050276)

### Lean 证明了穷举完整性和多项式运算上界

设 $S$ 为由 $n$ 个细胞构成的 Jaccard SNN 图，每个细胞有 $k>0$ 个近邻，剪枝规则对称。记 $E(S)$ 为 MML 枚举得到的有限划分集合。给定分辨率 $r$，从每个细胞各自成群开始，指定的确定性 Louvain 最终返回的规范划分记作 $L_S(r)$。

1. **穷举无遗漏，且每次运行结果唯一。** 对任意划分 $P$，都有

   $$P\in E(S) \quad\Longleftrightarrow\quad \exists\,r\in[0,\infty)\; L_S(r)=P.$$

   对每个实数 $r$，算法都会终止并返回唯一的规范划分。双向等价保证了在某段区间出现的划分和只在单个临界点出现的划分都会被列入，且列出的每项都能实际取得。[`louvain_enumeration_exact`](lean/RawJaccard.lean#L153) · [`raw_total_unique`](lean/RawJaccard.lean#L159)

2. **运算次数具有多项式上界。** 对每个固定的正整数 $k$，存在只依赖于 $k$ 的常数 $C(k)$，使得对任意 $n>0$ 和任意这样的图 $S$，稠密参考算法的运算次数均不超过 $C(k)n^{14}$。该模型对精确算术和随机访问按单位成本计数，包括建图、枚举、去重、计算内置经典模块度和收集全部最高分划分。ROGUE、SCCAF 和 Silhouette 在获得划分后另行计算，各自的评分耗时应另外计入。[`arithmetic_n14`](lean/ArithmeticBound.lean#L99) · [成本模型与构建说明](lean/README.md)

3. **经典模块度评分准确，且包含全部并列最高分方案。** 对总边权为正的图，设 $Q_S(P)$ 为划分 $P$ 在原图上的经典模块度。评分表为每个 $P\in E(S)$ 恰好保留一行，分数为 $Q_S(P)$。若研究者选择此指标，最高分划分的集合恰好是

   $$\{P\in E(S)\mid \forall P'\in E(S),\;Q_S(P')\le Q_S(P)\}.$$

   因此即使多个可达方案并列最高，也能将它们全部列出。[`scores_raw_exact`](lean/ScoredPath.lean#L37) · [`distinct_scores`](lean/ScoredPath.lean#L42) · [`best_exact`](lean/JaccardProgram.lean#L102)

## SNN 平均度有界时，稀疏扫描的运算上界为 $O_k(n^7)$

在单细胞分析中，剪枝后的 SNN 可以按稀疏图存储，逐条扫描非零边。记不同细胞间的无向边数为 $m$。当 $m\le c n$，且 $c$ 与细胞数无关时，SNN 的平均度有界。固定近邻数 $k$、常数 $c$ 和初始分割区间数后，稀疏算法穷举全部可达划分的算术运算上界为 $O(n^7)$。HESC 图有 498 个细胞、14,224 条边，平均每个细胞连接 57.1 个细胞。

<details>
<summary>稀疏上界的推导</summary>

1. **临界点数。** 固定 $k$ 后，清除 Jaccard 分母可将每条边的权重转成有界整数，上界只依赖 $k$。各细胞整数化加权度之和因此满足 $T=O_k(m)$。若 $T>0$，缩放后的划分得分可写为 $Ta-rb$，其中 $a,b$ 为整数，$0\le a\le T$，$0\le b\le T^2$。孤立交点的形式是 $T\Delta a/\Delta b$，所以候选临界点有 $O(T^3)$ 个。每个临界点及其右极限各运行一条轨迹，轨迹总数仍为 $O(T^3)$。[临界点计数](lean/BreakpointCount.lean)
2. **每条轨迹的扫描成本。** 每次接受移动都在 $O(T^3)$ 种目标系数对中严格前进，右极限运行在同分时按斜率比较。群收缩保留得分，至多 $n$ 个层级每层最多另加一轮无移动扫描，因此每条轨迹至多需要 $O(T^3+n)$ 轮。每轮只遍历各细胞、已存的非零边和相邻候选群，成本为 $O(n+m)$。代入 $m=O(n)$，全部扫描的成本为 $O_k(n^3)\times O_k(n^3)\times O(n)=O_k(n^7)$。[移动循环](SUNLouvainPath/src/path.cpp#L60)
3. **计入收缩和输出。** 设去重前有 $B=O(T^3)$ 个输出，即便将长度为 $n$ 的分群标签向量两两比较，去重也至多需要 $O(nB^2)=O_k(n^7)$ 次操作。为不同输出计算经典模块度另外需要 $O(B(n+m))$ 次操作。当前 C++ 实现在扫描时顺序遍历邻接表，使用按群编号索引的数组累加权重。收缩时要向有序映射插入边，每层至多需要 $O(m\log n+n)$ 次操作，每条轨迹至多 $n$ 层，因此所有轨迹的这部分成本在稀疏条件下至多为 $O_k(n^5\log n)$。用有序映射索引输出划分至多比较 $O(nB\log(B+1))$ 个细胞标签。这两项都在上面的运算次数界内。[群收缩](SUNLouvainPath/src/path.cpp#L125) · [划分索引](SUNLouvainPath/src/path.cpp#L312)

</details>

## 评价指标决定了 HESC 中得分最高的划分

在人胚胎干细胞分化数据中，MML 为 498 个细胞（$k=20$）找到了 **975 种不同划分**，覆盖 992 个分辨率段。下表分别列出每个指标在其适用范围内得分最高的划分。[HESC 数据，GEO GSE85066](https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE85066)

| 评价指标 | 最高分划分 | 群数 | 得分 | 可评分方案数（共 975 种） | 可取得该划分的 $r$ 示例 |
| --- | --- | ---: | ---: | ---: | ---: |
| ROGUE | P12 | 9 | 0.999789 | 60 | 4 |
| SCCAF 自投影准确率 | P1 | 3 | 1.000000 | 73 | 0 |
| 平均 Silhouette 轮廓宽度 | P6 | 8 | 0.521489 | 974 | 1 |
| 调整兰德指数（ARI） | P8 | 9 | 0.973899 | 975 | 2.9 |
| 经典模块度 | P6 | 8 | 0.863349 | 975 | 1 |

ROGUE 用 recount3 的基因读数估计衡量群内表达的均一性。SCCAF 衡量基因表达预测留出细胞群标签的准确率。Silhouette 在建图使用的前 10 个主成分上衡量群间分离程度。ARI 衡量划分与已有 9 类注释的吻合度。[评分规则与复现代码](docs/hesc/methods.zh-CN.md)

[全部 975 种划分的评分表](docs/hesc/partition-scores.csv) · [最高分方案的逐细胞群标签](docs/hesc/winning-memberships.csv)

## MML 以 R 包形式发布

MML 的 R 包名为 `SUNLouvainPath`。根据本机平台选择以下一组命令，在 R 中运行。

**64 位 x86 Windows，R 4.6.x。** 可以直接安装预编译的二进制包。

```r
install.packages(c("Matrix", "parallelly", "Rcpp", "SeuratObject"))
release_url <- "https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.0"
install.packages(paste0(release_url, "/SUNLouvainPath_0.3.0.zip"),
                 repos = NULL, type = "win.binary")
```

**Linux、macOS 或从源码安装的 Windows。** 源码安装需要 R ≥ 4.2 和支持 C++17 的编译工具。

```r
install.packages(c("Matrix", "parallelly", "Rcpp", "SeuratObject", "BH"))
release_url <- "https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.0"
install.packages(paste0(release_url, "/SUNLouvainPath_0.3.0.tar.gz"),
                 repos = NULL, type = "source")
```

## HESC 示例可复现分群并按自定义指标评分

包内示例会重新穷举分群，逐项核对每个细胞的分群标签、精确区间端点、模块度得分和推荐结果。`mml$partitions` 的每一行是一个细胞，每个以 `P` 开头的列是一种划分下所有细胞的分群标签。

```r
library(SUNLouvainPath)
hesc <- VerifyLouvainExample("hesc")
mml <- SeuratObject::Tool(hesc, slot = "SUNLouvainPath")
mml$partitions[1:5, c("cell", "P6", "P8")]
```

运行 ARI 示例前，请执行一次 `install.packages("mclust")`。下方的评分函数会将每种候选划分与 HESC 已有注释进行比较。换用其他指标时，替换 `score_partition()` 即可。最后一行可直接查看包内的经典模块度结果，供对照。

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

对自己的 SNN 图可使用 `EnumerateLouvain()`，默认搜索范围为 $[0,\infty)$。设置 `workers = 1L` 可用单线程运行，也可通过 `workers` 和 `split_points` 将各分辨率区间分配给多个线程。设置有限的 `r_max` 后，候选划分覆盖所选范围。[R 包与并行参数](SUNLouvainPath/)

## 作者

- **王俊博（Junbo Wang）** · [1124315977@qq.com](mailto:1124315977@qq.com)
- **廖建友（Jianyou Liao）** · [liaojy3@mail.sysu.edu.cn](mailto:liaojy3@mail.sysu.edu.cn)

王俊博、廖建友共同开发 MML，开发过程中使用了 GPT-6.2 Astra 辅助。两位作者对本项目报告的结果共同负责。**论文正在写作中，引用前请联系作者。**

[Louvain 算法 · Blondel 等，2008](https://doi.org/10.1088/1742-5468/2008/10/P10008) · [经典模块度 · Newman 与 Girvan，2004](https://doi.org/10.1103/PhysRevE.69.026113) · [分辨率参数 · Reichardt 与 Bornholdt，2006](https://doi.org/10.1103/PhysRevE.74.016110)

[原项目首页归档](docs/archive/README-before-MML.md) · [按原版本浏览归档首页及其链接](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/168f96cf690151580b91c99a59655e68d2cabcf1/README.md) · [仓库许可证](LICENSE) · [R 包许可证](SUNLouvainPath/DESCRIPTION)
