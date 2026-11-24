# Modularity-Max-Cluster-Under-Louvain

**共同开发者 · Developers**　王俊博 (Junbo Wang)、廖建友 (Jianyou Liao)、GPT-6.2 Astra (AI)。

**Manuscript in preparation. Please contact the author before citing this work.**  
**论文正在写作中。引用本工作前，请先联系作者。** [Contact the author · 联系作者](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/issues/new)

## What the package computes · 这个包计算什么

For a fixed shared nearest-neighbor (SNN) graph and fixed Louvain rules, which partition has the highest classical modularity among all partitions that the algorithm can return? `SUNLouvainPath` enumerates the distinct final partitions across **all nonnegative real resolutions**, including outputs attained only at a single boundary. It evaluates each partition with the same classical Newman–Girvan modularity $Q$ (scoring resolution 1) and reports every maximizer. If the earliest maximizing interval has an open left endpoint and the endpoint itself does not attain the maximum, the package returns its infimum and an attainable example resolution.

给定一张 SNN 图，固定细胞顺序、移动和平局规则后，Louvain 在不同分辨率下能给出哪些划分？其中哪种划分的经典模块度最高？本包枚举全部非负分辨率下该算法可以返回的分群，包括只在单个端点出现的分群。每个方案均按同一个经典模块度评分。推荐结果给出达到最高分的最小分辨率；如果只有下确界，则另给出一个能实际取得最高分的分辨率和对应划分。

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

The main Lean theorem equates membership in the finite enumerated set with being the final output of the specified Louvain procedure at some real resolution $r\geq 0$. For Jaccard SNN graphs with fixed neighbor count $k$, the formal development also bounds the search budgets polynomially in the number of cells. The code and documentation distinguish the mathematical proof from tests of the R/C++ implementation.

Lean 主定理证明了枚举结果与所有非负实数分辨率下的可达终态完全一致，并覆盖仅在临界点出现的分群。固定近邻数的 Jaccard SNN 图满足已形式化的多项式搜索上界。R 包可用上面的两个示例直接核验。[Proof and build instructions · 证明与构建说明](lean/) · [Main theorem · 主定理](lean/RawJaccard.lean#L153) · [Download proof · 下载证明包](downloads/Louvain_Lean_proof.zip)

## Downloads and licenses · 下载与许可

[Windows binary](downloads/SUNLouvainPath_0.2.1.zip) · [R source archive](downloads/SUNLouvainPath_0.2.1.tar.gz) · [SHA-256 checksums](downloads/SHA256SUMS)

The repository includes its original MIT license. The R package declares GPL-3 in its DESCRIPTION and includes the GPL text. 仓库保留原有 MIT 许可文件，R 包的 DESCRIPTION 单独声明 GPL-3。[Repository license](LICENSE) · [R package metadata](SUNLouvainPath/DESCRIPTION) · [R package license text](SUNLouvainPath/inst/COPYING)

