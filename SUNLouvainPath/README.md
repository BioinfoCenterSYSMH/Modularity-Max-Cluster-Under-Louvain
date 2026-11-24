# SUNLouvainPath

**共同开发者 · Developers**　王俊博 (Junbo Wang)、廖建友 (Jianyou Liao)、GPT-6.2 Astra (AI)。

**Manuscript in preparation. Please contact the author before citing. 论文正在写作中，引用前请联系作者。** [Contact · 联系方式](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/issues/new)

在已有 SNN 图上，枚举确定性多层 Louvain 对全部非负分辨率产生的不同分群，并用经典 Newman–Girvan 模块度给每种分群评分。

Windows 的 R 4.6.x 可以直接安装随附的二进制包。在已经装有 Seurat 的 R 会话中执行一次：

~~~r
base_url <- "https://raw.githubusercontent.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/main/downloads"
install.packages(paste0(base_url, "/SUNLouvainPath_0.2.1.zip"), repos = NULL, type = "win.binary")
~~~

源代码发行包为 `SUNLouvainPath_0.2.1.tar.gz`。从源码安装需要 Matrix、SeuratObject、Rcpp、BH 和 C++17 编译工具。

### Verify the bundled examples · 验证随包示例

Both calls reconstruct a graph, enumerate the partitions and check the output against stored references. 两个示例都可以离线运行。

~~~r
library(SUNLouvainPath)
ten <- VerifyLouvainExample("ten_cells")
hesc <- VerifyLouvainExample("hesc")
out <- SeuratObject::Tool(hesc, slot = "SUNLouvainPath")
out$recommendation
table(hesc$reference_annotation, out$partitions[[out$recommendation$representative_partition]])
~~~

10 细胞示例应得到 12 种划分，最高分方案有 3 群。HESC 的 498 个细胞应得到 975 种划分、992 个区间，最高分方案有 8 群，与 9 类原注释比较的调整兰德指数为 0.930962584。两次核验均检查每个细胞的划分、全部精确区间、评分及推荐结果。包内的 `extdata` 分开保存图输入和参考结果。HESC 的输入保留原始细胞顺序及建图边权，参考结果来自独立的早期计算。[HESC · GEO GSE85066](https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE85066)

### Run on a Seurat object · 在自己的对象上运行

~~~r
library(SUNLouvainPath)
obj <- EnumerateLouvain(obj, graph = "RNA_snn", k = 20)
out <- SeuratObject::Tool(obj, slot = "SUNLouvainPath")
out$partitions      # 第一列为细胞名，后续每列是一种不同分群
out$intervals       # 各分群出现的精确区间和端点开闭
out$scores          # 逐方案经典模块度、精确分数、并列最高分标志
out$recommendation  # 最高模块度方案首次出现的最小分辨率
~~~

将示例中的 20 替换为建图时的近邻数。仅有图时也可用
`EnumerateLouvain(obj, graph = "RNA_snn")`。默认找与存储值相容的最小近邻数；找不到时，按图中双精度数的精确二进制值计算。实际采用的方式记录在 `out$settings`。指定 `k` 时会严格核验非对角权重。包忽略自相似对角线。子图以对象中的细胞顺序运行，图外细胞的标签为 `NA`。

推荐表的 `recommended_resolution` 为精确分数，`partition` 可直接索引分群表。若 `status == "open_infimum"`，最高分首次出现于开区间，因此最小值为 `NA`。`infimum` 给出下确界，`representative_resolution` 和 `representative_partition` 给出可实际取到的一个最高分解。多个并列最高分均保存在 `scores` 中。无非对角边时经典模块度无定义。

~~~r
best <- out$scores[out$scores$is_max %in% TRUE, , drop = FALSE]
id <- out$recommendation$representative_partition
if (!is.na(id)) out$partitions[, c("cell", id), drop = FALSE]
~~~

使用对象列顺序作为细胞顺序，正增益平局取较小的当前群编号，零增益保留原位。聚合后按群内最早的原始细胞排序，沿用原图加权度。这个规则精确定义了“全部输出”的范围；Seurat 默认的随机起点和单例后处理可能给出不同结果。结果直接存放于 `obj@tools[["SUNLouvainPath"]]`。

引擎分别运行临界点和符号右极限。每次访问一个节点时，先选出目标群，再以精确整数运算找出有其他候选群可能超过它的首个交点。取整次运行中这些交点的最小值，即可确定本次轨迹有效的开区间。当所有选择都没有未来交点时，最后一个区间延伸至无穷大。该实现将 HESC 分析中的交点筛选推广到包支持的无向非负权图，输入细胞数、近邻数、边权和区间端点均由实际对象决定。

固定建图近邻数的 Jaccard 图满足关于细胞数的多项式时间论证。对于一般加权图，精确枚举仍然适用，但以整数化总边权计的上界可能很大。返回表仅描述这里定义的算法；推荐分辨率处的标签可直接从 `partitions` 取出。

0.2.0 的安装包在 SUN 论文的 GSE85066 HESC 原始 RNA_snn 上重现了先前独立计算的 975 种划分和 992 个连续区间。498 个细胞的逐细胞标签、每个区间的精确端点与开闭、全部经典模块度分数和最早推荐分辨率均已核对。另有不超过 10 个细胞的回归用例，涵盖并列最高、仅在一个精确端点出现的分群，以及最早区间左端开放的情形。设置表中的 `algorithm` 标识确定性规则，`package_version` 记录实际执行的软件版本。
