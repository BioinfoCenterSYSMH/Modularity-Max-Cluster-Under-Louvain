# SUNLouvainPath

本项目由王俊博、廖建友共同开发，开发过程中使用了 GPT-6.2 Astra 辅助。两位作者对本项目报告的结果共同负责。

Junbo Wang and Jianyou Liao developed this project with assistance from GPT-6.2 Astra. Both authors take joint responsibility for the results reported in this project.

**Manuscript in preparation. Please contact the author before citing. 论文正在写作中，引用前请联系作者。** [Contact · 联系方式](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/issues/new)

在已有 SNN 图上，枚举确定性多层 Louvain 在指定分辨率范围内产生的不同分群，并用经典 Newman–Girvan 模块度给每种分群评分。默认覆盖全部非负分辨率。

使用 0.3.0 的区间并行功能时，在本地仓库根目录执行与你的平台相应的安装命令。以下二进制包适用于 64 位 x86 Windows 上的 R 4.6.x。[Windows 二进制包](../downloads/SUNLouvainPath_0.3.0.zip)

~~~r
install.packages(c("Matrix", "parallelly", "Rcpp", "SeuratObject"))
install.packages("downloads/SUNLouvainPath_0.3.0.zip", repos = NULL, type = "win.binary")
~~~

从源码安装需要 R ≥ 4.2 和 C++17 编译工具。[R 源码包](../downloads/SUNLouvainPath_0.3.0.tar.gz)

~~~r
install.packages(c("Matrix", "parallelly", "Rcpp", "SeuratObject", "BH"))
install.packages("downloads/SUNLouvainPath_0.3.0.tar.gz", repos = NULL, type = "source")
~~~

已发布的 v0.2.1 另提供适用于 Windows R 4.6.x 的二进制包。

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

### Set the range and number of workers · 指定搜索范围与核心数

MML（maximum modularity in Louvain）默认分为 `[0, 0.5)`、`[0.5, 1)`、`[1, 2)`、`[2, Inf)` 四个区间。每个区间都在相同的原始图和细胞顺序上独立枚举，左端点单独计算。相邻区间若给出相同的划分，结果表会把对应的连续区间合并。

~~~r
# Custom split points, two threads and a finite inclusive maximum
limited <- EnumerateLouvain(obj, "RNA_snn", k = 20,
                            split_points = c(0.25, 0.5, 1),
                            r_max = 1.5, workers = 2L)
limits <- SeuratObject::Tool(limited, slot = "SUNLouvainPath")$settings
limits[c("split_points", "r_max", "workers")]

# One thread, one interval covering all nonnegative resolutions
serial <- EnumerateLouvain(obj, "RNA_snn", k = 20,
                           split_points = numeric(0), workers = 1L)
~~~

用 `split_points` 传入分割点向量。需要精确指定有理端点时，可以写 `split_points = c("1/2", "108/95")` 或 `r_max = "108/95"`。用字符串输入科学记数法（如 `"1e-5"`）时，指数的绝对值上限为 10,000。仅位于 0 和上限之间的分割点用于划分任务。有限上限本身属于搜索范围，`r_max = 0` 只计算原点。仅在设置有限上限时，计算完成后会提示实际范围。经典模块度始终按评分分辨率 1 计算，全部并列最高分和推荐分辨率都针对实际搜索范围。

默认 `workers = NULL` 按可用核心数和区间数选择线程数，最多 4 个。手动传入正整数可指定并行线程数上限，`workers = 1L` 在当前线程执行。多个 C++ 线程共享只读原图，每个线程拥有独立的分群状态。`out$settings[c("split_points", "r_max", "workers")]` 记录实际使用的分割点、上限和线程数。

Use a positive integer for `workers` to limit concurrent interval searches. Threads share the graph and maintain their own Louvain state. Each input graph and search range yields the same membership columns, scored partitions and maximizing recommendations across thread counts. The automatic setting uses `parallelly::availableCores()`. The numeric thread-count control follows RcppParallel's `numThreads` convention. [parallelly available cores](https://parallelly.futureverse.org/reference/availableCores.html) · [RcppParallel thread options](https://search.r-project.org/CRAN/refmans/RcppParallel/html/setThreadOptions.html)

将示例中的 20 替换为建图时的近邻数。仅有图时也可用
`EnumerateLouvain(obj, graph = "RNA_snn")`。默认找与存储值相容的最小近邻数；找不到时，按图中双精度数的精确二进制值计算。实际采用的方式记录在 `out$settings`。指定 `k` 时会严格核验非对角权重。包忽略自相似对角线。子图以对象中的细胞顺序运行，图外细胞的标签为 `NA`。

推荐表的 `recommended_resolution` 为精确分数，`partition` 可直接索引分群表。若 `status == "open_infimum"`，最高分首次出现于开区间，因此最小值为 `NA`。`infimum` 给出下确界，`representative_resolution` 和 `representative_partition` 给出可实际取到的一个最高分解。多个并列最高分均保存在 `scores` 中。无非对角边时经典模块度无定义。

~~~r
best <- out$scores[out$scores$is_max %in% TRUE, , drop = FALSE]
id <- out$recommendation$representative_partition
if (!is.na(id)) out$partitions[, c("cell", id), drop = FALSE]
~~~

使用对象列顺序作为细胞顺序，正增益平局取较小的当前群编号，零增益保留原位。聚合后按群内最早的原始细胞排序，沿用原图加权度。这个规则精确定义了“全部输出”的范围；Seurat 默认的随机起点和单例后处理可能给出不同结果。结果直接存放于 `obj@tools[["SUNLouvainPath"]]`。

引擎分别运行临界点和符号右极限。每次访问一个节点时，先选出目标群，再以精确整数运算找出有其他候选群可能超过它的首个交点。取整次运行中这些交点的最小值，即可确定本次轨迹有效的开区间。默认搜索全部非负分辨率，当所有选择都没有未来交点时，最后一个区间延伸至无穷大。各区间的结果按分辨率顺序整合，跨区间重复出现的划分只占一列。该实现将 HESC 分析中的交点筛选推广到包支持的无向非负权图。

固定建图近邻数的 Jaccard 图满足关于细胞数的多项式时间论证。对于一般加权图，精确枚举仍然适用，但以整数化总边权计的上界可能很大。返回表仅描述这里定义的算法；推荐分辨率处的标签可直接从 `partitions` 取出。

0.2.0 的安装包在 SUN 论文的 GSE85066 HESC 原始 RNA_snn 上重现了先前独立计算的 975 种划分和 992 个连续区间。498 个细胞的逐细胞标签、每个区间的精确端点与开闭、全部经典模块度分数和最早推荐分辨率均已核对。另有不超过 10 个细胞的回归用例，涵盖并列最高、仅在一个精确端点出现的分群，以及最早区间左端开放的情形。设置表中的 `algorithm` 标识确定性规则，`package_version` 记录实际执行的软件版本。
