# MML Beta 4 · 精确枚举 Seurat 图上的 Louvain 分群

[English](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/README.md)

给定一张共享近邻图（SNN），MML 枚举只改变分辨率时 Louvain 可以返回的细胞划分。Beta 4 新增 Seurat 5.5 Louvain 引擎，以精确算术追踪分群决策，以及多次随机启动中最优结果发生切换的分辨率。每个保留的方案都附有精确的分辨率区间，包括仅在一个端点出现的方案。经典模块度是内置的可选评分，研究者也可以用其他指标评价同一批分群。

## 安装 0.3.1.9004

在 Windows 的 64 位 R 4.6.x 中运行以下代码。其他平台可使用源码包，除下列依赖外还需 C++17 工具链和 R 包 `BH`。[Windows 安装包](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9004-beta.4/SUNLouvainPath_0.3.1.9004.zip) · [跨平台源码包](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9004-beta.4/SUNLouvainPath_0.3.1.9004.tar.gz) · [SHA256 校验值](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9004-beta.4/SHA256SUMS)

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

## 在 Seurat 对象上枚举并查询分辨率

假设 Seurat 对象 `obj` 已含有 `RNA_snn`。下例枚举整个闭区间 `[0,1]`，并查询两个精确分数。结果中，`queries` 给出各查询的状态，`query_idents` 给出最终标签，`raw$partitions` 给出单细胞群处理前的优化器分群。

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

- **Simple 引擎。** 直接调用 `EnumerateLouvain(obj, graph = "RNA_snn")`，默认采用 `louvain_engine = "simple"`、`max_clusters = 101` 和 `r_max = Inf`。将 `max_clusters` 设为 `Inf` 可枚举所有群数。指定有限群数上限时，引擎能依据图本身安全地跳过高分辨率区间。单线程运行可设 `workers = 1L`。
- **Seurat 引擎。** `algorithm = 1L` 选择原始 Louvain，`2L` 加入多层细化。`random.seed`、`n.start` 和 `n.iter` 分别指定种子、启动次数和每次启动的迭代上限。目标函数 1 扫描用户所选范围，`modularity.fxn = 2L` 的分辨率最高为 1。群数上限按单细胞群处理后的最终划分判断。若所有群均只有一个细胞，MML 在 `group.singletons = TRUE` 时保留各单细胞群。该引擎支持上述两种 Louvain 算法，SLM 和 Leiden 属于其他算法。[全部参数、输出字段及原生实现对照](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/SUNLouvainPath/README.md#简体中文)

## 验证和形式证明

- **HESC。** 498 个细胞的 Simple 路径在默认上限下保留 303 种划分，分布在 312 个区间。解除群数上限后得到 975 种划分。所有保留方案的细胞归属、精确模块度及区间端点均与完整路径吻合。[HESC 验证记录](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/validation/cluster-limits.tsv)
- **Seurat 5.5。** 在 14 组图和参数组合中，新引擎在 1,067 个精确查询点上与独立参考实现一致。另在 50 细胞 PBMC 图上，分辨率从 0 到 5 的 501 个对照点全部与原生 Seurat 的细胞归属一致。针对临界点的小图测试中，108 次原生双精度查询有 2 次因浮点舍入产生不同的细胞归属。[独立精确验证](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/validation/seurat-oracle.md) · [PBMC 记录](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/validation/seurat-pbmc-results.tsv) · [原生差异明细](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/blob/v0.3.1.9004-beta.4/validation/seurat-native-differences.tsv)
- **Lean 4。** 对固定 Jaccard SNN 图上的原始确定性 Simple 模型，形式证明确认了枚举结果恰好覆盖所有非负实数分辨率下可达的分群，包括仅在端点出现的结果。固定近邻数时，形式化的稠密图枚举与评分算法对 `n` 个细胞的算术操作数上界为 `O(n^14)`。新增 Seurat 引擎的验证见上面的独立对照。[Lean 证明包](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/releases/download/v0.3.1.9004-beta.4/Louvain_Lean_proof.zip)

另一项独立验收从 Windows 安装包运行，在五张小图、九组配置上采用单线程，放开群数上限，核对单例处理前的细胞归属。3,485 个精确查询均恰好落入一个输出区间，细胞归属均与独立求解器一致。[验收结果与参考程序](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/tree/v0.3.1.9004-beta.4/validation/independent)

## 作者

王俊博、廖建友共同开发 MML，开发过程中使用 GPT-6.2 Astra 辅助。两位作者对报告的结果共同负责。论文正在写作中，引用前请联系作者。[王俊博 · 1124315977@qq.com](mailto:1124315977@qq.com) · [廖建友 · liaojy3@mail.sysu.edu.cn](mailto:liaojy3@mail.sysu.edu.cn)
