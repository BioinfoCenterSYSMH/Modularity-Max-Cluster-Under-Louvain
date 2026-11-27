# MML beta 1 · SUNLouvainPath 0.3.1.9001

[简体中文](#简体中文) · [English](#english)

## 简体中文

MML 枚举同一张 SNN 图上、仅改变分辨率时确定性 Louvain 可返回的全部划分，包括恰好只在一个端点出现的划分。研究者可以在这批候选上计算自己的评价指标。包内给出经典模块度、全部并列最高分以及最早取得最高分的分辨率。如果最早区间为左开，推荐表给出下确界和可实际取得的代表值。

此 beta 自动检测连通分量，按原细胞顺序和全图权重尺度独立计算各分量。它直接求出独立细胞对的分群和全单点末段。对于需要运行 Louvain 的部分，相邻分辨率复用经过精确比较确认的移动，端点有歧义时单独求解。单线程与多线程均使用同一套确定性规则。

在 R 中运行以下代码，可查询结果及程序为本图选择的计算路径。

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

默认区间由 0.5、1、2 分割，覆盖所有非负分辨率，最多使用四个可用核心。将 `workers = 1L` 与 `split_points = numeric(0)` 合用可执行单线程、单区间搜索；用 `r_max = "3/2"` 可包含精确上限 1.5。非对角边采用精确 Jaccard 或所存双精度值的精确有理表示。具体参数见 `?EnumerateLouvain`。包内置 10 细胞和 HESC 两套可离线核验的输入与参考结果。

```r
ten <- VerifyLouvainExample("ten_cells")
hesc <- VerifyLouvainExample("hesc")
```

王俊博、廖建友共同开发 MML，开发过程中使用 GPT-6.2 Astra 辅助。两位作者对报告的结果共同负责。论文正在写作中，引用前请联系作者。[王俊博](mailto:1124315977@qq.com) · [廖建友](mailto:liaojy3@mail.sysu.edu.cn)

## English

MML enumerates every distinct final partition returned by its deterministic Louvain rule as resolution varies over the requested range, including partitions confined to one exact endpoint. Researchers can score those partitions using their preferred metric. The package supplies classical modularity, all tied maxima and the earliest maximizing resolution. If only an open infimum exists, the recommendation includes an attainable representative.

This beta detects connected components, preserves the original cell order and graph-wide weight scale, and directly solves isolated cells, independent pairs and the all-singleton tail. For the remaining search it reuses certified moves across adjacent resolutions and evaluates ambiguous endpoints separately. The R interface and the four result tables are compatible with version 0.3.0.

Use the first example above on a Seurat object with an SNN graph. The default covers all nonnegative resolutions with splits at 0.5, 1 and 2 and uses up to four available cores. Use `workers = 1L, split_points = numeric(0)` for a serial, unsplit search, or set an inclusive exact maximum such as `r_max = "3/2"`. Query `out$settings$search_plan` for the chosen route, component sizes, edge count and the exact start of the singleton tail. The second example checks the two bundled datasets against independent references.

Junbo Wang and Jianyou Liao developed MML with assistance from GPT-6.2 Astra. Both authors take joint responsibility for the reported results. The manuscript is in preparation. Please contact the authors before citing. [Junbo Wang](mailto:1124315977@qq.com) · [Jianyou Liao](mailto:liaojy3@mail.sysu.edu.cn)
