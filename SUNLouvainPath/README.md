# MML Beta 4 · SUNLouvainPath 0.3.1.9004

[简体中文](#简体中文) · [English](#english)

## 简体中文

给定一张 Seurat SNN 图，MML 枚举只改变分辨率时确定性 Louvain 可以返回的划分。默认保留至多 101 群的所有方案。设置 `max_clusters = 50` 可只考察至多 50 群的方案；`max_clusters = Inf` 枚举所有群数。参数 `r_max` 单独限制分辨率，包括指定的有限右端点。两种限制均可由研究者设定。

```r
library(SUNLouvainPath)
obj <- EnumerateLouvain(obj, graph = "RNA_snn", k = 20, workers = 1L,
                        max_clusters = 101)
out <- SeuratObject::Tool(obj, slot = "SUNLouvainPath")
out$settings$max_clusters
out$settings$search_plan
out$partitions
out$intervals
out$scores
out$recommendation
```

`partitions` 给出保留的每种划分的细胞归属。`intervals` 列出产生这些划分的精确分辨率区间和端点，含仅在单个分辨率出现的方案。被排除的分辨率会在区间表中留下间隙。若所选范围内没有合格方案，细胞表仅保留细胞名，区间表和评分表均为零行，推荐状态为 `no_eligible_partition`。

经典模块度可用于给这些候选评分，`scores$is_max` 标记全部并列最优方案。若最早的最高分区间为左开，`recommendation` 给出下确界和一个实际可取的代表分辨率。评价其他性状时，可将任意指标应用于 `partitions` 中的同一批候选。

Simple 引擎根据输入边权与加权度计算可安全跳过的高分辨率段，并保留任何重新回到群数限制内的方案。`settings$r_max` 是用户选用的范围上限；`settings$search_plan` 记录扫描上界和端点是否包含。默认分割点为 0.5、1、2，使用最多四个可用核心。使用 `workers = 1L, split_points = numeric(0)` 可执行单线程、单区间搜索。非对角边采用精确 Jaccard 权重或所存双精度值的精确有理表示。更多参数见 `?EnumerateLouvain`。

```r
ten <- VerifyLouvainExample("ten_cells")
hesc <- VerifyLouvainExample("hesc")
```

验证函数在内部显式使用 `max_clusters = Inf`，逐项检查完整参考路径。内置 HESC 图有 498 个细胞，完整路径含 975 种划分、992 段区间。

### Seurat 5.5 精确引擎

```r
obj <- EnumerateLouvain(obj, graph = "RNA_snn", louvain_engine = "seurat",
    seurat.control = list(algorithm = 1L, modularity.fxn = 1L, n.start = 10L,
                          n.iter = 10L, random.seed = 0L, group.singletons = TRUE,
                          resolution = c("1/2", "4/5"), verbose = FALSE))
out <- SeuratObject::Tool(obj, slot = "SUNLouvainPath")
out$raw$intervals
out$queries
out$query_idents
```

- **总控和搜索范围。** `louvain_engine = "simple"` 为默认值。只读取所选引擎的具名列表 `simple.control` 或 `seurat.control`。其中的 `graph`、`k`、`weights`、`split_points`、`r_max`、`workers`、`max_clusters` 优先于同名顶层参数。Simple 上述安全剪枝及之前的 Lean 证明适用于原算法。Seurat 引擎按输入图的列顺序编号，精确追踪优化器的比较、端点和右极限，包括各次启动之间的得分交点。运行量依赖实际轨迹。
- **优化器。** `algorithm = 1`（也可写 `"louvain"`）是原始 Louvain；`2` 增加多层细化。`modularity.fxn = 1` 使用经典度数零模型的分辨率形式，范围为 `[0,r_max]`（无限上界为开端点）；`2` 使用单位节点权重，范围为 `[0,min(r_max,1)]`。记录请求上限 `settings$r_max` 与有效上限 `settings$effective_r_max`。`n.start = 10`、`n.iter = 10`、`random.seed = 0` 分别指定启动次数、每次启动的最大外层迭代数和 Java 随机数种子；得分并列时保留最早的启动。最终方案始终另按经典模块度评分。
- **单例。** `group.singletons = TRUE` 依次将单细胞群分配给平均 SNN 连接最强的非单例群。并列按 R 默认采样规则和种子 1 选择，保留调用者的随机数状态。全部为单例时，原生 TRUE 分支可能因缺少接收群而报错；MML 在这里保留各单例。设为 `FALSE` 会沿用 Seurat 5.5 串行语义，将所有单例标记为同一类 `singleton`。原生多 worker 分支在调用 `GroupSingletons` 时省略这个参数；MML 所有线程数均使用显式选定的设置。无非对角边的图，MML 定义其优化器输出为所有细胞各自成群，随后应用同一后处理。
- **查询与输出。** `resolution` 默认为 `0.8`，也可传入向量、精确分数字符串或用 `NULL` 关闭查询；连续路径始终按有效范围枚举。结果 `raw$partitions` 保存按簇大小排序的原始编号加一，`raw$intervals` 为原始路径。`partitions` 是经单例处理、按最终群数筛选、重新统一编号的结果。`queries` 按输入顺序标记 `ok`、`filtered_max_clusters`、`outside_r_max` 或 `outside_modularity_domain`。成功查询的 `query_idents` 保存原生风格的标签，失败查询对应列为 NA；超出群数上限的域内查询仍有原始方案编号。
- **接口映射。** `graph.name` 和 `graph` 指向同一图。`cluster.name` 为每个查询命名一列，`verbose` 控制运行反馈。返回值位于 `object@tools`，保留原有活动身份类别。`algorithm=3` 属于 SLM，`4` 属于 Leiden。请求这些算法、传入 Leiden 专用的 `initial.membership`、`node.sizes`、`leiden_method`、`leiden_objective_function` 或传入已弃用的 `method`，都会得到明确报错。`temp.file.location` 可接收路径，内存模式不使用该路径；`edge.file.name` 仅接收空字符串或 NULL。
- **精度差异。** 两个细胞共享唯一一条边，权重为 `49/64`。取 `r=2`、算法 1、模块度 1、一次启动和迭代、种子 0。精确移动增益为 0，优化器保留两个单例。原生双精度计算产生约 `1.11e-16` 的正增益，优化器合并两者。这一差异在输入本身可以精确表示时也会出现。[Seurat R 接口](https://github.com/satijalab/seurat/blob/v5.5.0/R/clustering.R) · [原始优化器](https://github.com/satijalab/seurat/blob/v5.5.0/src/ModularityOptimizer.cpp)

王俊博、廖建友共同开发 MML，开发过程中使用 GPT-6.2 Astra 辅助。两位作者对报告的结果共同负责。论文正在写作中，引用前请联系作者。[王俊博](mailto:1124315977@qq.com) · [廖建友](mailto:liaojy3@mail.sysu.edu.cn)

## English

On a fixed Seurat SNN graph, MML enumerates the partitions returned by deterministic Louvain as resolution varies. By default it returns all partitions with up to 101 clusters. Choose `max_clusters = 50` for studies targeting up to 50 clusters, or `max_clusters = Inf` to include every cluster count. The independent resolution limit `r_max` includes a user-supplied finite endpoint. The first example above shows a serial run and the result tables stored in the Seurat object.

`partitions` contains cell memberships for each retained partition. `intervals` reports the exact endpoints and boundary inclusion flags for the retained partitions, including single points. Excluded resolutions can leave gaps. If the requested domain has no eligible partition, the cell table contains only cell names, both the interval and score tables have zero rows, and the recommendation status is `no_eligible_partition`.

Classical modularity is an optional score. The `scores$is_max` flag identifies all tied maxima among retained candidates. When the first maximizing interval is open on its left, `recommendation` reports the infimum and an attainable representative resolution. Researchers can also apply another score directly to the memberships in `partitions`.

The Simple engine uses input edge weights and weighted degrees to certify a high-resolution tail that it can skip, and retains qualifying partitions even if they reappear after cluster count exceeds the cap. `settings$r_max` records the requested resolution limit. `settings$search_plan` describes the upper scan boundary and its inclusion flag. The default split points are 0.5, 1 and 2 and the default uses up to four available cores. Use `workers = 1L, split_points = numeric(0)` for a serial, unsplit search. Off-diagonal weights use exact Jaccard fractions or the exact rational representation of stored doubles. See `?EnumerateLouvain` for all arguments.

The second example above verifies both offline datasets. The verifier uses `max_clusters = Inf` internally to compare against the full reference paths. The 498-cell HESC graph has 975 distinct full-path partitions and 992 resolution segments.

### Seurat 5.5 exact engine

The Seurat example above runs algorithm 1 with ten starts, requests exact partitions at two resolutions and returns the complete continuous path.

- **Engine and domain.** `louvain_engine = "simple"` is the default. Only the selected named list, `simple.control` or `seurat.control`, is evaluated. Its `graph`, `k`, `weights`, `split_points`, `r_max`, `workers` and `max_clusters` override the corresponding top-level settings. The Simple certificate and the existing Lean proof concern the original algorithm. The Seurat engine numbers cells in graph column order and traces optimizer comparisons at exact points and their right limits, including crossings between restart score lines. Computational cost depends on the executed traces.
- **Optimizer.** `algorithm = 1` (also `"louvain"`) selects original Louvain and `2` adds multilevel refinement. `modularity.fxn = 1` uses degree weights over the requested domain. With `2`, node weights are one and the domain ends at `min(r_max, 1)`, inclusive. Inspect `settings$r_max` and `settings$effective_r_max` for the requested and effective limits. Defaults are `n.start = 10`, `n.iter = 10` (maximum outer iterations per start) and `random.seed = 0` (Java RNG). The earliest start wins equal scores. Final partitions are separately scored by classical modularity.
- **Singletons.** With `group.singletons = TRUE`, each singleton is assigned in turn to the nonsingleton group with the highest mean SNN weight, with R's default sampling rules and seed 1 for ties. MML preserves the caller's RNG state. With all cells singleton, native TRUE can fail for lack of a recipient; MML retains the separate cells. `FALSE` pools singletons under the label `singleton`, following Seurat 5.5's sequential branch. Its native multiworker branch omits this argument in the postprocessing call; MML honours the selected setting with any worker count. On a graph without off-diagonal edges, MML defines an all-singleton raw result and applies the selected postprocessing.
- **Queries and output.** `resolution` defaults to `0.8`; supply a vector or exact fraction strings for additional queries, or `NULL` for none. The effective continuous domain is always enumerated. `raw$partitions` stores the size-ordered raw optimizer IDs plus one and `raw$intervals` stores their path. `partitions` stores distinct, canonically numbered final assignments after postprocessing and the cluster cap. `queries` preserves input order and reports `ok`, `filtered_max_clusters`, `outside_r_max` or `outside_modularity_domain`. `query_idents` stores native-style factor labels for successful queries and NA for unavailable results. In-domain filtered queries retain a raw ID.
- **Argument mapping.** `graph.name` aliases `graph`; both must select the same input. `cluster.name` names query columns and `verbose` controls feedback. Results go into the object's tools slot, preserving its active identities. Algorithm 3 denotes SLM and 4 denotes Leiden. Requesting these, supplying Leiden's `initial.membership`, `node.sizes`, `leiden_method` or `leiden_objective_function`, or specifying deprecated `method` raises an error. `temp.file.location` accepts a path for compatibility and has no effect on in-memory computation. `edge.file.name` accepts only NULL or an empty string.
- **Arithmetic.** For two cells joined by a single edge of weight `49/64`, take resolution 2, algorithm 1, objective 1, one start and iteration, and seed 0. The exact move gain is zero and the optimizer returns two singletons. Native double arithmetic gives a positive gain of about `1.11e-16` and merges the cells despite the exactly representable inputs. [Seurat R interface](https://github.com/satijalab/seurat/blob/v5.5.0/R/clustering.R) · [Original optimizer](https://github.com/satijalab/seurat/blob/v5.5.0/src/ModularityOptimizer.cpp)

Junbo Wang and Jianyou Liao developed MML with assistance from GPT-6.2 Astra. Both authors take joint responsibility for the reported results. The manuscript is in preparation. Please contact the authors before citing. [Junbo Wang](mailto:1124315977@qq.com) · [Jianyou Liao](mailto:liaojy3@mail.sysu.edu.cn)
