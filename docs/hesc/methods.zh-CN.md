# 五种评价指标给出了各自的 HESC 分群结果

[English](methods.md) · **简体中文**

MML v0.3.0 为同一批 498 个 HESC 细胞穷举出 975 种不同划分。成员矩阵的每一列给出一种划分下全部细胞的群标签。每种指标在各自的适用范围内取最大值，择优使用显示舍入前的得分。[全部划分的评分](partition-scores.csv) · [各项最高分方案的逐细胞群标签](winning-memberships.csv)

## 各个指标衡量不同的分群特征

- **ROGUE 衡量群内表达的均一性。** 我们将 498 个细胞逐一对应到 SRP073808 的测序记录，采用 recount3 默认的基因读数估计方法，将每个基因的碱基覆盖总量除以该文库的平均比对长度，再取整，得到含 63,856 个 GENCODE v26 基因行的矩阵。将全部细胞合为一个样本，使用原作者 ROGUE 实现的全长测序设置（$K=500$），每个群至少 10 个细胞。整套划分取各群纯度按细胞数加权的平均值，并要求每个群的得分均为有限值。共有 60 种划分获得评分。另以该研究公开的 TPM 表达量检验输入尺度的影响，同一汇总规则选出 P60（20 群，0.991770）。CSV 中的 `rogue_TPM_sensitivity` 单列这项对照。[细胞与测序记录的对应表](cell-runs.tsv) · [recount3 读数换算](https://research.libd.org/recount3/reference/compute_read_counts.html) · [ROGUE 原文](https://doi.org/10.1038/s41467-020-16904-3)
- **SCCAF 衡量留出细胞群标签的预测准确率。** 我们使用 SCCAF 0.0.10 原作者的 `self_projection` 函数，以及 Seurat 的 RNA 数据层（24,789 个基因，来自公开表达量，按 10,000 缩放后取对数）。按默认分类器设置运行 L1 逻辑回归，以 1、2、3 为随机种子，将细胞按群分层，三次各取一半训练、一半测试，取三次测试准确率的平均值。每个群在每次训练集和测试集中都要有代表，73 种划分满足条件。P1 每次都正确预测了全部 249 个测试细胞。它的三群分别是 51 个 H7hESC 细胞、55 个 LatM（侧中胚层）细胞，以及其余 7 类注释合在一起的 392 个细胞。这个指标衡量的是表达数据对候选分群自身标签的预测能力。[SCCAF 原文](https://doi.org/10.1038/s41592-020-0825-9) · [软件版本](https://pypi.org/project/SCCAF/0.0.10/)
- **Silhouette 衡量原建图空间中的群间分离程度。** 取原 SNN 建图使用的前 10 个主成分，以欧氏距离计算每个细胞的标准轮廓宽度，对全部细胞求平均。单细胞群的轮廓宽度按定义取零。适用范围为 2 至 497 群，共 974 种划分。[原始主成分坐标](hesc-pca.csv) · [R 实现](https://stat.ethz.ch/R-manual/R-devel/library/cluster/html/silhouette.html) · [Rousseeuw，1987](https://doi.org/10.1016/0377-0427%2887%2990125-7)
- **ARI 衡量与已有 9 类注释的吻合度。** 将每种划分与原始参考类别比较，计算调整兰德指数。**经典模块度**在原 SNN 图上统一按评分分辨率 1 计算。两者均覆盖全部 975 种划分。R 包以分数形式保存精确的经典模块度。[数据来源](https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE85066)

## 复现评分的步骤

安装 MML v0.3.0，下载本仓库，在 `docs/hesc` 目录运行以下命令。MML 示例提供按固定细胞顺序排列的完整候选标签。脚本使用真实 HESC 表达数据和主成分坐标计算表达与距离指标，并核对 ROGUE 和 SCCAF 公开输入文件的校验和。[MML 安装与 ARI 示例](../../README.zh-CN.md) · [HESC 表达对象](https://github.com/BioinfoCenterSYSMH/SUN-Project/blob/fce0623bb02f3e6292a9421c0af23acfc6a0abc7/data/hesc_demo.rda)

```r
install.packages(c("cluster", "data.table", "digest", "dplyr", "R.utils", "remotes", "tibble"))
remotes::install_github("PaulingLiu/ROGUE@6e1c8f9ee419c8c323ce9816841f78545dc17bf9")
```

```sh
Rscript prepare_rogue.R rogue_input cell-runs.tsv
Rscript score_rogue.R rogue_input/hesc_recount3_read_estimates.rds rogue_scores.csv

Rscript prepare_sccaf.R sccaf_input
python -m pip install numpy==1.26.4 scipy==1.14.0 scikit-learn==1.4.2
python -m pip download --no-deps --dest deps SCCAF==0.0.10
python score_sccaf.py --data sccaf_input --deps deps --workers 2

Rscript score_silhouette.R hesc-pca.csv silhouette_scores.csv
```

评分 CSV 每行是一种划分。得分留空时，状态列记录该指标的适用条件。`sccaf_correct_seed*` 三列分别记录每次 249 个测试细胞中预测正确的数量。`first_r_lower` 是该划分首次出现区间的精确下端点，`first_r_included` 标记在该端点能否取得该划分。
