# HESC partitions scored under five criteria

**English** · [简体中文](methods.zh-CN.md)

MML v0.3.0 enumerates 975 distinct partitions of the same 498 HESC cells. Each column of the membership matrix assigns a cluster to every cell. Each criterion is maximized over the partitions that meet its scoring requirements. All maxima use the scores before display rounding. [All candidate scores](partition-scores.csv) · [Cell assignments of all winners](winning-memberships.csv)

## Each criterion measures a different property

- **ROGUE measures within-cluster expression purity.** Each of the 498 cells was matched to its sequencing run in SRP073808. For each gene and cell we used the recount3 default read-count estimate, which divides gene base coverage by the library’s average mapped length and rounds to the nearest integer. This yields 63,856 GENCODE v26 gene rows. We ran the authors’ ROGUE implementation with the full-length platform setting ($K=500$) and its default minimum of ten cells per cluster. All cells were pooled as a single sample. Our score for a partition is the cell-count-weighted mean of its cluster purities, with a finite score required for every cluster. 60 partitions received a score. As an input-scale sensitivity analysis, applying the same aggregation to the deposited TPM expression values selected P60 (20 clusters, 0.991770). The CSV records this separately as `rogue_TPM_sensitivity`. [Cell-to-run mapping](cell-runs.tsv) · [recount3 count transformation](https://research.libd.org/recount3/reference/compute_read_counts.html) · [ROGUE paper](https://doi.org/10.1038/s41467-020-16904-3)
- **SCCAF measures how accurately held-out cell labels can be predicted.** We used the authors’ `self_projection` function from SCCAF 0.0.10 and the Seurat RNA data layer (24,789 genes, log-normalized at a scale factor of 10,000 from the deposited expression abundances). We used L1 logistic regression with the default classifier settings and three stratified 50:50 train/test splits with seeds 1, 2 and 3. The score is mean test accuracy. Each cluster must occur in both halves of each split. All 73 eligible partitions were evaluated. P1 achieved 249 correct predictions out of 249 in each split. Its three groups contain all 51 H7hESC cells, all 55 LatM (lateral mesoderm) cells, and the 392 cells from the other seven reference classes, respectively. This measures how well the expression data predict the candidate partition’s own labels. [SCCAF paper](https://doi.org/10.1038/s41592-020-0825-9) · [Software](https://pypi.org/project/SCCAF/0.0.10/)
- **Silhouette measures separation in the graph-building space.** We computed the mean of the standard cell-level silhouette widths from Euclidean distances in the ten principal components used to build the original SNN, assigning zero width to singletons. The eligible domain is 2 through 497 clusters, covering 974 candidates. [Original PC coordinates](hesc-pca.csv) · [R implementation](https://stat.ethz.ch/R-manual/R-devel/library/cluster/html/silhouette.html) · [Rousseeuw, 1987](https://doi.org/10.1016/0377-0427%2887%2990125-7)
- **ARI measures agreement with the nine original labels.** We scored each partition against the nine reference classes using the adjusted Rand index. **Classical modularity** uses the original SNN and a common scoring resolution of 1. Both measures cover all 975 partitions. The R package stores exact modularity as a fraction. [Data source](https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE85066)

## Reproducing the results

From a checkout of this repository, run the commands below in `docs/hesc` after installing MML v0.3.0. The MML example supplies the ordered membership columns. The scripts use the original HESC expression data and PCA coordinates for the expression- and distance-based scores. The public inputs to ROGUE and SCCAF are checked against pinned checksums. [MML installation and ARI example](../../README.md) · [HESC expression object](https://github.com/BioinfoCenterSYSMH/SUN-Project/blob/fce0623bb02f3e6292a9421c0af23acfc6a0abc7/data/hesc_demo.rda)

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

The score CSV gives one row per partition. A blank score and its status identify a candidate outside that metric’s scoring domain. The three `sccaf_correct_seed*` columns give correct predictions out of 249 per split. `first_r_lower` is the exact lower endpoint of the partition’s first interval. `first_r_included` records whether the partition is attained at that endpoint.
