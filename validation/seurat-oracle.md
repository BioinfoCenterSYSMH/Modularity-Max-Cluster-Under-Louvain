# Seurat optimizer validation

The fixed-resolution reference in `seurat_oracle.py` uses Python integers and fractions. At each vertex it recalculates candidate groups, their members, their mass and their internal links from a dense matrix. It shares neither C++ source nor symbolic path tracing with MML. Its Java-compatible generator supplies vertex permutations and is carried through levels, iterations and random starts. Seurat 5.5's native optimizer supplies the separate double-precision comparison.

Run the following after installing the Windows or source package into an R library. Seurat 5.5.0 is required for this validation. Intermediate exports live in a temporary directory.

```powershell
python -B verify-seurat-oracle.py --library "D:/path/to/installed/R-library" --output .
```

Beta 4 passed 1,067 exact probes across 14 combinations of graph and controls. The runner checks optimizer labels in their original size-ranked order, the full final partition and endpoint inclusivity. Every reported interval is probed in its interior and at its endpoints, plus the unbounded tail where present. For five tiny graph/control combinations the probe set additionally includes intersections of the score lines for **all** set partitions and a point in every intervening interval. This independently covers possible movement and restart-score decisions for those fixtures. The remaining probes check lengths up to ten cells and include both modularity functions, both algorithms, refinement, disconnected graphs, ties and the all-singleton extension. Seurat's original R singleton routine provides the postprocessing reference where defined.

The two PBMC configurations use the seven-cell induced submatrix on the first seven sorted barcodes of `MML_pbmc_coverage/results/trials/001/audit.rds` (SHA-256 `158e80a2e0caaa46f6d7e99322f0511413709c5552c9fb5cd9c1acd171bfc255`). The exact weights are reconstructed from the deposited k=20 Jaccard overlaps. These are checks on a real small submatrix of the original 50-cell graph.

The seven-cell, four-start fixture isolates a switch between random-start winners at `r=13/14`. All recorded vertex visits and moves from every startup trajectory agree immediately before, exactly at and immediately after this value. The internal directed weights and squared cluster volumes are (26, 906) for the first three starts and (34, 1354) for the fourth. With total weighted degree 52, their objective lines cross at 52 × (34 − 26)/(1354 − 906) = 13/14. The fourth start wins on the left and the first start wins at equality and on the right.

Of 108 native-double queries, 103 exactly matched the reference optimizer's size-ranked labels. Three more matched its cell memberships after label permutation. Two produced genuinely different memberships. The smallest example has two cells, one dyadic edge of weight 49/64, and `r=2`. Its mathematically zero gain retains two singleton optimizer groups, while native Seurat merges the two cells. These counts describe this selected fixture set. See [all counts](seurat-oracle-results.tsv) and [every discrepancy](seurat-native-differences.tsv).
