# Rscript score_silhouette.R PATH_TO_hesc-pca.csv OUTPUT_CSV
# Uses stored PC1–10 from the original RNA_snn preprocessing and MML v0.3.0 fixtures.
args <- commandArgs(trailingOnly = TRUE)
if (length(args) != 2L) stop("Usage: Rscript score_silhouette.R PATH_TO_hesc-pca.csv OUTPUT_CSV")
stopifnot(as.character(packageVersion("SUNLouvainPath")) == "0.3.0")
fixture <- function(name) {
    readRDS(system.file("extdata", name, package = "SUNLouvainPath", mustWork = TRUE))
}
graph <- fixture("hesc_graph.rds")
labels <- fixture("hesc_expected.rds")$labels
pca <- read.csv(args[1L], check.names = FALSE, stringsAsFactors = FALSE)
dims <- paste0("PC_", seq_len(10L))
stopifnot(identical(names(pca), c("cell", dims)), !anyNA(pca$cell), !anyDuplicated(pca$cell),
          identical(rownames(labels), graph$cells), setequal(pca$cell, graph$cells),
          identical(dim(labels), c(498L, 975L)))
coords <- as.matrix(pca[match(graph$cells, pca$cell), dims])
stopifnot(is.numeric(coords), all(is.finite(coords)))
distance <- dist(coords, method = "euclidean")
n_clusters <- apply(labels, 2L, function(g) length(unique(g)))
eligible <- n_clusters >= 2L & n_clusters < nrow(labels)
scores <- rep(NA_real_, ncol(labels))
for (i in which(eligible)) {
    widths <- cluster::silhouette(labels[, i], distance)[, "sil_width"]
    stopifnot(length(widths) == nrow(labels), all(is.finite(widths)))
    scores[i] <- mean(widths)
}
result <- data.frame(partition = colnames(labels), n_clusters = unname(n_clusters),
                     mean_silhouette_width = scores,
                     status = ifelse(eligible, "evaluated", "undefined_all_singletons"))
options(digits = 17)
write.csv(result, args[2L], row.names = FALSE, na = "")
print(result[which(scores == max(scores, na.rm = TRUE)), ])
