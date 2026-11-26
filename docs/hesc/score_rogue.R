# Rscript score_rogue.R READ_COUNT_ESTIMATES.rds OUTPUT.csv
suppressPackageStartupMessages({
    library(Matrix)
    library(tibble)
    library(dplyr)
    library(ROGUE)
})
args <- commandArgs(trailingOnly = TRUE)
stopifnot(length(args) == 2L, as.character(packageVersion("SUNLouvainPath")) == "0.3.0")
counts <- readRDS(args[1])
fixture <- system.file("extdata", "hesc_expected.rds", package = "SUNLouvainPath", mustWork = TRUE)
labels <- readRDS(fixture)$labels
stopifnot(identical(colnames(counts), rownames(labels)), identical(dim(labels), c(498L, 975L)),
          all(counts@x >= 0), all(is.finite(counts@x)))

# A cluster's score depends only on its member cells, so identical sets share a fit.
cache <- new.env(hash = TRUE, parent = emptyenv())
cluster_score <- function(ix) {
    key <- paste(ix, collapse = ",")
    if (!exists(key, cache, inherits = FALSE)) {
        value <- tryCatch({
            fit <- ROGUE::rogue(counts[, ix, drop = FALSE], rep("cluster", length(ix)),
                                rep("pooled", length(ix)), platform = "full-length", min.cell.n = 10)
            as.numeric(fit[1, 1])
        }, error = function(e) {
            message("ROGUE fit for ", length(ix), " cells: ", conditionMessage(e))
            NA_real_
        })
        assign(key, value, envir = cache)
    }
    get(key, envir = cache, inherits = FALSE)
}

evaluate <- function(i) {
    groups <- unname(split(seq_len(nrow(labels)), labels[, i]))
    sizes <- lengths(groups)
    status <- "cluster_below_10"
    score <- NA_real_
    if (all(sizes >= 10L)) {
        purity <- vapply(groups, cluster_score, numeric(1))
        if (all(is.finite(purity))) {
            score <- weighted.mean(purity, sizes)
            status <- "ok"
        } else {
            status <- "undefined_fit"
        }
    }
    data.frame(partition = colnames(labels)[i], n_clusters = length(groups),
               min_cluster_size = min(sizes), score = score, status = status)
}
scores <- do.call(rbind, lapply(seq_len(ncol(labels)), evaluate))
write.csv(scores, args[2], row.names = FALSE, na = "")
print(scores[which(scores$score == max(scores$score, na.rm = TRUE)), ])
