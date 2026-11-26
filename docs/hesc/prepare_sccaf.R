# Rscript prepare_sccaf.R OUTPUT_DIRECTORY [PATH_TO_hesc_demo.rda]
# Input fixtures are supplied by MML's SUNLouvainPath 0.3.0 R package.
suppressPackageStartupMessages(library(SeuratObject))
suppressPackageStartupMessages(library(Matrix))
args <- commandArgs(trailingOnly = TRUE)
if (!length(args) || length(args) > 2L) {
    stop("Usage: Rscript prepare_sccaf.R OUTPUT_DIRECTORY [PATH_TO_hesc_demo.rda]")
}
stopifnot(as.character(packageVersion("SUNLouvainPath")) == "0.3.0")
fixture <- function(name) {
    readRDS(system.file("extdata", name, package = "SUNLouvainPath", mustWork = TRUE))
}
graph <- fixture("hesc_graph.rds")
expected <- fixture("hesc_expected.rds")
commit <- "fce0623bb02f3e6292a9421c0af23acfc6a0abc7"
checksum <- "e470105fc2a0a7540877fb1c1c47e364165a39100372abb23b5e1bf97827aee3"
if (length(args) == 2L) {
    demo_file <- args[2L]
} else {
    demo_file <- tempfile(fileext = ".rda")
    url <- sprintf("https://raw.githubusercontent.com/BioinfoCenterSYSMH/SUN-Project/%s/data/hesc_demo.rda", commit)
    download.file(url, demo_file, mode = "wb")
}
stopifnot(identical(digest::digest(file = demo_file, algo = "sha256"), checksum))
data_env <- new.env()
loaded <- load(demo_file, envir = data_env)
stopifnot("hesc_demo" %in% loaded)
counts <- LayerData(data_env$hesc_demo, assay = "RNA", layer = "counts")
cells <- graph$cells
labels <- expected$labels
stopifnot(inherits(counts, "dgCMatrix"), identical(dim(counts), c(24789L, 498L)),
          !anyDuplicated(cells), !anyDuplicated(colnames(counts)), setequal(cells, colnames(counts)),
          identical(rownames(labels), cells), identical(colnames(labels), paste0("P", seq_len(975L))))
counts <- counts[, cells, drop = FALSE]
total <- Matrix::colSums(counts)
stopifnot(all(is.finite(total)), all(total > 0), all(counts@x >= 0))
# Match Seurat LogNormalize at scale 10,000 on each cell's nonzero expression
# values. The sparse gene-by-cell CSC layout is the cell-by-gene CSR layout
# expected by score_sccaf.py.
norm <- counts
norm@x <- log1p((counts@x / rep.int(total, diff(counts@p))) * 10000)
out <- args[1L]
dir.create(out, recursive = TRUE, showWarnings = FALSE)
writeLines(cells, file.path(out, "cells.txt"))
writeLines(rownames(norm), file.path(out, "genes.txt"))
con <- gzfile(file.path(out, "logdata.csr.gz"), "wb", compression = 1L)
tryCatch({
    writeBin(as.integer(c(ncol(norm), nrow(norm), length(norm@x))), con, size = 4L, endian = "little")
    writeBin(norm@p, con, size = 4L, endian = "little")
    writeBin(norm@i, con, size = 4L, endian = "little")
    writeBin(norm@x, con, size = 8L, endian = "little")
}, finally = close(con))
con <- file(file.path(out, "membership.bin"), "wb")
tryCatch(writeBin(as.integer(labels), con, size = 4L, endian = "little"), finally = close(con))
message("Prepared 498 cells, 24,789 expression features and 975 MML partitions.")
