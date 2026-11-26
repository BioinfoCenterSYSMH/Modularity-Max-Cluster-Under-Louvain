# Rscript prepare_rogue.R OUTPUT_DIRECTORY CELL_TO_SRR.tsv
suppressPackageStartupMessages(library(Matrix))
suppressPackageStartupMessages(library(data.table))
args <- commandArgs(trailingOnly = TRUE)
stopifnot(length(args) == 2L, as.character(packageVersion("SUNLouvainPath")) == "0.3.0")
dir.create(args[1], showWarnings = FALSE, recursive = TRUE)
folder <- normalizePath(args[1])
filemap <- fread(args[2])
fixture <- system.file("extdata", "hesc_graph.rds", package = "SUNLouvainPath", mustWork = TRUE)
cells <- readRDS(fixture)$cells

base <- "https://recount-opendata.s3.amazonaws.com/recount3/release/human"
paths <- c("data_sources/sra/gene_sums/08/SRP073808/sra.gene_sums.SRP073808.G026.gz",
           "data_sources/sra/metadata/08/SRP073808/sra.recount_qc.SRP073808.MD.gz",
           "annotations/gene_sums/human.gene_sums.G026.gtf.gz")
hashes <- c("f8893c6874dc94b17984fdc42d32ab083bd8072bdab80d64f54fcac7548cab9a",
            "698fd7cdebd593edebf25b36d26144c186caa302b7ba11c8e794f80caf49bcab",
            "2d1bdff8d91e08f1291fd47850d9d61cfa6768cc3a4cb8516775a873b007d0f6")
options(timeout = max(600L, getOption("timeout")))
for (i in seq_along(paths)) {
    target <- file.path(folder, basename(paths[i]))
    if (!file.exists(target)) {
        tmp <- tempfile(tmpdir = folder)
        download.file(paste0(base, "/", paths[i]), tmp, mode = "wb")
        stopifnot(digest::digest(tmp, algo = "sha256", file = TRUE) == hashes[i],
                  file.rename(tmp, target))
    }
    stopifnot(digest::digest(target, algo = "sha256", file = TRUE) == hashes[i])
}
stopifnot(identical(cells,filemap$cell),length(cells)==498L,!anyDuplicated(cells),
          !anyDuplicated(filemap$run_accession))
runs <- filemap$run_accession
gz <- function(name) file.path(folder,name)
qc <- fread(gz("sra.recount_qc.SRP073808.MD.gz"))
qc <- qc[match(runs,external_id)]
stopifnot(identical(qc$external_id,runs),all(is.finite(qc$star.average_mapped_length)),
          all(qc$star.average_mapped_length>0))
# GENCODE v26 uses a stable versioned gene_id and can repeat a display symbol across loci.
ann <- readLines(gzfile(gz("human.gene_sums.G026.gtf.gz")))
dat <- strsplit(ann[!startsWith(ann,"#")],"\t",fixed=TRUE)
f <- vapply(dat, function(row) row[[9L]], "")
attr <- function(key) sub(paste0('.*',key,' "([^"]+)".*'),"\\1",f)
id <- attr("gene_id")
symbol <- attr("gene_name")
stopifnot(!anyDuplicated(id), !anyNA(symbol), !any(symbol==""), all(startsWith(id, "ENSG")))
rows <- data.table(gene_id=id,gene_name=symbol)
gene <- fread(gz("sra.gene_sums.SRP073808.G026.gz"),skip=2,select=c("gene_id",runs),nThread=2)
stopifnot(!anyDuplicated(gene$gene_id), all(gene$gene_id %in% rows$gene_id),
          identical(names(gene)[-1L],runs))
# Exact same rounding and divisor as upstream; columnwise to reduce peak RAM.
matrix_for_rogue <- do.call(cbind,lapply(seq_along(runs),function(j) {
    Matrix(round(gene[[j+1L]]/qc$star.average_mapped_length[j],0),ncol=1,sparse=TRUE)
}))
matrix_for_rogue <- as(matrix_for_rogue, "dgCMatrix")
rows <- rows[match(gene$gene_id,gene_id)]
duplicate_symbol <- duplicated(rows$gene_name) | duplicated(rows$gene_name,fromLast=TRUE)
rows$feature <- ifelse(duplicate_symbol,paste0(rows$gene_name,"|",rows$gene_id), rows$gene_name)
stopifnot(!anyDuplicated(rows$feature),identical(rows$gene_id,gene$gene_id))
dimnames(matrix_for_rogue) <- list(rows$feature,cells)
stopifnot(all(matrix_for_rogue@x>=0L), all(matrix_for_rogue@x == round(matrix_for_rogue@x)),
          all(colSums(matrix_for_rogue)>0L), identical(colnames(matrix_for_rogue),cells))
saveRDS(matrix_for_rogue, gz("hesc_recount3_read_estimates.rds"))
cat("Saved gene read-count estimates for", nrow(matrix_for_rogue), "genes and",
    ncol(matrix_for_rogue), "cells.\n")
