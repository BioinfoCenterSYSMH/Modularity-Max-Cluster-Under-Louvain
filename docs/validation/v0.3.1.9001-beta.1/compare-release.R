# Run in fresh Rscript processes so each process loads exactly one native DLL.
# Rscript --vanilla compare-release.R <reference|beta> <installed-library> <result-dir>
args <- commandArgs(trailingOnly = TRUE)
stopifnot(length(args) == 3L, args[1L] %in% c("reference", "beta"))
mode <- args[1L]
lib <- normalizePath(args[2L], winslash = "/", mustWork = TRUE)
result_dir <- args[3L]
dir.create(result_dir, recursive = TRUE, showWarnings = FALSE)
.libPaths(c(lib, .libPaths()))
suppressPackageStartupMessages(library(SUNLouvainPath))
stopifnot(identical(normalizePath(find.package("SUNLouvainPath"), winslash = "/"),
                    normalizePath(file.path(lib, "SUNLouvainPath"), winslash = "/")))
version <- as.character(packageVersion("SUNLouvainPath"))
stopifnot(if (mode == "reference") version == "0.3.0" else package_version(version) > "0.3.0")

make_object <- function(graph, project) {
    cells <- rownames(graph)
    counts <- Matrix::sparseMatrix(i = rep(1L, length(cells)), j = seq_along(cells),
        x = rep(1, length(cells)), dims = c(1L, length(cells)),
        dimnames = list("placeholder", cells))
    obj <- SeuratObject::CreateSeuratObject(counts, project = project)
    obj[["RNA_snn"]] <- SeuratObject::as.Graph(graph)
    obj
}
fixture <- function(name) {
    input <- readRDS(system.file("extdata", paste0(name, "_graph.rds"),
                                 package = "SUNLouvainPath", mustWork = TRUE))
    n <- length(input$cells)
    w <- input$overlap / (2 * input$k - input$overlap)
    g <- Matrix::sparseMatrix(i = c(input$i, input$j, seq_len(n)),
        j = c(input$j, input$i, seq_len(n)), x = c(w, w, input$diagonal),
        dims = c(n, n), dimnames = list(input$cells, input$cells))
    list(obj = make_object(g, name), k = input$k)
}

result_fields <- c("partitions", "intervals", "scores", "recommendation")
records <- list()
compare <- function(name, obj, ..., check_fixture = NULL) {
    elapsed <- system.time(result <- suppressMessages(EnumerateLouvain(obj, ...)))[["elapsed"]]
    out <- SeuratObject::Tool(result, slot = "SUNLouvainPath")[result_fields]
    if (!is.null(check_fixture)) {
        ref <- readRDS(system.file("extdata", paste0(check_fixture, "_expected.rds"),
                                   package = "SUNLouvainPath", mustWork = TRUE))
        stopifnot(identical(as.matrix(out$partitions[-1L]), ref$labels),
                  identical(out$intervals, ref$intervals),
                  identical(out$scores[names(ref$scores)], ref$scores),
                  identical(out$recommendation[names(ref$recommendation)], ref$recommendation))
    }
    file <- file.path(result_dir, paste0(name, "-0.3.0.rds"))
    if (mode == "reference") {
        saveRDS(out, file)
    } else {
        ref <- readRDS(file)
        for (field in result_fields) if (!identical(out[[field]], ref[[field]])) {
            stop(sprintf("%s: %s differs from v0.3.0", name, field))
        }
    }
    records[[name]] <<- data.frame(case = name, version = version, cells = nrow(out$partitions),
        partitions = ncol(out$partitions) - 1L, intervals = nrow(out$intervals), seconds = elapsed)
    message(name, ": ", ncol(out$partitions) - 1L, " partitions, ", nrow(out$intervals),
            " intervals, ", elapsed, " seconds")
}

for (name in c("ten_cells", "hesc")) {
    input <- fixture(name)
    compare(paste0(name, "-serial"), input$obj, k = input$k, workers = 1L,
            split_points = numeric(), check_fixture = name)
    compare(paste0(name, "-four-workers"), input$obj, k = input$k, workers = 4L,
            check_fixture = name)
}

# Use stored weights exactly as supplied by R and interleave component vertex IDs.
# Include disconnected and connected graphs, edgeless graphs, isolated vertices,
# diverse degree distributions and cuts with more digits than fit in a double.
set.seed(13027)
for (case in seq_len(30L)) {
    n <- sample(2:10, 1L)
    cells <- paste0("C", seq_len(n))
    g <- matrix(0, n, n, dimnames = list(cells, cells))
    candidates <- upper.tri(g)
    if (case %% 2L) candidates <- candidates & outer(seq_len(n) %% 2L, seq_len(n) %% 2L, "==")
    g[candidates] <- sample(c(0, 0, 0.01, 0.1, 0.25, 1, 2.7), sum(candidates), replace = TRUE)
    g <- g + t(g)
    diag(g) <- 1
    obj <- make_object(Matrix::Matrix(g, sparse = TRUE), "stored")
    limit <- c("0", "11/10", "7", "Inf")[1L + case %% 4L]
    compare(sprintf("stored-%02d", case), obj, weights = "stored", workers = 3L,
            split_points = c("1/3", "1", "100000000000000000000000000000001/100000000000000000000000000000000", "4"),
            r_max = limit)
}
write.table(do.call(rbind, records), file.path(result_dir, paste0(mode, "-timing.tsv")),
            row.names = FALSE, quote = FALSE, sep = "\t")
