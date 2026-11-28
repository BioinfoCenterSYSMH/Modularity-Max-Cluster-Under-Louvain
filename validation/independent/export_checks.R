args <- commandArgs(TRUE)
stopifnot(length(args) == 2L)
.libPaths(c(normalizePath(args[1L]), .libPaths()))
suppressPackageStartupMessages(library(Seurat))
suppressPackageStartupMessages(library(SUNLouvainPath))
stopifnot(packageVersion("SUNLouvainPath") == "0.3.1.9004")

graph_object <- function(n, edges) {
    cells <- sprintf("c%02d", seq_len(n))
    counts <- Matrix::sparseMatrix(i = rep(1L, n), j = seq_len(n), x = 1,
                                  dims = c(1L, n), dimnames = list("gene", cells))
    obj <- CreateSeuratObject(counts)
    i <- edges[, 1L]
    j <- edges[, 2L]
    weights <- edges[, 3L] / edges[, 4L]
    graph <- Matrix::sparseMatrix(i = c(i, j, seq_len(n)), j = c(j, i, seq_len(n)),
                                 x = c(weights, weights, rep(1, n)), dims = c(n, n),
                                 dimnames = list(cells, cells))
    obj[["RNA_snn"]] <- as.Graph(graph)
    obj
}

get_path <- function(obj, ...) SeuratObject::Tool(EnumerateLouvain(obj, ...), slot = "SUNLouvainPath")
cycle <- matrix(c(1, 2, 1, 3, 2, 3, 1, 3, 3, 4, 1, 3, 1, 4, 1, 3), ncol = 4L, byrow = TRUE)
star <- matrix(c(1, 2, 1, 1, 1, 3, 1, 8, 1, 4, 1, 8), ncol = 4L, byrow = TRUE)
refine <- matrix(c(1,2,3,4, 1,4,1,1, 1,5,1,1, 2,4,1,4, 2,5,1,1,
                   3,4,1,4, 3,5,1,2, 4,5,1,1), ncol = 4L, byrow = TRUE)
restart <- matrix(c(1,2,1,4, 2,3,1,4, 2,4,1,4), ncol = 4L, byrow = TRUE)
pair <- matrix(c(1,2,1,2), ncol = 4L)
cases <- list(
    list(name = "cycle_seed_0", n = 4L, edges = cycle, k = 2L, params = list(seed = 0L)),
    list(name = "cycle_seed_4", n = 4L, edges = cycle, k = 2L, params = list(seed = 4L)),
    list(name = "empty_stack", n = 4L, edges = star, params = list(n_start = 1L, n_iter = 1L)),
    list(name = "original", n = 5L, edges = refine, params = list(algorithm = 1L, n_start = 1L, n_iter = 1L)),
    list(name = "refined", n = 5L, edges = refine, params = list(algorithm = 2L, n_start = 1L, n_iter = 1L)),
    list(name = "iterated", n = 5L, edges = refine, params = list(algorithm = 1L, n_start = 1L, n_iter = 2L)),
    list(name = "restart_once", n = 5L, edges = restart, params = list(n_start = 1L, n_iter = 1L)),
    list(name = "restart_twice", n = 5L, edges = restart, params = list(n_start = 2L, n_iter = 1L)),
    list(name = "alternative_modularity", n = 2L, edges = pair, params = list(modularity = 2L))
)

cycle_object <- graph_object(4L, cycle)
simple <- get_path(cycle_object, k = 2L, max_clusters = Inf)
ignored <- get_path(cycle_object, k = 2L, max_clusters = Inf, louvain_engine = "simple",
                    seurat.control = stop("Inactive Seurat control was evaluated"))
stopifnot(identical(simple, ignored))

out <- lapply(seq_along(cases), function(i) {
    case <- cases[[i]]
    modularity <- case$params$modularity
    limit <- if (identical(modularity, 2L)) "1" else "Inf"
    settings <- case$params
    mapped <- c(algorithm = "algorithm", modularity = "modularity.fxn", n_start = "n.start",
                n_iter = "n.iter", seed = "random.seed")
    names(settings) <- unname(mapped[names(settings)])
    settings$group.singletons <- i %% 2L == 0L
    settings$resolution <- c("0", "1/2", "1")
    settings$verbose <- FALSE
    obj <- graph_object(case$n, case$edges)
    path <- get_path(obj, k = case$k, weights = if (is.null(case$k)) "stored" else "jaccard",
        workers = 1L, max_clusters = Inf, r_max = limit, louvain_engine = "seurat",
        simple.control = stop("Inactive Simple control was evaluated"), seurat.control = settings)
    stopifnot(identical(path$settings$louvain_engine, "seurat"))
    raw <- path$raw
    list(name = case$name, n = case$n, controls = case$params, r_max = limit,
         edges = lapply(seq_len(nrow(case$edges)), function(j) {
             edge <- case$edges[j, ]
             list(edge[1L] - 1L, edge[2L] - 1L, sprintf("%d/%d", edge[3L], edge[4L]))
         }), intervals = raw$intervals, partitions = as.list(raw$partitions[-1L]))
})
jsonlite::write_json(out, args[2L], auto_unbox = TRUE, pretty = TRUE)
cat(length(out), "exact paths exported and inactive settings isolated\n")
