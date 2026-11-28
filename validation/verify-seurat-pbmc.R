# Compare the full raw optimizer path on PBMC trial 001 with the stored
# Seurat 5.5 fixed-r results. Supply audit.rds and the output TSV path.
args <- commandArgs(trailingOnly = TRUE)
stopifnot(length(args) == 2L, packageVersion("SUNLouvainPath") == "0.3.1.9004")
data <- readRDS(args[1L])
edges <- data$edges
n <- length(data$cells)
values <- unique(edges$x)
weights <- list(n = n, i = edges$i, j = edges$j, type = match(edges$x, values),
                values = values, overlap = edges$overlap[match(values, edges$x)], k = 20L)
stopifnot(n == 50L, identical(as.integer(data$grid_numerators), 0:500),
          all(values == weights$overlap / (40 - weights$overlap)))

scan <- getFromNamespace("seurat_path_cpp", "SUNLouvainPath")
finalize <- getFromNamespace("seurat_results_cpp", "SUNLouvainPath")
started <- proc.time()[["elapsed"]]
path <- do.call(scan, c(weights, list(split_points = paste0(1:49, "/10"), r_max = "5",
               workers = 4L, algorithm = 1L, modularity_fxn = 1L, n_start = 10L,
               n_iter = 10L, random_seed = 0L)))
elapsed <- proc.time()[["elapsed"]] - started
queries <- do.call(finalize, c(weights, list(raw = path$membership, intervals = path$intervals,
                   group_singletons = FALSE, cap = 0L, points = paste0(0:500, "/100"),
                   r_max = "5", fxn = 1L, sample_tie = function(...) stop("Unexpected tie"))))$queries
# Named singleton postprocessing is a separate layer. Compare the raw
# optimizer labels selected at each exact rational query instead.
stopifnot(all(queries$status == "ok"))
canonical <- function(x) match(x, unique(x))
matched <- vapply(seq_along(data$seurat), function(q) {
    identical(canonical(path$membership[, queries$raw_partition[q]]), canonical(data$seurat[[q]]))
}, logical(1))
keys <- apply(path$membership, 2L, function(x) paste(canonical(x), collapse = ","))
result <- data.frame(trial = "001", cells = n, edges = nrow(edges), r_max = 5L,
                     native_queries = length(matched), native_matches = sum(matched),
                     ordered_optimizers = ncol(path$membership),
                     optimizer_partitions = length(unique(keys)), ordered_intervals = nrow(path$intervals),
                     exact_point_runs = path$search_plan$exact_point_runs,
                     right_limit_runs = path$search_plan$right_limit_runs, elapsed_seconds = elapsed)
print(result, row.names = FALSE)
write.table(result, args[2L], sep = "\t", quote = FALSE, row.names = FALSE)
stopifnot(all(matched))
