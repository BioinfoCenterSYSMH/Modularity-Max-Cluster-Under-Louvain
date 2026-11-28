# Run with Beta 4 installed, passing the output TSV path as the sole argument.
suppressPackageStartupMessages(library(SUNLouvainPath))
stopifnot(as.character(packageVersion("SUNLouvainPath")) == "0.3.1.9004")
args <- commandArgs(trailingOnly = TRUE)
stopifnot(length(args) == 1L)
tool <- function(x) SeuratObject::Tool(x, slot = "SUNLouvainPath")

records <- list()
for (dataset in c("ten_cells", "hesc")) {
    object <- VerifyLouvainExample(dataset)
    full <- tool(object)
    stopifnot(full$settings$max_clusters == Inf)
    graph <- full$settings$graph
    args_run <- list(object = object, graph = graph, k = full$settings$k_used, workers = 2L)
    default <- tool(do.call(EnumerateLouvain, args_run))
    stopifnot(default$settings$max_clusters == 101)
    for (limit in c(100, 101)) {
        reduced <- tool(do.call(EnumerateLouvain, c(args_run, list(max_clusters = limit))))
        if (limit == 101) stopifnot(identical(reduced, default))
        selected <- full$scores$n_clusters <= limit
        expected_ids <- full$scores$partition[selected]
        keys <- setNames(reduced$scores$partition, expected_ids)
        expected <- full$intervals[full$intervals$n_clusters <= limit, , drop = FALSE]
        expected$partition <- unname(keys[expected$partition])
        rownames(expected) <- NULL
        stopifnot(
            reduced$settings$max_clusters == limit,
            identical(unname(as.matrix(reduced$partitions[-1L])),
                      unname(as.matrix(full$partitions[expected_ids]))),
            identical(reduced$partitions$cell, full$partitions$cell),
            identical(reduced$intervals, expected),
            identical(reduced$scores$modularity_exact, full$scores$modularity_exact[selected]),
            any(full$scores$is_max[selected]),
            identical(reduced$scores$is_max, full$scores$is_max[selected])
        )
        records[[length(records) + 1L]] <- data.frame(
            dataset = dataset, cells = nrow(reduced$partitions), max_clusters = limit,
            full_partitions = nrow(full$scores), retained_partitions = nrow(reduced$scores),
            retained_intervals = nrow(reduced$intervals), bound = reduced$settings$search_plan$cluster_bound)
    }
}
write.table(do.call(rbind, records), args[1L], sep = "\t", row.names = FALSE, quote = FALSE)
