validate_control_names <- function(x) {
    if (!is.list(x) || is.data.frame(x) || is.object(x) ||
        (length(x) && (is.null(names(x)) || anyNA(names(x)) || any(!nzchar(names(x))) ||
                       anyDuplicated(names(x))))) {
        stop("The selected engine control must be a list with unique, nonempty names.", call. = FALSE)
    }
}

seurat_controls <- function(input) {
    defaults <- list(algorithm = 1L, modularity.fxn = 1L, n.start = 10L, n.iter = 10L,
                     random.seed = 0L, group.singletons = TRUE, resolution = 0.8,
                     graph.name = NULL, cluster.name = NULL, verbose = TRUE,
                     initial.membership = NULL, node.sizes = NULL, leiden_method = NULL,
                     leiden_objective_function = NULL, method = NULL,
                     temp.file.location = NULL, edge.file.name = NULL)
    unknown <- setdiff(names(input), names(defaults))
    if (length(unknown)) stop("Unknown Seurat control: ", paste(unknown, collapse = ", "), call. = FALSE)
    x <- defaults
    x[names(input)] <- input
    integer_setting <- function(value, name, lower) {
        if (!typeof(value) %in% c("integer", "double") || length(value) != 1L ||
            is.object(value) || !is.null(dim(value)) || !is.finite(value) ||
            value != floor(value) || value < lower || value > .Machine$integer.max) {
            stop("Invalid integer value for ", name, ".", call. = FALSE)
        }
        as.integer(value)
    }
    if (is.character(x$algorithm) && length(x$algorithm) == 1L && !is.na(x$algorithm)) {
        if (tolower(x$algorithm) == "louvain") x$algorithm <- 1L
        else if (tolower(x$algorithm) == "leiden") x$algorithm <- 4L
    }
    x$algorithm <- integer_setting(x$algorithm, "algorithm", 1)
    if (!x$algorithm %in% 1:2) {
        stop("Select Louvain algorithm 1 or 2. Seurat algorithm 3 is SLM and 4 is Leiden.", call. = FALSE)
    }
    x$modularity.fxn <- integer_setting(x$modularity.fxn, "modularity.fxn", 1)
    if (!x$modularity.fxn %in% 1:2) stop("modularity.fxn must be 1 or 2.", call. = FALSE)
    for (field in c("n.start", "n.iter")) x[[field]] <- integer_setting(x[[field]], field, 1)
    x$random.seed <- integer_setting(x$random.seed, "random.seed", -.Machine$integer.max)
    for (field in c("group.singletons", "verbose")) {
        if (!identical(x[[field]], TRUE) && !identical(x[[field]], FALSE))
            stop(field, " must be TRUE or FALSE.", call. = FALSE)
    }
    leiden <- c("initial.membership", "node.sizes", "leiden_method", "leiden_objective_function")
    supplied <- leiden[!vapply(x[leiden], is.null, logical(1))]
    if (length(supplied)) stop("Leiden-only controls: ", paste(supplied, collapse = ", "), call. = FALSE)
    if (!is.null(x$method)) stop("method is deprecated. Select algorithm 1 or 2.", call. = FALSE)
    if (!is.null(x$edge.file.name) && !identical(x$edge.file.name, ""))
        stop("MML enumerates the supplied SNN. edge.file.name must be NULL or empty.", call. = FALSE)
    if (!is.null(x$temp.file.location) && (!is.character(x$temp.file.location) ||
        length(x$temp.file.location) != 1L || is.na(x$temp.file.location)))
        stop("temp.file.location must be NULL or a path.", call. = FALSE)
    x$resolution <- if (is.null(x$resolution)) character() else resolution_text(x$resolution, "resolution")
    # Reuse the exact parser to reject nonfinite/malformed query strings up front.
    resolution_ranges_cpp(x$resolution, "Inf")
    if (!is.null(x$cluster.name) && (!is.character(x$cluster.name) || anyNA(x$cluster.name) ||
        any(!nzchar(x$cluster.name)) || length(x$cluster.name) != length(x$resolution))) {
        stop("Supply one nonempty cluster.name per queried resolution.", call. = FALSE)
    }
    x
}

seurat_enumeration <- function(vertices, cells, edges, values, encoding, ranges, requested,
                               workers, cap, control, graph) {
    n <- length(vertices)
    types <- match(edges$x, values)
    raw <- seurat_path_cpp(n, edges$i, edges$j, types, values, encoding$overlap, encoding$k,
                           ranges$split_points, ranges$r_max, workers, control$algorithm,
                           control$modularity.fxn, control$n.start, control$n.iter, control$random.seed)
    # Seurat resets its seed before sampling recipients. Restore the caller's RNG and
    # pin R 4's default sampling algorithm; the C++ caller memoises draws by tie size.
    choose_recipient <- function(size) {
        withr::with_seed(1L, sample.int(size, 1L), .rng_kind = "Mersenne-Twister",
                         .rng_normal_kind = "Inversion", .rng_sample_kind = "Rejection")
    }
    path <- seurat_results_cpp(n, edges$i, edges$j, types, values, encoding$overlap, encoding$k,
                               raw$membership, raw$intervals, control$group.singletons, cap,
                               control$resolution, requested, control$modularity.fxn, choose_recipient)
    raw_ids <- paste0("Raw", seq_len(ncol(raw$membership)))
    colnames(raw$membership) <- raw_ids
    row_index <- match(cells, vertices)
    raw_table <- data.frame(cell = cells, raw$membership[row_index, , drop = FALSE],
                            row.names = cells, check.names = FALSE)
    raw$intervals$n_clusters <- apply(raw$membership, 2L, max)[raw$intervals$partition]
    raw$intervals$partition <- raw_ids[raw$intervals$partition]
    path$raw <- list(partitions = raw_table, intervals = raw$intervals)
    path$search_plan <- raw$search_plan
    queries <- path$queries
    queries$raw_partition <- raw_ids[queries$raw_partition]
    output_ids <- if (ncol(path$membership)) paste0("P", seq_len(ncol(path$membership))) else character()
    queries$partition <- output_ids[queries$partition]
    headers <- control$cluster.name
    if (is.null(headers)) headers <- if (nrow(queries)) paste0(graph, "_res.", control$resolution) else character()
    queries$cluster_name <- make.unique(c("cell", headers))[-1L]
    columns <- list(cell = cells)
    for (q in seq_len(nrow(queries))) {
        labels <- path$query_idents[row_index, q]
        levels <- sort(unique(labels[!is.na(labels)]))
        names <- as.character(levels)
        names[levels == n] <- "singleton"
        columns[[queries$cluster_name[q]]] <- factor(labels, levels = levels, labels = names)
    }
    path$queries <- queries
    path$query_idents <- as.data.frame(columns, row.names = cells, check.names = FALSE,
                                       stringsAsFactors = FALSE)
    if (control$verbose) message("Seurat Louvain ", control$algorithm, ": ", ncol(raw$membership),
                                 " optimizer labelings, ", ncol(path$membership), " eligible partitions.")
    path
}
