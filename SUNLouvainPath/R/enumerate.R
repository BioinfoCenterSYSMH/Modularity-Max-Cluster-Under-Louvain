# Identify an exact Jaccard encoding by comparing the correctly rounded doubles.
# A pruned graph or a subset may admit several k values; report the one used.
decode_weights <- function(values, k, mode, n) {
    if (!is.null(k)) {
        if (!is.numeric(k) || length(k) != 1L || !is.finite(k) ||
            k < 1 || k > .Machine$integer.max || k != floor(k)) {
            stop("k must be a positive integer.")
        }
        if (mode == "stored") stop("Use k with Jaccard weights, or omit k for stored weights.")
    }
    if (mode != "stored" && all(values <= 1)) {
        candidates <- if (is.null(k)) seq_len(n) else as.integer(k)
        for (candidate in candidates) {
            overlap <- round(2 * candidate * values / (1 + values))
            if (all(overlap / (2 * candidate - overlap) == values)) {
                return(list(k = candidate, overlap = overlap))
            }
        }
    }
    if (!is.null(k) || mode == "jaccard") {
        stop("Off-diagonal weights do not match the requested Jaccard encoding. ",
             "Supply the construction k, or use weights = 'stored' without k.")
    }
    list(k = 0L, overlap = numeric())
}

# Character inputs retain exact user-supplied fractions. Numeric inputs use
# the fewest significant decimal digits that round-trip to the supplied R value.
resolution_text <- function(x, name) {
    if (is.null(x) && identical(name, "split_points")) return(character())
    if (!is.null(dim(x)) || is.object(x) || anyNA(x)) {
        stop(name, " must contain non-missing numbers or resolution strings.", call. = FALSE)
    }
    if (is.character(x)) return(trimws(unname(x)))
    if (!typeof(x) %in% c("integer", "double")) {
        stop(name, " must be numeric or character.", call. = FALSE)
    }
    if (any(x < 0) || (name == "split_points" && any(!is.finite(x)))) {
        stop(name, " contains a resolution outside its allowed range.", call. = FALSE)
    }
    x[x == 0] <- 0
    text <- rep.int("Inf", length(x))
    remaining <- which(is.finite(x))
    for (digits in seq_len(17L)) {
        if (!length(remaining)) break
        values <- x[remaining]
        candidate <- trimws(formatC(values, format = "g", digits = digits, decimal.mark = "."))
        exact <- as.double(candidate) == values
        text[remaining[exact]] <- candidate[exact]
        remaining <- remaining[!exact]
    }
    if (length(remaining)) stop("Could not encode numeric ", name, ".", call. = FALSE)
    text
}

interval_worker_count <- function(workers, intervals) {
    if (is.null(workers)) workers <- min(4L, parallelly::availableCores())
    if (length(workers) != 1L || !typeof(workers) %in% c("integer", "double") ||
        is.object(workers) || !is.null(dim(workers)) || !is.finite(workers) ||
        workers < 1 || workers > .Machine$integer.max || workers != floor(workers)) {
        stop("workers must be NULL or a positive whole number.", call. = FALSE)
    }
    as.integer(min(workers, intervals))
}

EnumerateLouvain <- function(object, graph = NULL, k = NULL,
                             weights = c("auto", "jaccard", "stored"),
                             split_points = c(0.5, 1, 2), r_max = Inf, workers = NULL,
                             max_clusters = 101, louvain_engine = c("simple", "seurat"),
                             simple.control = list(), seurat.control = list()) {
    engine <- match.arg(louvain_engine)
    common <- list(graph = graph, k = k, weights = weights, split_points = split_points,
                   r_max = r_max, workers = workers, max_clusters = max_clusters)
    # Only force the active control. The inactive configuration may even be a promise.
    active <- if (engine == "simple") simple.control else seurat.control
    validate_control_names(active)
    shared <- intersect(names(active), names(common))
    common[shared] <- active[shared]
    specific <- active[setdiff(names(active), shared)]
    if (engine == "simple" && length(specific)) {
        stop("Unknown Simple control: ", paste(names(specific), collapse = ", "), call. = FALSE)
    }
    control <- if (engine == "seurat") seurat_controls(specific) else NULL
    if (!is.null(control$graph.name)) {
        if (!is.null(common$graph) && !identical(common$graph, control$graph.name))
            stop("graph and seurat.control$graph.name must select the same graph.", call. = FALSE)
        common$graph <- control$graph.name
    }
    do.call(enumerate_graph, c(list(object = object, control = control), common))
}

enumerate_graph <- function(object, graph, k, weights, split_points, r_max,
                            workers, max_clusters, control) {
    if (!inherits(object, "Seurat")) stop("object must be a Seurat object.")
    if (length(max_clusters) != 1L || !typeof(max_clusters) %in% c("integer", "double") ||
        is.object(max_clusters) || !is.null(dim(max_clusters)) || is.na(max_clusters) ||
        max_clusters < 1 || max_clusters != floor(max_clusters)) {
        stop("max_clusters must be a positive whole number or Inf.", call. = FALSE)
    }
    weights <- match.arg(weights, c("auto", "jaccard", "stored"))
    if (length(r_max) != 1L) stop("r_max must be a single upper limit.", call. = FALSE)
    limit_text <- resolution_text(r_max, "r_max")
    ranges <- resolution_ranges_cpp(resolution_text(split_points, "split_points"), limit_text)
    requested_r_max <- ranges$r_max
    if (!is.null(control) && control$modularity.fxn == 2L &&
        length(resolution_ranges_cpp("1", requested_r_max)$split_points)) {
        ranges <- resolution_ranges_cpp(ranges$split_points, "1")
    }
    n_workers <- interval_worker_count(workers, length(ranges$split_points) + 1L)
    graphs <- SeuratObject::Graphs(object)
    if (is.null(graph)) {
        default <- paste0(SeuratObject::DefaultAssay(object), "_snn")
        matches <- grep("snn$", graphs, value = TRUE, ignore.case = TRUE)
        if (default %in% graphs) graph <- default
        else if (length(matches) == 1L) graph <- matches
        else stop("Specify graph by name. Available graphs: ", paste(graphs, collapse = ", "))
    }
    if (!is.character(graph) || length(graph) != 1L || is.na(graph) || !graph %in% graphs) {
        stop("Unknown graph. Available graphs: ", paste(graphs, collapse = ", "))
    }
    g <- object[[graph]]
    rn <- rownames(g)
    cn <- colnames(g)
    cells <- colnames(object)
    if (!length(rn) || nrow(g) != ncol(g) || is.null(cn) ||
        anyNA(rn) || anyNA(cn) || anyDuplicated(rn) || anyDuplicated(cn) ||
        !setequal(rn, cn) || !all(rn %in% cells)) {
        stop("The graph must be square with matching, unique Seurat cell names on both axes.")
    }
    vertices <- if (is.null(control)) cells[cells %in% rn] else cn
    g <- g[vertices, vertices, drop = FALSE]
    if (any(!is.finite(g@x)) || any(g@x < 0)) stop("Weights must be finite and nonnegative.")
    if (!isTRUE(Matrix::isSymmetric(g, tol = 0))) stop("The SNN graph must be symmetric.")
    edges <- Matrix::summary(Matrix::drop0(Matrix::triu(g, k = 1L)))
    values <- unique(edges$x)
    encoding <- decode_weights(values, k, weights, length(vertices))
    # Any cap at least as large as the graph retains the complete path.
    cap <- if (max_clusters < length(vertices)) as.integer(max_clusters) else 0L
    if (is.null(control)) {
        path <- enumerate_capped_parallel_cpp(length(vertices), edges$i, edges$j, match(edges$x, values),
                                             values, encoding$overlap, encoding$k, ranges$split_points,
                                             ranges$r_max, n_workers, cap)
    } else {
        path <- seurat_enumeration(vertices, cells, edges, values, encoding, ranges, requested_r_max,
                                   n_workers, cap, control, graph)
    }

    membership <- path$membership[match(cells, vertices), , drop = FALSE]
    ids <- if (ncol(membership)) paste0("P", seq_len(ncol(membership))) else character()
    colnames(membership) <- ids
    partitions <- data.frame(cell = cells, membership, row.names = cells, check.names = FALSE)
    intervals <- path$intervals
    n_clusters <- if (length(ids)) apply(path$membership, 2L, max) else integer()
    intervals$n_clusters <- n_clusters[intervals$partition]
    intervals$partition <- ids[intervals$partition]
    scores <- data.frame(partition = ids, n_clusters = n_clusters, path$scores)
    recommendation <- path$recommendation
    recommendation$partition <- ids[recommendation$partition]
    recommendation$representative_partition <- ids[recommendation$representative_partition]
    result <- list(
        partitions = partitions,
        intervals = intervals,
        scores = scores,
        recommendation = recommendation,
        settings = list(graph = graph, weight_model = if (encoding$k) "jaccard" else "stored",
                        k_used = if (encoding$k) encoding$k else NA_integer_,
                        k_supplied = k, vertex_order = vertices,
                        diagonal = "ignored", louvain_engine = if (is.null(control)) "simple" else "seurat",
                        algorithm = if (is.null(control)) "SUNLouvainPath-0.1" else control$algorithm,
                        split_points = ranges$split_points, r_max = requested_r_max,
                        max_clusters = max_clusters, workers = path$search_plan$effective_workers,
                        search_plan = path$search_plan,
                        package_version = as.character(utils::packageVersion("SUNLouvainPath")))
    )
    if (!is.null(control)) {
        result$settings$seurat.control <- control
        result$settings$effective_r_max <- ranges$r_max
        result$raw <- path$raw
        result$queries <- path$queries
        result$query_idents <- path$query_idents
    }
    object@tools[["SUNLouvainPath"]] <- result
    if (!identical(ranges$r_max, requested_r_max)) {
        message("Seurat modularity.fxn = 2 uses [0, 1]; requested r_max = ", requested_r_max, ".")
    } else if (ranges$r_max != "Inf") {
        message("Requested resolution range: [0, ", ranges$r_max, "] (r_max = ", limit_text, ").")
    }
    object
}
