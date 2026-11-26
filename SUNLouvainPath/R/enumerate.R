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
                             split_points = c(0.5, 1, 2), r_max = Inf, workers = NULL) {
    if (!inherits(object, "Seurat")) stop("object must be a Seurat object.")
    weights <- match.arg(weights)
    if (length(r_max) != 1L) stop("r_max must be a single upper limit.", call. = FALSE)
    limit_text <- resolution_text(r_max, "r_max")
    ranges <- resolution_ranges_cpp(resolution_text(split_points, "split_points"), limit_text)
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
    vertices <- cells[cells %in% rn]
    g <- g[vertices, vertices, drop = FALSE]
    if (any(!is.finite(g@x)) || any(g@x < 0)) stop("Weights must be finite and nonnegative.")
    if (!isTRUE(Matrix::isSymmetric(g, tol = 0))) stop("The SNN graph must be symmetric.")
    edges <- Matrix::summary(Matrix::drop0(Matrix::triu(g, k = 1L)))
    values <- unique(edges$x)
    encoding <- decode_weights(values, k, weights, length(vertices))
    path <- enumerate_parallel_cpp(length(vertices), edges$i, edges$j, match(edges$x, values),
                                  values, encoding$overlap, encoding$k, ranges$split_points,
                                  ranges$r_max, n_workers)

    membership <- path$membership[match(cells, vertices), , drop = FALSE]
    ids <- paste0("P", seq_len(ncol(membership)))
    colnames(membership) <- ids
    partitions <- data.frame(cell = cells, membership, row.names = cells, check.names = FALSE)
    intervals <- path$intervals
    n_clusters <- apply(path$membership, 2L, max)
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
                        diagonal = "ignored", algorithm = "SUNLouvainPath-0.1",
                        split_points = ranges$split_points, r_max = ranges$r_max,
                        workers = n_workers,
                        package_version = as.character(utils::packageVersion("SUNLouvainPath")))
    )
    object@tools[["SUNLouvainPath"]] <- result
    if (ranges$r_max != "Inf") {
        message("Resolution range used: [0, ", ranges$r_max, "] (r_max = ", limit_text, ").")
    }
    object
}
