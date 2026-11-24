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

EnumerateLouvain <- function(object, graph = NULL, k = NULL,
                             weights = c("auto", "jaccard", "stored")) {
    if (!inherits(object, "Seurat")) stop("object must be a Seurat object.")
    weights <- match.arg(weights)
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
    path <- enumerate_path_cpp(length(vertices), edges$i, edges$j,
                               match(edges$x, values), values, encoding$overlap, encoding$k)

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
                        package_version = as.character(utils::packageVersion("SUNLouvainPath")))
    )
    object@tools[["SUNLouvainPath"]] <- result
    object
}
