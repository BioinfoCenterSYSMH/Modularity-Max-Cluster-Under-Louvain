# Reconstruct the graph from integer neighbor overlaps in the published cell order.
# Only the graph is analyzed. The single assay feature is a Seurat container placeholder.
VerifyLouvainExample <- function(dataset = c("ten_cells", "hesc")) {
    dataset <- match.arg(dataset)
    read_fixture <- function(kind) {
        path <- system.file("extdata", paste0(dataset, "_", kind, ".rds"),
                            package = "SUNLouvainPath", mustWork = TRUE)
        readRDS(path)
    }
    input <- read_fixture("graph")
    cells <- input$cells
    n <- length(cells)
    weights <- input$overlap / (2 * input$k - input$overlap)
    graph <- Matrix::sparseMatrix(
        i = c(input$i, input$j, seq_len(n)), j = c(input$j, input$i, seq_len(n)),
        x = c(weights, weights, input$diagonal), dims = c(n, n), dimnames = list(cells, cells))
    counts <- Matrix::sparseMatrix(i = rep(1L, n), j = seq_len(n), x = rep(1, n),
                                   dims = c(1L, n), dimnames = list("placeholder", cells))
    object <- SeuratObject::CreateSeuratObject(counts, project = dataset)
    object[["RNA_snn"]] <- SeuratObject::as.Graph(graph)
    if (!is.null(input$annotation)) {
        object$reference_annotation <- input$annotation
    }
    object <- EnumerateLouvain(object, graph = "RNA_snn", k = input$k, weights = "jaccard")
    observed <- SeuratObject::Tool(object, slot = "SUNLouvainPath")
    expected <- read_fixture("expected")
    compare <- function(value, reference, item) {
        if (!isTRUE(all.equal(value, reference, tolerance = 0))) {
            stop(sprintf("%s example: %s differ from the reference.", dataset, item), call. = FALSE)
        }
    }
    labels <- as.matrix(observed$partitions[, -1L, drop = FALSE])
    compare(as.character(observed$partitions$cell), cells, "cell IDs")
    compare(labels, expected$labels, "partition memberships")
    compare(observed$intervals, expected$intervals, "breakpoints or endpoint inclusion flags")
    compare(observed$scores[names(expected$scores)], expected$scores, "exact scores or maximum flags")
    compare(observed$recommendation[names(expected$recommendation)], expected$recommendation,
            "recommended resolutions or partitions")

    best <- observed$recommendation$representative_partition
    groups <- observed$partitions[[best]]
    internal <- sum(weights[groups[input$i] == groups[input$j]])
    degrees <- Matrix::rowSums(graph) - input$diagonal
    volumes <- tapply(degrees, groups, sum)
    classic_q <- internal / sum(weights) - sum((volumes / sum(degrees))^2)
    best_row <- match(best, observed$scores$partition)
    stopifnot(abs(classic_q - observed$scores$modularity[best_row]) < 1e-12)
    message(sprintf("%s verified: %d cells, %d partitions, %d intervals; best Q = %.9f (%d clusters).",
                    dataset, n, ncol(labels), nrow(observed$intervals), classic_q,
                    observed$scores$n_clusters[best_row]))
    if (!is.null(input$annotation)) {
        agreement <- table(input$annotation, groups)
        pairs <- function(x) sum(x * (x - 1) / 2)
        by_type <- pairs(rowSums(agreement))
        by_group <- pairs(colSums(agreement))
        chance <- by_type * by_group / choose(n, 2)
        ari <- (pairs(agreement) - chance) / ((by_type + by_group) / 2 - chance)
        stopifnot(nrow(agreement) == 9L, abs(ari - 0.930962584338794) < 1e-12)
        message(sprintf("Reference annotation: %d classes; adjusted Rand index = %.9f.",
                        nrow(agreement), ari))
    }
    invisible(object)
}
