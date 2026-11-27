library(SUNLouvainPath)

object_from_edges <- function(n, i, j, w) {
    cells <- paste0("C", seq_len(n))
    g <- Matrix::sparseMatrix(i = c(i, j, seq_len(n)), j = c(j, i, seq_len(n)),
        x = c(w, w, rep(1, n)), dims = c(n, n), dimnames = list(cells, cells))
    counts <- Matrix::sparseMatrix(i = rep(1L, n), j = seq_len(n), x = rep(1, n),
        dims = c(1L, n), dimnames = list("feature", cells))
    obj <- SeuratObject::CreateSeuratObject(counts)
    obj[["RNA_snn"]] <- SeuratObject::as.Graph(g)
    obj
}
result <- function(obj, ...) {
    obj <- suppressMessages(EnumerateLouvain(obj, ...))
    SeuratObject::Tool(obj, slot = "SUNLouvainPath")[c("partitions", "intervals", "scores", "recommendation")]
}

# Two interleaved components change on the same two global thresholds. Both
# the label order and the scores are expressed on the complete six-cell graph.
triangles <- object_from_edges(6L, c(1, 1, 3, 2, 2, 4), c(3, 5, 5, 4, 6, 6),
                               c(1, 1/5, 1/5, 1, 1/5, 1/5))
simul <- result(triangles, k = 3L, split_points = numeric(), workers = 1L)
stopifnot(identical(simul, result(triangles, k = 3L, split_points = c("7/3", "35/9", "10"), workers = 4L)),
          identical(simul$intervals$lower, c("0", "7/3", "35/9")),
          all(simul$intervals$lower_closed), !any(simul$intervals$upper_closed),
          identical(simul$partitions$P1, c(1L, 2L, 1L, 2L, 1L, 2L)),
          identical(simul$partitions$P2, c(1L, 2L, 1L, 2L, 3L, 4L)),
          identical(simul$partitions$P3, 1:6),
          identical(simul$scores$modularity_exact, c("1/2", "33/98", "-19/98")))

# These two distinct stored binary64 weights give one extremely narrow but
# nonempty middle interval. The integer 4 falls strictly inside it.
matching <- object_from_edges(5L, c(1, 2), c(4, 5), c(0.1 + 0.2, 0.3))
cut1 <- "10808639105689191/2702159776422298"
cut2 <- "21617278211378382/5404319552844595"
close <- result(matching, weights = "stored", workers = 4L, split_points = c(cut1, "4", cut2))
stopifnot(identical(close$intervals$lower, c("0", cut1, cut2)),
          identical(close$intervals$upper, c(cut1, cut2, "Inf")),
          all(close$intervals$lower_closed), !any(close$intervals$upper_closed),
          identical(close$partitions$P2, c(1L, 2L, 3L, 4L, 2L)),
          identical(close$scores$modularity_exact, c(
              "58413339658516817306151547117240/116826679317033634612303094234481",
              "1622592768292133513819790039668/12980742146337070512478121581609",
              "-58413339658516817306151547117241/233653358634067269224606188468962")))
closed_cap <- result(matching, weights = "stored", split_points = c(cut1, cut2), r_max = "4", workers = 2L)
stopifnot(identical(closed_cap$intervals$upper, c(cut1, "4")),
          identical(closed_cap$intervals$upper_closed, c(FALSE, TRUE)),
          identical(closed_cap$partitions, close$partitions[1:3]))

# A six-cell component, an isolated vertex, and an independent pair appear
# in interleaved vertex order. The global path has a point-only partition at
# 128/95, including when a user caps the range at that exact fraction.
i <- c(1,1,1,1,1,3,3,3,3,4,4,4,6,8,2)
j <- c(3,4,6,8,9,4,6,8,9,6,8,9,8,9,7)
overlap <- c(2,3,1,1,2,2,1,1,2,1,1,2,1,2,3)
interleaved <- object_from_edges(9L, i, j, overlap / (6 - overlap))
path <- result(interleaved, k = 3L, workers = 1L, split_points = numeric())
stopifnot(identical(path, result(interleaved, k = 3L, workers = 4L,
                                split_points = c("128/95", "32/13", "64/5"))),
          identical(path$intervals$partition[2:4], c("P2", "P3", "P2")),
          identical(path$partitions$P3, c(1L, 2L, 3L, 1L, 4L, 5L, 2L, 3L, 3L)),
          path$scores$modularity_exact[3] == "85/512")
cap <- result(interleaved, k = 3L, r_max = "128/95", split_points = c("1/8", "2944/2475"), workers = 3L)
singleton <- tail(cap$intervals, 1L)
stopifnot(singleton$lower == "128/95", singleton$upper == singleton$lower,
          singleton$lower_closed, singleton$upper_closed, identical(cap$partitions, path$partitions[1:4]))

# Route diagnostics describe the original graph even when the user requests
# just r=0. The tail starts at the same global fraction as in an unbounded run.
check_plan <- function(obj, mode, sizes, edges, tail_start, ...) {
    tested <- suppressMessages(EnumerateLouvain(obj, workers = 1L, r_max = 0, ...))
    plan <- SeuratObject::Tool(tested, slot = "SUNLouvainPath")$settings$search_plan
    stopifnot(identical(plan$mode, mode), identical(plan$n_components, length(sizes)),
              identical(sort(plan$component_sizes), sort(sizes)), identical(plan$n_edges, edges),
              identical(plan$singleton_tail_start, tail_start))
}
empty_graph <- object_from_edges(4L, integer(), integer(), numeric())
cycle_graph <- object_from_edges(4L, c(1, 2, 3, 1), c(2, 3, 4, 4), rep(1, 4))
check_plan(empty_graph, "edgeless", rep(1L, 4L), 0, "0", weights = "stored")
check_plan(cycle_graph, "connected", 4L, 4, "2", weights = "stored")
check_plan(matching, "matching", c(2L, 2L, 1L), 2, cut2, weights = "stored")
check_plan(interleaved, "components", c(6L, 2L, 1L), 15, "64/5", k = 3L)
