library(SUNLouvainPath)

object_from_matrix <- function(weights) {
    cells <- paste0("C", seq_len(nrow(weights)))
    dimnames(weights) <- list(cells, cells)
    counts <- matrix(1, 1, length(cells), dimnames = list("test", cells))
    obj <- SeuratObject::CreateSeuratObject(counts)
    obj[["RNA_snn"]] <- SeuratObject::as.Graph(as(Matrix::Matrix(weights, sparse = TRUE), "generalMatrix"))
    obj
}
extract <- function(x) SeuratObject::Tool(x, slot = "SUNLouvainPath")
run <- function(x, control, ...) {
    extract(suppressMessages(EnumerateLouvain(x, louvain_engine = "seurat",
        simple.control = stop("inactive Simple controls were forced"), seurat.control = control, ...)))
}
bad <- function(x) inherits(try(x, silent = TRUE), "try-error")
w <- matrix(0, 4, 4)
w[cbind(c(1,2,2,3),c(2,3,4,4))] <- c(5,8,7,7)
obj <- object_from_matrix(w + t(w))
base <- extract(EnumerateLouvain(obj, workers = 1L))
unused <- extract(EnumerateLouvain(obj, simple.control = list(workers = 1L),
                                  seurat.control = stop("inactive Seurat control was forced")))
stopifnot(identical(base, unused), base$settings$louvain_engine == "simple")
control <- list(algorithm = "louvain", n.start = 1, n.iter = 1, random.seed = 0,
                resolution = c("9/8", "1.125", "100", "101"), verbose = FALSE,
                graph.name = "RNA_snn", cluster.name = c("a","b","tail","outside"))
set.seed(292)
rng_before <- .Random.seed
grouped <- run(obj, control, workers = 1, r_max = 100)
stopifnot(identical(rng_before, .Random.seed),
          identical(grouped$queries$status, c("ok","ok","ok","outside_r_max")),
          identical(grouped$queries$resolution[1:2], c("9/8","9/8")),
          identical(grouped$query_idents$a, grouped$query_idents$b),
          identical(as.character(grouped$query_idents$a), c("0","0","1","1")),
          length(unique(grouped$query_idents$tail)) == 4,
          all(is.na(grouped$query_idents$outside)))
control$group.singletons <- FALSE
pooled <- run(obj, control, workers = 2, r_max = 100, max_clusters = 1)
stopifnot(pooled$queries$status[1] == "filtered_max_clusters",
          !is.na(pooled$queries$raw_partition[1]), is.na(pooled$queries$partition[1]),
          all(is.na(pooled$query_idents$a)), all(as.character(pooled$query_idents$tail) == "singleton"),
          all(pooled$scores$n_clusters == 1L))
for (algo in 1:2) for (fxn in 1:2) {
    cfg <- list(algorithm = algo, modularity.fxn = fxn, n.start = 2L, n.iter = 3L,
                random.seed = 4, verbose = FALSE, resolution = c(0, 0.8, 1, 1.25))
    serial <- run(obj, cfg, workers = 1L, r_max = 2)
    parallel <- run(obj, cfg, workers = 2L, split_points = c("3/4","9/8"), r_max = 2)
    outputs <- c("partitions","scores","intervals","recommendation","raw","queries","query_idents")
    stopifnot(identical(serial[outputs], parallel[outputs]),
              serial$settings$r_max == "2",
              serial$settings$effective_r_max == if (fxn == 2) "1" else "2",
              serial$queries$status[4] == if (fxn == 2) "outside_modularity_domain" else "ok")
}
limited <- run(obj, list(modularity.fxn = 2, resolution = NULL, verbose = FALSE))
stopifnot(limited$settings$effective_r_max == "1", nrow(limited$queries) == 0L,
          identical(names(limited$query_idents), "cell"))
at_zero <- run(obj, list(resolution = c(0, "1/10"), verbose = FALSE), r_max = 0)
stopifnot(identical(at_zero$queries$status, c("ok", "outside_r_max")),
          nrow(at_zero$intervals) == 1L)
stopifnot(bad(run(obj, list(algorithm = 3))), bad(run(obj, list(algorithm = "leiden"))),
          bad(run(obj, list(node.sizes = 1))), bad(run(obj, list(initial.membership = c(1,1,2,2)))),
          bad(run(obj, list(unknown = 1))), bad(run(obj, list(n.iter = 0))),
          bad(run(obj, list(edge.file.name = "other.txt"))),
          bad(run(obj, list(graph.name = "different"), graph = "RNA_snn")))
empty <- object_from_matrix(diag(1,3))
for (mode in c(TRUE,FALSE)) {
    ans <- run(empty, list(group.singletons = mode, resolution = c(0,1), verbose = FALSE))
    stopifnot(ans$scores$n_clusters == if (mode) 3L else 1L,
              is.na(ans$scores$modularity), ans$recommendation$status == "undefined_modularity")
}
