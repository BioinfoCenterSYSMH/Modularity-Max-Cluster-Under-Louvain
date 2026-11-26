library(SUNLouvainPath)

# All fixtures and examples are constructed here and contain at most ten cells.
make_object <- function(w) {
    n <- nrow(w)
    stopifnot(n >= 1L, n <= 10L)
    cells <- LETTERS[seq_len(n)]
    dimnames(w) <- list(cells, cells)
    counts <- Matrix::Matrix(matrix(1, 3, n, dimnames = list(letters[1:3], cells)),
                             sparse = TRUE)
    obj <- SeuratObject::CreateSeuratObject(counts)
    obj[["RNA_snn"]] <- SeuratObject::as.Graph(Matrix::Matrix(w, sparse = TRUE))
    obj
}
from_sets <- function(sets) {
    shared <- outer(seq_len(nrow(sets)), seq_len(nrow(sets)),
                    Vectorize(function(i, j) length(intersect(sets[i, ], sets[j, ]))))
    shared / (2 * ncol(sets) - shared)
}
tool <- function(x) SeuratObject::Tool(x, slot = "SUNLouvainPath")
lookup <- function(x, num, den) {
    if (x == "Inf") return(-1)
    p <- as.numeric(strsplit(x, "/", fixed = TRUE)[[1L]])
    if (length(p) == 1L) p[2] <- 1
    sign(num * p[2] - p[1] * den)
}
at_r <- function(out, num, den) {
    z <- out$intervals
    lo <- vapply(z$lower, lookup, numeric(1), num = num, den = den)
    hi <- vapply(z$upper, lookup, numeric(1), num = num, den = den)
    hit <- which((lo > 0 | (lo == 0 & z$lower_closed)) &
                 (hi < 0 | (hi == 0 & z$upper_closed)))
    stopifnot(length(hit) == 1L)
    out$partitions[[z$partition[hit]]]
}

w <- matrix(1/3, 3, 3)
diag(w) <- 1
w[1, 2] <- w[2, 1] <- 1
o <- make_object(w)
o@tools$existing <- list(keep = 3)
f <- EnumerateLouvain(o, k = 2)
out <- tool(f)
stopifnot(identical(o@tools, list(existing = list(keep = 3))),
          identical(f@tools$existing, o@tools$existing),
          identical(f@meta.data, o@meta.data), identical(f@active.ident, o@active.ident),
          identical(f@graphs, o@graphs), identical(tool(unserialize(serialize(f, NULL))), out),
          identical(out$intervals$lower, c("0","5/4","15/8")),
          identical(out$scores$modularity_exact, c("0","-2/25","-9/25")),
          out$recommendation$recommended_resolution == "0",
          identical(tool(EnumerateLouvain(o))$intervals, out$intervals))

# Independent oracle. List every set partition for a four-cell graph and
# every crossing of its whole-partition score lines. Re-run a reference
# Louvain that recomputes scores from the original graph for every move.
# Small integer numerators/denominators make the products exact in R doubles.
all_parts <- function(n) {
    if (n == 1L) return(list(1L))
    unlist(lapply(all_parts(n - 1L), function(g)
        lapply(seq_len(max(g) + 1L), function(i) c(g, i))), recursive = FALSE)
}
coeff <- function(w, g) {
    inside <- sum(w[upper.tri(w) & outer(g, g, "==")])
    c(2 * sum(w) * inside, sum(tapply(rowSums(w), g, sum)^2))
}
reference <- function(w, num, den) {
    val <- function(g) sum(coeff(w, g) * c(den, -num))
    n <- nrow(w)
    unit <- seq_len(n)
    repeat {
        lab <- seq_len(max(unit))
        repeat {
            old <- lab
            for (u in seq_along(lab)) {
                g <- lab[unit]
                best <- val(g)
                adjacent <- colSums(w[unit == u, , drop = FALSE]) > 0
                for (target in sort(unique(g[adjacent & g != lab[u]]))) {
                    option <- g
                    option[unit == u] <- target
                    q <- val(option)
                    if (q > best) {
                        best <- q
                        lab[u] <- target
                    }
                }
            }
            if (identical(old, lab)) break
        }
        merged <- match(lab[unit], unique(lab[unit]))
        if (max(merged) == max(unit)) return(merged)
        unit <- merged
    }
}
verify_all <- function(w) {
    out <- tool(EnumerateLouvain(make_object(w), weights = "stored"))
    ab <- vapply(all_parts(nrow(w)), function(g) coeff(w, g), numeric(2))
    pairs <- utils::combn(seq_len(ncol(ab)), 2L)
    diff <- ab[, pairs[1, ], drop = FALSE] - ab[, pairs[2, ], drop = FALSE]
    diff <- diff[, diff[2, ] != 0 & diff[1, ] * diff[2, ] >= 0, drop = FALSE]
    cuts <- t(cbind(c(0, 1), abs(diff)))
    v <- cuts[, 1] / cuts[, 2]
    cuts <- cuts[order(v)[!duplicated(sort(v))], , drop = FALSE]
    last <- nrow(cuts)
    probes <- rbind(cuts, cuts[-last, , drop = FALSE] + cuts[-1L, , drop = FALSE],
                    c(sum(cuts[last, ]), cuts[last, 2]))
    witnessed <- character(nrow(probes))
    for (i in seq_len(nrow(probes))) {
        r <- probes[i, ]
        expected <- reference(w, r[1], r[2])
        stopifnot(identical(at_r(out, r[1], r[2]), expected))
        witnessed[i] <- paste(expected, collapse = ",")
    }
    stopifnot(length(unique(witnessed)) == nrow(out$scores))
    for (i in seq_len(nrow(out$scores))) {
        ab <- coeff(w, out$partitions[[out$scores$partition[i]]])
        q <- (ab[1] - ab[2]) / sum(w)^2
        stopifnot(abs(out$scores$modularity[i] - q) < 1e-14)
    }
    out
}
cycle <- matrix(c(0,1,0,1, 1,0,1,0, 0,1,0,1, 1,0,1,0), 4)
ties <- verify_all(cycle)
stopifnot(sum(ties$scores$is_max) > 1L, ties$recommendation$recommended_resolution == "0")
weighted <- matrix(c(0,3,1,0, 3,0,2,0, 1,2,0,1, 0,0,1,0), 4)
invisible(verify_all(weighted))

sets <- rbind(c(1,2,5),c(2,5,6),c(1,3,5),c(1,4,5),c(2,3,5),c(2,5,6))
open <- tool(EnumerateLouvain(make_object(from_sets(sets)), k = 3))
rec <- open$recommendation
stopifnot(rec$status == "open_infimum", is.na(rec$recommended_resolution),
          is.na(rec$partition), rec$infimum == "65/66",
          rec$representative_partition %in% open$scores$partition[open$scores$is_max])
p <- as.numeric(strsplit(rec$representative_resolution, "/", fixed = TRUE)[[1]])
intw <- round(from_sets(sets) * 10)
diag(intw) <- 0
stopifnot(identical(reference(intw, p[1], p[2]), open$partitions[[rec$representative_partition]]),
          !identical(reference(intw, 65, 66), open$partitions[[rec$representative_partition]]))

sets <- rbind(c(1,2,3),c(2,3,6),c(1,2,3),c(3,4,5),c(1,5,6),c(1,2,6))
point <- tool(EnumerateLouvain(make_object(from_sets(sets))))
z <- point$intervals
idx <- which(z$lower == "108/95" & z$upper == "108/95")
stopifnot(length(idx) == 1L, z$lower_closed[idx], z$upper_closed[idx],
          z$partition[idx-1L] == z$partition[idx+1L],
          z$partition[idx] != z$partition[idx-1L])
intw <- round(from_sets(sets) * 10)
diag(intw) <- 0
stopifnot(identical(reference(intw, 108, 95), at_r(point, 108, 95)))

empty <- tool(EnumerateLouvain(make_object(diag(1, 3))))
one <- tool(EnumerateLouvain(make_object(matrix(1, 1, 1))))
stopifnot(identical(empty$partitions$P1, 1:3), is.na(empty$scores$modularity),
          empty$recommendation$status == "undefined_modularity",
          one$intervals$upper == "Inf", one$scores$n_clusters == 1L)
bad <- function(expr) inherits(try(expr, silent = TRUE), "try-error")
stopifnot(bad(EnumerateLouvain(o, k = 1)), bad(EnumerateLouvain(o, graph = "missing")))
asym <- w
asym[1, 2] <- 0.1
stopifnot(bad(EnumerateLouvain(make_object(asym))))

# A second graph may cover a subset of the object's cells. It also may
# arrive in a different order. The selected graph follows object cell order.
subset_obj <- make_object(diag(1, 5))
ord <- c("C", "A", "B")
subset_obj[["other_snn"]] <- o[["RNA_snn"]]
sub <- tool(EnumerateLouvain(subset_obj, graph = "other_snn", k = 2))
stopifnot(identical(sub$settings$vertex_order, c("A", "B", "C")),
          all(is.na(sub$partitions[4:5, -1L])), identical(sub$scores, out$scores))
# Directly exercise an imported graph with unordered axes. Current Seurat
# already enforces object order when inserting through its public setter.
subset_obj@graphs[["other_snn"]] <- SeuratObject::as.Graph(o[["RNA_snn"]][ord, ord])
stopifnot(identical(tool(EnumerateLouvain(subset_obj, "other_snn", k = 2)), sub))

# A stored double such as 0.1 is not exactly 1/10. The open group's first
# nontrivial score must keep that exact distinction.
binary <- matrix(c(0,1,0.1, 1,0,0.1, 0.1,0.1,0), 3)
stored <- tool(EnumerateLouvain(make_object(binary)))
stopifnot(stored$settings$weight_model == "stored",
          any(nchar(stored$scores$modularity_exact) > 30))

# Integration test through Seurat's actual neighbour graph builder.
if (requireNamespace("Seurat", quietly = TRUE)) {
    n <- 10L
    obj <- make_object(diag(1, n))
    xy <- cbind(PC_1 = c(1,2,3,4,5,9,10,11,12,13),
                PC_2 = c(2,2.1,1.9,3,1,0,2,1,2.1,4))
    rownames(xy) <- colnames(obj)
    obj[["pca"]] <- SeuratObject::CreateDimReducObject(embeddings = xy, key = "PC_", assay = "RNA")
    obj <- Seurat::FindNeighbors(obj, reduction = "pca", dims = 1:2, k.param = 3L,
                                 nn.method = "rann", prune.SNN = 0, verbose = FALSE)
    f <- EnumerateLouvain(obj, k = 3L)
    ans <- tool(f)
    stopifnot(identical(ans$partitions$cell, colnames(obj)),
              nrow(ans$partitions) == 10L, ans$settings$weight_model == "jaccard",
              ans$intervals$lower[1L] == "0", tail(ans$intervals$upper, 1) == "Inf")
    g <- as.matrix(obj[["RNA_snn"]])
    diag(g) <- 0
    expected <- vapply(ans$partitions[-1], function(p)
        sum((g - outer(rowSums(g), rowSums(g)) / sum(g)) * outer(p, p, "==")) /
        sum(g), numeric(1))
    stopifnot(max(abs(expected - ans$scores$modularity)) < 1e-13)
    # Check each reported point, each open segment and the unbounded tail
    # against the whole-partition reference on this actual SNN graph.
    intw <- round(g * 10)  # k=3 has weights 0, 1/5, 1/2, 1
    fraction <- function(s) {
        v <- as.numeric(strsplit(s, "/", fixed = TRUE)[[1]])
        if (length(v) == 1L) c(v, 1) else v
    }
    for (row in seq_len(nrow(ans$intervals))) {
        z <- ans$intervals[row, ]
        left <- fraction(z$lower)
        right <- if (z$upper == "Inf") c(sum(left), left[2]) else fraction(z$upper)
        probes <- rbind(left, right, left + right)
        for (idx in seq_len(nrow(probes))) {
            r <- probes[idx, ]
            stopifnot(identical(reference(intw, r[1], r[2]), at_r(ans, r[1], r[2])))
        }
    }
}

# Splitting the parameter axis must preserve every public result table,
# including its ordering, re-used partition IDs, open boundaries, and ties.
result_names <- c("partitions", "intervals", "scores", "recommendation")
same_path <- function(x, y) identical(x[result_names], y[result_names])
point_obj <- make_object(from_sets(sets))
serial <- tool(EnumerateLouvain(point_obj, k = 3L, split_points = numeric(), workers = 1L))
fragments <- c("1/7", "108/95", "3/2", "5/2")
parallel_path <- tool(EnumerateLouvain(point_obj, k = 3L, split_points = fragments,
                                       workers = 2L))
stopifnot(same_path(point, serial), same_path(serial, parallel_path),
          identical(point$settings$split_points, c("1/2", "1", "2")),
          identical(serial$settings$workers, 1L), identical(parallel_path$settings$workers, 2L))

# Check against the original unrestricted C++ scanner as an independent
# reference for splitting and stitching (the moving rules are shared).
edges <- Matrix::summary(Matrix::drop0(Matrix::triu(point_obj[["RNA_snn"]], k = 1L)))
values <- unique(edges$x)
old <- SUNLouvainPath:::enumerate_path_cpp(6L, edges$i, edges$j, match(edges$x, values),
                                         values, round(6 * values / (1 + values)), 3L)
ids <- paste0("P", seq_len(ncol(old$membership)))
old_intervals <- old$intervals
old_intervals$partition <- ids[old_intervals$partition]
old_rec <- old$recommendation
old_rec$partition <- ids[old_rec$partition]
old_rec$representative_partition <- ids[old_rec$representative_partition]
stopifnot(identical(unname(as.matrix(serial$partitions[-1L])), unname(old$membership)),
          identical(serial$intervals[names(old_intervals)], old_intervals),
          identical(serial$scores[names(old$scores)], old$scores),
          identical(serial$recommendation, old_rec))

# At 108/95 the partition differs from *both* adjacent open intervals. A
# finite closed range ending at that split must include the point just once.
messages <- capture.output(bounded <- tool(EnumerateLouvain(point_obj, k = 3L,
    split_points = fragments, r_max = "108/95", workers = 2L)), type = "message")
z <- bounded$intervals
last <- nrow(z)
stopifnot(any(grepl("108/95", messages, fixed = TRUE)),
          z$lower[last] == "108/95", z$upper[last] == "108/95",
          z$lower_closed[last], z$upper_closed[last],
          sum(z$lower == "108/95" & z$upper == "108/95") == 1L,
          identical(at_r(bounded, 108, 95), at_r(serial, 108, 95)),
          identical(at_r(bounded, 1, 1), at_r(serial, 1, 1)),
          bad(at_r(bounded, 109, 95)))

# A numeric cap inside a constant interval becomes a closed upper boundary.
# On this graph the first transition is 5/4, so [0,1] has one partition
# even though the default splits include an interior cut at 0.5.
messages <- capture.output(short <- tool(EnumerateLouvain(o, k = 2L,
    split_points = c(2, 1, 0.5, 0, 0.5), r_max = 1, workers = 1L)), type = "message")
stopifnot(length(messages) > 0L, nrow(short$intervals) == 1L,
          identical(short$settings$split_points, "1/2"), identical(short$settings$r_max, "1"),
          short$intervals$lower == "0", short$intervals$upper == "1",
          short$intervals$lower_closed, short$intervals$upper_closed)

# Infinity remains silent and [0,0] runs exactly one point, including when
# the full path's first optimal interval has a positive, unattained infimum.
open_obj <- make_object(from_sets(rbind(c(1,2,5),c(2,5,6),c(1,3,5),
                                         c(1,4,5),c(2,3,5),c(2,5,6))))
messages <- capture.output(unbounded <- tool(EnumerateLouvain(open_obj,
    k = 3L, r_max = Inf, split_points = numeric(), workers = 1L)), type = "message")
stopifnot(!length(messages), same_path(unbounded, open))
limited <- tool(suppressMessages(EnumerateLouvain(open_obj, k = 3L,
    split_points = c("65/66", "99/100"), r_max = 1, workers = 2L)))
rec <- limited$recommendation
witness <- as.numeric(strsplit(rec$representative_resolution, "/", fixed = TRUE)[[1L]])
if (length(witness) == 1L) witness[2L] <- 1
stopifnot(rec$status == "open_infimum", rec$infimum == "65/66",
          witness[1] * 66 > witness[2] * 65, witness[1] <= witness[2],
          identical(at_r(limited, witness[1], witness[2]),
                    limited$partitions[[rec$representative_partition]]))
messages <- capture.output(zero <- tool(EnumerateLouvain(open_obj, k = 3L,
    r_max = 0, workers = 4L)), type = "message")
stopifnot(length(messages) > 0L, nrow(zero$intervals) == 1L,
          identical(zero$settings$workers, 1L),
          zero$intervals$lower == "0", zero$intervals$upper == "0",
          zero$intervals$lower_closed, zero$intervals$upper_closed,
          nrow(zero$scores) == 1L, zero$scores$is_max,
          zero$recommendation$recommended_resolution == "0",
          identical(at_r(zero, 0, 1), at_r(unbounded, 0, 1)))

cycle_serial <- tool(EnumerateLouvain(make_object(cycle), weights = "stored",
    split_points = numeric(), workers = 1L))
stopifnot(same_path(ties, cycle_serial), sum(cycle_serial$scores$is_max) > 1L,
          bad(EnumerateLouvain(o, workers = 0L)), bad(EnumerateLouvain(o, workers = 1.5)),
          bad(EnumerateLouvain(o, r_max = -1)), bad(EnumerateLouvain(o, r_max = NA_real_)),
          bad(EnumerateLouvain(o, split_points = c(0.5, NA_real_))),
          bad(EnumerateLouvain(o, split_points = c(1, Inf))),
          bad(EnumerateLouvain(o, split_points = -1)))
