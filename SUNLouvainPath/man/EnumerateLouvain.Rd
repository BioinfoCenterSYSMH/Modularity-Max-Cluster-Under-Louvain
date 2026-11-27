\name{EnumerateLouvain}
\alias{EnumerateLouvain}
\title{Enumerate deterministic Louvain partitions on a Seurat SNN graph}
\usage{
EnumerateLouvain(object, graph = NULL, k = NULL,
                 weights = c("auto", "jaccard", "stored"),
                 split_points = c(0.5, 1, 2), r_max = Inf, workers = NULL)
}
\arguments{
  \item{object}{A Seurat object containing an undirected, nonnegative graph.}
  \item{graph}{A graph name. Defaults to the default assay's \code{_snn}
    graph, then to the unique graph with a name ending in \code{snn}.}
  \item{k}{Known construction neighbour count for Jaccard decoding. If supplied,
    incompatible off-diagonal weights cause an error. A subset may retain weights
    from a graph built with a larger \code{k}.}
  \item{weights}{With \code{"auto"}, try the Jaccard encoding described below,
    then fall back to the exact stored binary weights. With \code{"jaccard"},
    require a compatible encoding. With \code{"stored"}, use the stored doubles
    as exact binary rationals and omit \code{k}.}
  \item{split_points}{Vector of finite, nonnegative resolution values. Distinct
    points strictly inside the search range split it into intervals. Use
    \code{numeric(0)} for a single interval. Numeric values are interpreted
    using their shortest round-trip decimal representation. Character values
    can specify an exact decimal or fraction, for example \code{"108/95"}.
    For decimals supplied as strings in scientific notation, the absolute
    value of the exponent must be at most 10000.}
  \item{r_max}{Inclusive maximum resolution. The default \code{Inf} covers
    all nonnegative resolutions. A finite upper limit can be a numeric value
    or an exact character value with the same exponent limit as
    \code{split_points}. \code{r_max = 0} evaluates only zero. After a
    successful finite search the function reports the actual search range.}
  \item{workers}{Maximum number of concurrent native enumeration threads, as
    a positive integer. The default \code{NULL} uses up to four threads,
    subject to \code{parallelly::availableCores()} and the number of intervals. Use
    \code{workers = 1L} to run on the calling thread.}
}
\description{
Returns all distinct final partitions produced as the generalized modularity
resolution varies across the requested range on a fixed graph. Classical
Newman--Girvan modularity at scoring resolution one ranks all partitions.
}
\details{
The algorithm ignores diagonal entries (cell self-similarities). It uses each
off-diagonal undirected edge once. For Jaccard weights, each stored double must
equal the double resulting from rounding an overlap fraction
\eqn{s/(2k-s)}. If \code{k} is omitted, try the smallest compatible positive
integer up to the graph vertex count. This identifies a compatible encoding;
the construction parameter can be supplied when known. The recorded
\code{weight_model} and \code{k_used} describe the actual computation.

The deterministic engine starts each level with singleton units, visits them
in order of their smallest original cell index (object column order), and
chooses the highest strictly positive gain among neighbouring communities.
Equal positive gains favour the smaller current community slot. A tie with
staying leaves the unit in place. Empty slots are not move targets.
After a sweep with no moves, communities are contracted, preserving their
weighted volumes. No singleton reassignment or random restarts are applied.
Seurat's \code{FindClusters()} has its own ordering and postprocessing.

Exact integer arithmetic tracks changes in affine move comparisons. At a
boundary the engine reuses an adjacent trajectory when its move choices also
win under the boundary tie rules. Otherwise it evaluates the exact point.
Successive trajectories may reuse a prefix of certified moves.
For each newly evaluated move, compare the chosen target with every eligible challenger.
The earliest possible overtake anywhere on the latter run certifies
the open interval before that root. Each interval starts from the same
original graph with the same vertex order. The default intervals are
\code{[0, 0.5)}, \code{[0.5, 1)}, \code{[1, 2)} and \code{[2, Inf)}.
The interval starting at a split point evaluates that point exactly. The
final interval also evaluates a finite \code{r_max} exactly. Threads share
the read-only graph and maintain independent Louvain states.
Outputs are merged in resolution order. Identical partitions receive one
ID, adjacent pieces with the same output are coalesced, and exact scores
determine all tied maximizers across the search range.
On large graphs, time and output size can be substantial.

Connected components retain the original relative vertex order and share the
full graph's weight scale. Isolated vertices and disjoint cell pairs have
closed-form paths. The exact start of the all-singleton tail is computed
from the original graph, independently of the requested range.
}
\value{
The returned Seurat object contains \code{object@tools[["SUNLouvainPath"]]}.
This result can also be accessed with
\code{SeuratObject::Tool(object, slot = "SUNLouvainPath")}. Its tables are:
\itemize{
  \item \code{partitions}: a cell column and one integer membership column for
    each distinct partition. Cells outside a selected subgraph receive \code{NA}.
  \item \code{intervals}: partition ID, exact rational endpoints lower/upper,
    endpoint inclusion flags and number of clusters. \code{"Inf"} marks the
    unbounded tail. A singleton point has equal closed endpoints.
  \item \code{scores}: partition ID, number of clusters, classical modularity
    as a double and an exact fraction, and an exact maximum flag \code{is_max}.
  \item \code{recommendation}: the earliest attained resolution among all
    maximum-score partitions, reported as an exact string and a numeric
    approximation. A status of \code{"open_infimum"} indicates that the
    minimum does not exist: the recommended minimum is \code{NA}, and the
    infimum and a concrete interior representative with its partition ID
    are supplied. Use the exact strings to reason about boundary ties.
    With zero total off-diagonal weight, the singletons are returned for
    all resolutions and the scores and recommendation are undefined.
}
The \code{settings} list stores the selected graph, vertex order, weight
interpretation, effective \code{split_points}, actual \code{r_max} and
number of enumeration threads used (\code{workers}). The effective boundaries
are returned as exact strings. Within \code{settings}, \code{search_plan}
reports the mode (\code{edgeless}, \code{matching}, \code{components}, or
\code{connected}), \code{n_components}, \code{component_sizes} in order of
the earliest cell, the off-diagonal edge count \code{n_edges}, and the exact
inclusive \code{singleton_tail_start}. Repeating the call replaces this tool's result
in the returned object.
}
\references{
Default core detection uses \href{https://parallelly.futureverse.org/reference/availableCores.html}{\code{parallelly::availableCores()}}.
The numeric thread-count argument follows the convention in
\href{https://search.r-project.org/CRAN/refmans/RcppParallel/html/setThreadOptions.html}{RcppParallel's
\code{setThreadOptions(numThreads)}}. This package uses native C++ threads.
}
\examples{
cells <- c("A", "B", "C")
counts <- Matrix::Matrix(matrix(1, 2, 3,
    dimnames = list(c("gene1", "gene2"), cells)), sparse = TRUE)
obj <- SeuratObject::CreateSeuratObject(counts)
g <- matrix(1/3, 3, 3, dimnames = list(cells, cells))
diag(g) <- 1
g[1, 2] <- g[2, 1] <- 1
obj[["RNA_snn"]] <- SeuratObject::as.Graph(Matrix::Matrix(g, sparse = TRUE))
obj <- EnumerateLouvain(obj, "RNA_snn", k = 2, workers = 1L)
out <- SeuratObject::Tool(obj, slot = "SUNLouvainPath")
out$scores
out$recommendation

limited <- EnumerateLouvain(obj, "RNA_snn", k = 2,
                            split_points = c("1/4", "1/2"),
                            r_max = "3/4", workers = 2L)
SeuratObject::Tool(limited, slot = "SUNLouvainPath")$settings$r_max
}
