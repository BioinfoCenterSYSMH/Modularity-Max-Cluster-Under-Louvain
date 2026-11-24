\name{EnumerateLouvain}
\alias{EnumerateLouvain}
\title{Enumerate deterministic Louvain partitions on a Seurat SNN graph}
\usage{
EnumerateLouvain(object, graph = NULL, k = NULL,
                 weights = c("auto", "jaccard", "stored"))
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
}
\description{
Returns all distinct final partitions produced as the generalized modularity
resolution varies over the nonnegative real line. The graph is fixed. Classical
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

Exact integer arithmetic tracks changes in affine move comparisons. Runs
at a boundary and at its symbolic right-hand limit separately handle exact
ties. For each move, compare the chosen target with every eligible challenger.
The earliest possible overtake anywhere on the latter run certifies
the open interval before that root. The scan ends when the current trace
has no further root. Identical outputs on adjacent pieces are coalesced.
On large graphs, time and output size can be substantial.
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
The \code{settings} list stores the selected graph, vertex order and weight
interpretation. Repeating the call replaces this tool's result in the
returned object.
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
obj <- EnumerateLouvain(obj, "RNA_snn", k = 2)
out <- SeuratObject::Tool(obj, slot = "SUNLouvainPath")
out$scores
out$recommendation
}
