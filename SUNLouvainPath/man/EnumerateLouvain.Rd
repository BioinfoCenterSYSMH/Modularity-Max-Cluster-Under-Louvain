\name{EnumerateLouvain}
\alias{EnumerateLouvain}
\title{Enumerate deterministic Louvain partitions on a Seurat SNN graph}
\usage{
EnumerateLouvain(object, graph = NULL, k = NULL,
                 weights = c("auto", "jaccard", "stored"),
                 split_points = c(0.5, 1, 2), r_max = Inf, workers = NULL,
                 max_clusters = 101, louvain_engine = c("simple", "seurat"),
                 simple.control = list(), seurat.control = list())
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
    successful call with a finite \code{r_max}, the function reports the
    requested finite resolution range.}
  \item{workers}{Maximum number of concurrent native enumeration threads, as
    a positive integer. The default \code{NULL} uses up to four threads,
    subject to \code{parallelly::availableCores()} and the number of intervals. Use
    \code{workers = 1L} to run on the calling thread.}
  \item{max_clusters}{Maximum number of clusters in a returned partition,
    inclusive. Supply a positive whole number or \code{Inf}. The default
    \code{101} targets analyses of up to 101 subclusters. Use \code{Inf}
    for the full path over the requested resolution range.}
  \item{louvain_engine}{Select the original deterministic MML Louvain engine
    (\code{"simple"}, the default), or the exact arithmetic version of Seurat
    5.5's seeded Louvain workflow (\code{"seurat"}).}
  \item{simple.control}{Named list of overrides for \code{graph}, \code{k},
    \code{weights}, \code{split_points}, \code{r_max}, \code{workers} and
    \code{max_clusters}. Only the selected engine's list is evaluated.}
  \item{seurat.control}{Named list accepting the same overrides and the
    Seurat-specific arguments below. Its entries take precedence over the
    corresponding top-level search settings.}
}
\description{
Returns every distinct final partition with at most \code{max_clusters}
clusters produced as the generalized modularity resolution varies across the
requested range on a fixed graph. The package evaluates classical
Newman--Girvan modularity at scoring resolution one on the retained partitions.
Other evaluation criteria can be applied to their cell memberships.
}
\details{
The algorithm ignores diagonal entries (cell self-similarities). It uses each
off-diagonal undirected edge once. For Jaccard weights, each stored double must
equal the double resulting from rounding an overlap fraction
\eqn{s/(2k-s)}. If \code{k} is omitted, try the smallest compatible positive
integer up to the graph vertex count. This identifies a compatible encoding;
the construction parameter can be supplied when known. The recorded
\code{weight_model} and \code{k_used} describe the actual computation.

The Simple engine starts each level with singleton units, visits them
in order of their smallest original cell index (object column order), and
chooses the highest strictly positive gain among neighbouring communities.
Equal positive gains favour the smaller current community slot. A tie with
staying leaves the unit in place. Empty slots are not move targets.
After a sweep with no moves, communities are contracted, preserving their
weighted volumes. No singleton reassignment or random restarts are applied.

Exact integer arithmetic tracks changes in affine move comparisons. At a
boundary the engine reuses an adjacent trajectory when its move choices also
win under the boundary tie rules. Otherwise it evaluates the exact point.
Successive trajectories may reuse a prefix of certified moves.
For each newly evaluated move, compare the chosen target with every eligible challenger.
The earliest possible overtake anywhere on the latter run certifies
the open interval before that root. Each interval starts from the same
original graph with the same vertex order. With both limits set to
\code{Inf}, the default intervals are
\code{[0, 0.5)}, \code{[0.5, 1)}, \code{[1, 2)} and \code{[2, Inf)}.
The interval starting at a split point evaluates that point exactly. The
membership at a finite \code{r_max} is included if it meets the cap. Threads share
the read-only graph and maintain independent Louvain states.
Outputs are merged in resolution order. Identical partitions receive one
ID, adjacent pieces with the same output are coalesced, and exact scores
determine all tied maximizers among the retained partitions.
On large graphs, time and output size can be substantial.

For Simple, connected components retain the original relative vertex order and share the
full graph's weight scale. Isolated vertices and disjoint cell pairs have
closed-form paths. The exact start of the all-singleton tail is computed
from the original graph, independently of the requested range.

For a finite cluster cap, Simple can certify a resolution above which every
partition returned by this Louvain algorithm exceeds the cap. The certificate
uses the graph's edge weights and weighted degrees and the strict gain required
for a move from the initial partition. The scan may stop at that boundary.
Cluster counts can decrease as resolution increases. The scan includes
eligible partitions that reappear after an ineligible partition.

The Seurat engine uses graph column order and Seurat 5.5's Java random
generator, permutations, tie handling and multiple starts. It traces the
affine comparisons on each executed path and selects the best start at
each resolution. The earliest start wins an exact tie. Crossings between
start scores can change the winner inside an interval where every start's
partition is constant. The scan evaluates exact points and right limits.
It applies the cluster cap after singleton processing. Native Seurat uses
double precision, so its result can differ at rounding-sensitive decisions.

The following entries of \code{seurat.control} map to \code{FindClusters}:
\describe{
  \item{\code{algorithm}}{1 (default) or \code{"louvain"} for Louvain;
    2 for Louvain with multilevel refinement. Algorithm 3 (SLM) and
    4 (Leiden) belong to different algorithm families and raise an error.}
  \item{\code{modularity.fxn}}{1 (default) uses weighted degrees and
    the requested domain. Objective 2 uses unit node weights and caps
    the continuous domain at \code{min(r_max, 1)}, inclusive.}
  \item{\code{n.start}, \code{n.iter}, \code{random.seed}}{Number of
    starts (default 10), maximum outer iterations per start (10), and
    seed for the Java random generator shared across starts (0).}
  \item{\code{group.singletons}}{With \code{TRUE} (default), each singleton
    joins the group to which it has the highest mean edge weight among groups
    initially containing at least two cells. Earlier assignments update the
    group means. Ties use R's default sampling algorithm with seed 1 and
    MML restores the caller's RNG state. If all cells are singletons,
    MML retains their separate labels, where native Seurat can fail.
    With \code{FALSE}, singletons share the label \code{"singleton"} as
    in serial Seurat 5.5. MML honors this argument at every worker count.}
  \item{\code{resolution}}{One or more fixed resolutions to query in
    input order. Defaults to 0.8; supply exact decimal or fraction strings
    for precise boundary queries, or \code{NULL} to skip queries. The
    continuous scan is determined by the effective domain at every setting.}
  \item{\code{graph.name}, \code{cluster.name}, \code{verbose}}{Graph alias
    agreeing with \code{graph} when both are supplied; an optional name
    per queried resolution; and a logical switch for progress feedback
    (default \code{TRUE}). Active Seurat identities are preserved.}
  \item{Other arguments}{Non-NULL Leiden controls \code{initial.membership},
    \code{node.sizes}, \code{leiden_method}, \code{leiden_objective_function}
    or deprecated \code{method} raise an error. \code{temp.file.location}
    accepts a path for interface compatibility. The in-memory graph input
    requires \code{edge.file.name} to be NULL or an empty string.}
}
On graphs without off-diagonal edges, MML defines separate raw singletons
and then applies the selected postprocessing. The included Lean proof
covers the Simple algorithm.
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
    unbounded tail. A singleton point has equal closed endpoints. With a
    finite cluster cap, excluded resolutions can leave gaps between intervals.
  \item \code{scores}: partition ID, number of clusters, classical modularity
    as a double and an exact fraction, and an exact maximum flag \code{is_max}.
  \item \code{recommendation}: the earliest attained resolution among all
    maximum-score partitions, reported as an exact string and a numeric
    approximation. A status of \code{"open_infimum"} indicates that the
    minimum does not exist: the recommended minimum is \code{NA}, and the
    infimum and a concrete interior representative with its partition ID
    are supplied. Use the exact strings to reason about boundary ties.
    With zero total off-diagonal weight, classical modularity and the
    recommendation are undefined. If no partition meets the cap, the
    status is \code{"no_eligible_partition"}, the partitions table contains
    only its cell column, and the interval and score tables have zero rows.
}
The \code{settings} list stores the selected graph, vertex order, weight
interpretation, \code{max_clusters}, requested resolution limit
\code{r_max}, split points and worker information. Resolution boundaries
are returned as exact strings. Within Simple's \code{settings}, \code{search_plan}
reports the mode (\code{edgeless}, \code{matching}, \code{components}, or
\code{connected}), \code{n_components}, \code{component_sizes} in order of
the earliest cell, the off-diagonal edge count \code{n_edges}, and the exact
inclusive \code{singleton_tail_start}. It also records the scan limit
\code{scan_r_max} and its inclusion flag \code{scan_upper_closed}.
For Seurat, \code{settings$effective_r_max} records the domain endpoint
and \code{settings$search_plan} reports the trace run counts.
The \code{raw} tables retain size-ordered optimizer labels plus one and
their complete resolution intervals. The final \code{partitions} table
uses canonical labels after singleton handling. \code{queries} records
each query's exact resolution, raw and final IDs, and status
(\code{ok}, \code{filtered_max_clusters}, \code{outside_r_max},
or \code{outside_modularity_domain}); a filtered in-domain query retains its
raw ID. \code{query_idents} gives native-style factor labels for successful
queries and missing values for the other queries.
Repeating the call replaces this tool's result in the returned object.
}
\references{
The Seurat engine follows the \href{https://github.com/satijalab/seurat/blob/v5.5.0/src/ModularityOptimizer.cpp}{Seurat 5.5 optimizer}
and \href{https://github.com/satijalab/seurat/blob/v5.5.0/R/clustering.R}{\code{FindClusters} interface}.
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
                            r_max = "3/4", workers = 2L, max_clusters = 2)
SeuratObject::Tool(limited, slot = "SUNLouvainPath")$settings$r_max
full <- EnumerateLouvain(obj, "RNA_snn", k = 2, max_clusters = Inf)
SeuratObject::Tool(full, slot = "SUNLouvainPath")$scores
seeded <- EnumerateLouvain(obj, "RNA_snn", k = 2, louvain_engine = "seurat",
                          r_max = 1, workers = 1L,
                          seurat.control = list(algorithm = 2L, n.start = 2L,
                                                resolution = c("1/2", "4/5")))
SeuratObject::Tool(seeded, slot = "SUNLouvainPath")$queries
}
