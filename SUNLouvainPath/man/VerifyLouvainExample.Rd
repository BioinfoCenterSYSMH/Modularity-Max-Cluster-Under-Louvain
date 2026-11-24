\name{VerifyLouvainExample}
\alias{VerifyLouvainExample}
\title{Reproduce a bundled resolution-path example}
\usage{
VerifyLouvainExample(dataset = c("ten_cells", "hesc"))
}
\arguments{
\item{dataset}{A ten-cell demonstration or a 498-cell human embryonic stem cell
differentiation dataset from GEO accession GSE85066.}
}
\description{Reconstructs a stored, cell-ordered Jaccard shared-nearest-neighbor
graph and calls \code{\link{EnumerateLouvain}} on a new Seurat object. Checks
every partition, exact interval, exact modularity score, maximum flag and
recommended resolution against reference results. Also computes the winning
partition's modularity directly from the edges. For HESC, checks agreement
with the original nine reference annotations.}
\details{The assay consists of one placeholder feature. The graph and cell
order are sufficient for reproducing the clustering. The example input and
expected results are separate files and are installed with the package.
The ten-cell graph uses k = 3 and HESC uses k = 20.}
\value{Invisibly returns the verified Seurat object. Use
\code{SeuratObject::Tool(object, slot = "SUNLouvainPath")} to inspect the
outputs. The HESC object has a \code{reference_annotation} metadata column.}
\examples{
ten <- VerifyLouvainExample("ten_cells")
\donttest{
hesc <- VerifyLouvainExample("hesc")
}
}
