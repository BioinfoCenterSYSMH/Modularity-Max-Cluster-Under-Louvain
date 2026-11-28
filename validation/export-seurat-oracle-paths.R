# Called by verify-seurat-oracle.py. Extract raw and post-processed MML paths,
# plus fixed-point answers from the unmodified Seurat 5.5 double optimizer.
args <- commandArgs(TRUE)
stopifnot(length(args) == 2L)
.libPaths(c(normalizePath(args[1]), .libPaths()))
suppressPackageStartupMessages(library(SUNLouvainPath))
suppressPackageStartupMessages(library(Seurat))
stopifnot(as.character(packageVersion("Seurat")) == "5.5.0",
          as.character(packageVersion("SUNLouvainPath")) == "0.3.1.9004")
base <- args[2]
read_tsv <- function(name) read.delim(file.path(base,name),stringsAsFactors=FALSE)
spec <- read_tsv("cases.tsv")
edges <- read_tsv("edges.tsv")
queries <- read_tsv("native-queries.tsv")
tab <- function(x,file) write.table(x,file.path(base,file),sep="\t",row.names=FALSE,quote=FALSE)
key <- function(x) paste(as.integer(x),collapse=",")
path_rows <- function(name, x) {
    y <- x$intervals
    y$labels <- vapply(y$partition, function(p) key(x$partitions[[p]]), character(1))
    y$case <- name
    y[c("case","lower","upper","lower_closed","upper_closed","labels")]
}
raw_rows <- list()
final_rows <- list()
post_rows <- list()
native_rows <- list()
for (idx in seq_len(nrow(spec))) {
    z <- spec[idx,]
    e <- edges[edges$case == z$case,]
    names <- sprintf("c%02d", seq_len(z$n))
    counts <- Matrix::sparseMatrix(i=rep(1L,z$n),j=seq_len(z$n),x=rep(1,z$n),
                                   dims=c(1L,z$n), dimnames=list("placeholder",names))
    obj <- CreateSeuratObject(counts)
    g <- Matrix::sparseMatrix(i=c(e$i,e$j,seq_len(z$n)),j=c(e$j,e$i,seq_len(z$n)),
                              x=c(rep(e$num/e$den,2),rep(1,z$n)),dims=rep(z$n,2),
                              dimnames=list(names,names))
    obj[["RNA_snn"]] <- SeuratObject::as.Graph(g)
    ctrl <- list(algorithm=z$algorithm,modularity.fxn=z$fxn,n.start=z$starts,
                 n.iter=z$iters,random.seed=z$seed,group.singletons=z$group)
    run <- suppressMessages(EnumerateLouvain(obj, "RNA_snn", k=if(z$jaccard) 20L else NULL,
           weights=if(z$jaccard) "jaccard" else "stored", workers=1L + idx %% 2L,
           max_clusters=Inf,louvain_engine="seurat",seurat.control=ctrl))
    tool <- SeuratObject::Tool(run, slot="SUNLouvainPath")
    raw_rows[[idx]] <- path_rows(z$case,tool$raw)
    final_rows[[idx]] <- path_rows(z$case,tool)
    mapping <- lapply(tool$raw$partitions[-1L], function(raw){
        v <- structure(as.character(raw-1L),names=names)
        processed <- if(z$group && all(table(v)==1L) && length(v)>1L) v else
            Seurat:::GroupSingletons(v,obj[["RNA_snn"]],group.singletons=z$group,verbose=FALSE)
        data.frame(case=z$case,raw=key(raw),post=key(match(processed,unique(processed))))
    })
    post_rows[[idx]] <- do.call(rbind,mapping)
    q <- queries[queries$case==z$case,]
    if (nrow(e)) {
        native_rows[[z$case]] <- data.frame(case=z$case,r=q$r,labels=vapply(seq_len(nrow(q)),function(j){
            key(Seurat:::RunModularityClusteringCpp(g,z$fxn,q$num[j]/q$den[j],z$algorithm,
                                                     z$starts,z$iters,z$seed,FALSE,"")+1L)
        }, character(1)))
    }
}
tab(do.call(rbind,raw_rows),"raw.tsv")
tab(do.call(rbind,final_rows),"final.tsv")
tab(do.call(rbind,post_rows),"post.tsv")
tab(do.call(rbind,native_rows),"native.tsv")
