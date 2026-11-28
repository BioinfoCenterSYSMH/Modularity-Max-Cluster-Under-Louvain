"""Independently validate MML's Seurat paths. Requires Python 3.9+, R and Seurat 5.5.0.

python verify-seurat-oracle.py --library PATH_TO_INSTALLED_BETA --output validation-directory
"""
import argparse
import csv
import shutil
import subprocess
import tempfile
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

from seurat_oracle import Graph
from seurat_oracle_cases import cases, algebraic_crossings


def write(path, headers, rows):
    with path.open("w", newline="", encoding="utf-8") as stream:
        table = csv.writer(stream, delimiter="\t", lineterminator="\n")
        table.writerow(headers)
        table.writerows(rows)


def read_cases(path):
    grouped = defaultdict(list)
    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            grouped[row["case"]].append(row)
    return grouped


def canonical(labels):
    return tuple(labels.index(v) for v in labels)


def label_text(labels):
    return ",".join(map(str, labels))


def parse_path(rows):
    return [(F(row["lower"]), None if row["upper"] == "Inf" else F(row["upper"]),
             row["lower_closed"] == "TRUE", row["upper_closed"] == "TRUE", row["labels"])
            for row in rows]


def lookup(path, r):
    vals = [key for lower,upper,left,right,key in path
            if (lower < r or (left and lower == r))
            and (upper is None or r < upper or (right and r == upper))]
    if len(vals) != 1:
        raise AssertionError(f"At r={r}, expected exactly one partition, got {vals}")
    return vals[0]


def prepare(base, settings):
    truth = lambda b: "TRUE" if b else "FALSE"
    write(base/"cases.tsv","case n algorithm fxn starts iters seed group jaccard".split(),
          [(x.name,x.n,x.algorithm,x.fxn,x.starts,x.iters,x.seed,truth(x.group),truth(x.jaccard))
           for x in settings])
    write(base/"edges.tsv","case i j num den".split(),
          [(c.name,i+1,j+1,F(w).numerator,F(w).denominator)
           for c in settings for i,j,w in c.edges])
    probes = [F(0),F(1,5),F(23,37),F(4,5),F(13,14),F(1),F(3,2),F(2),F(9)]
    write(base/"native-queries.tsv","case r num den".split(),
          [(c.name,str(q),q.numerator,q.denominator) for c in settings for q in probes
           if c.fxn == 1 or q <= 1])


def audit(base, output, settings):
    raw = read_cases(base/"raw.tsv")
    final = read_cases(base/"final.tsv")
    post = read_cases(base/"post.tsv")
    native = read_cases(base/"native.tsv")
    summary, differences = [], []
    for case in settings:
        graph = Graph(case.n,case.edges)
        options = dict(algorithm=case.algorithm,fxn=case.fxn,starts=case.starts,
                       iters=case.iters,seed=case.seed)
        raw_path, final_path = parse_path(raw[case.name]), parse_path(final[case.name])
        assert (raw_path[-1][1] is None) if case.fxn == 1 else (
            raw_path[-1][1] == 1 and raw_path[-1][3])
        bounds = {F(0), F(1), F(4,5), F(13,14)}
        for seg in raw_path + final_path:
            bounds.add(seg[0])
            if seg[1] is not None:
                bounds.add(seg[1])
        if case.complete:
            bounds.update(algebraic_crossings(graph,case.fxn))
        bounds = sorted(bounds)
        probes = set(bounds)
        probes.update((a+b)/2 for a,b in zip(bounds,bounds[1:]))
        if case.fxn == 1:
            probes.add(bounds[-1]+1)
        post_lookup = {r["raw"]:r["post"] for r in post[case.name]}
        for r in sorted(probes):
            expected = tuple(x+1 for x in graph.evaluate(r,**options)[0])
            actual = lookup(raw_path,r)
            if actual != label_text(expected):
                raise AssertionError(f"{case.name} at {r}: expected ranked raw {expected}, got {actual}")
            seen = tuple(lookup(final_path,r).split(","))
            independent = tuple(post_lookup[actual].split(","))
            if canonical(seen) != canonical(independent):
                raise AssertionError(f"{case.name} at {r}: singleton postprocessing mismatch")
        different = 0
        for row in native[case.name]:
            r = F(row["r"])
            expected = tuple(x+1 for x in graph.evaluate(r,**options)[0])
            native_ranked = tuple(map(int,row["labels"].split(",")))
            if expected != native_ranked:
                different += 1
                differences.append((case.name,str(r),label_text(expected),row["labels"],
                                    canonical(expected)!=canonical(native_ranked)))
        if case.name in ("rounding","dyadic_rounding"):
            target = "1" if case.name == "rounding" else "2"
            assert any(c==case.name and r==target and changed for c,r,a,b,changed in differences)
        if case.name == "start_switch":
            x, h = F(13,14), F(1,100000)
            l, p, r = [graph.evaluate(v,record=True,**options) for v in (x-h,x,x+h)]
            assert l[2] == p[2] == r[2] and l[0] != p[0] == r[0]
            assert [(s.internal,s.squares) for s in p[1]] == [(26,906)]*3+[(34,1354)]
            assert any(seg[0] == x for seg in raw_path)
        if case.name.startswith("refinement_"):
            expected = (0,0,0,1,0,1,1,1,1,0) if case.algorithm==1 else (1,1,0,0,1,0,0,0,0,1)
            assert graph.evaluate(F(4,5),**options)[0] == expected
        summary.append((case.name,case.n,case.algorithm,case.fxn,len(raw_path),len(probes),
                        case.complete,len(native[case.name]),different))
    write(output/"seurat-oracle-results.tsv",
          ["case","cells","algorithm","modularity_fxn","raw_intervals","exact_probes",
           "all_partition_line_crossings","native_probes","native_ranked_differences"],summary)
    write(output/"seurat-native-differences.tsv",
          ["case","resolution","exact_ranked","native_ranked","different_membership"],differences)
    print(f"{len(summary)} cases, {sum(s[5] for s in summary)} exact point/interval probes, "
          f"{sum(s[7] for s in summary)} native queries, {len(differences)} ranked differences.")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library",required=True)
    parser.add_argument("--output",required=True,type=Path)
    parser.add_argument("--rscript",default=shutil.which("Rscript") or
                        "C:/Program Files/R/R-4.6.0/bin/Rscript.exe")
    args=parser.parse_args()
    settings=cases()
    args.output.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory() as temp:
        base=Path(temp)
        prepare(base,settings)
        subprocess.run([args.rscript,"--vanilla",str(Path(__file__).with_name("export-seurat-oracle-paths.R")),
                        str(Path(args.library).resolve()),str(base)],check=True)
        audit(base,args.output,settings)


if __name__ == "__main__":
    main()
