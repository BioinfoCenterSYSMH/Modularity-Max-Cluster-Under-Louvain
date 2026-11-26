"""Evaluate every eligible HESC partition using the unchanged SCCAF self_projection function."""
import argparse
import ast
import contextlib
import csv
import gzip
import hashlib
import io
import os
from pathlib import Path
import sys
import time
import warnings
import zipfile

for key in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[key] = "1"

args = argparse.ArgumentParser()
args.add_argument("--data", type=Path, default=Path(__file__).resolve().parent)
args.add_argument("--deps", type=Path, default=Path(__file__).resolve().parent / "deps")
args.add_argument("--workers", type=int, default=3)
opt, _ = args.parse_known_args()
if (opt.deps / "py14").is_dir():
    sys.path.insert(0, str(opt.deps / "py14"))
import numpy as np
import sklearn
from scipy.sparse import csr_matrix
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import train_test_split
from sklearn.exceptions import ConvergenceWarning

SEEDS = (1, 2, 3)
FIELDS = ["partition", "n_clusters", "min_cluster_size", "status", "accuracy",
          "correct1", "correct2", "correct3", "total_correct", "total_test", "convergence_warnings"]
X = None
LABELS = None
SELF_PROJECT = None

def initialize():
    global X, LABELS, SELF_PROJECT
    assert sklearn.__version__ == "1.4.2"
    wheel = opt.deps / "SCCAF-0.0.10-py3-none-any.whl"
    assert hashlib.sha256(wheel.read_bytes()).hexdigest() == "4cfff1a1c303097cc309d6b448ace79eff98f97d288097d91e71a1820244838d"
    with zipfile.ZipFile(wheel) as z:
        module = ast.parse(z.read("SCCAF/__init__.py").decode())
    func = next(f for f in module.body if isinstance(f,ast.FunctionDef) and f.name == "self_projection")
    env = dict(np=np, LogisticRegression=LogisticRegression, train_test_split=train_test_split)
    exec(compile(ast.Module(body=[func],type_ignores=[]), str(wheel), "exec"),env)
    SELF_PROJECT = env["self_projection"]
    with gzip.open(opt.data / "logdata.csr.gz","rb") as f:
        def read(dtype, n):
            return np.frombuffer(f.read(np.dtype(dtype).itemsize*n), dtype=dtype)
        n,g,nnz = read("<i4",3)
        indptr, indices, data = read("<i4",n+1), read("<i4",nnz), read("<f8",nnz)
        assert not f.read(1)
    X = csr_matrix((data, indices, indptr),shape=(n,g))
    LABELS = np.fromfile(opt.data/"membership.bin", dtype="<i4").reshape((975,n))
    assert n == 498 and g == 24789 and X.nnz == nnz and np.isfinite(data).all()

def evaluate(i):
    y = LABELS[i]
    classes, counts = np.unique(y, return_counts=True)
    row = dict(partition=f"P{i+1}",n_clusters=len(classes),min_cluster_size=int(counts.min()))
    if len(classes) < 2 or counts.min() < 2:
        return dict(row, status="ineligible_one_class" if len(classes)<2 else "ineligible_singleton")
    correct, convergence, test_total = [], 0, 0
    for seed in SEEDS:
        train_y,test_y = train_test_split(y,stratify=y,test_size=.5,random_state=seed)
        if len(set(train_y)) != len(classes) or len(set(test_y)) != len(classes):
            return dict(row, status="ineligible_class_absent_train_or_test")
        np.random.seed(seed)
        with contextlib.redirect_stdout(io.StringIO()), warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always",ConvergenceWarning)
            _, prediction, truth, clf, _, accuracy = SELF_PROJECT(X,y,cv=0,n_jobs=1)
        convergence += sum(issubclass(w.category,ConvergenceWarning) for w in caught)
        assert np.array_equal(test_y,truth) and np.array_equal(clf.classes_,classes)
        correct.append(int(np.sum(truth==prediction)))
        assert accuracy == correct[-1]/len(truth)
        test_total += len(truth)
    return dict(row, status="ok", accuracy=sum(correct)/test_total, correct1=correct[0],
                correct2=correct[1],correct3=correct[2],total_correct=sum(correct),
                total_test=test_total, convergence_warnings=convergence)

def main():
    from concurrent.futures import ProcessPoolExecutor
    start = time.monotonic()
    with (opt.data/"sccaf_scores.csv").open("w",encoding="utf-8",newline="") as out:
        writer = csv.DictWriter(out, FIELDS)
        writer.writeheader()
        with ProcessPoolExecutor(max_workers=opt.workers,initializer=initialize) as pool:
            for index,row in enumerate(pool.map(evaluate,range(975),chunksize=1)):
                writer.writerow(row)
                if index < 73:
                    out.flush()
                    print(row["partition"],row["status"],row.get("total_correct"),round(time.monotonic()-start,1),flush=True)

if __name__ == "__main__":
    main()