# Exact Louvain resolution path in Lean 4

本项目由王俊博、廖建友共同开发，开发过程中使用了 GPT-6.2 Astra 辅助。两位作者对本项目报告的结果共同负责。

Junbo Wang and Jianyou Liao developed this project with assistance from GPT-6.2 Astra. Both authors take joint responsibility for the results reported in this project.

**Manuscript in preparation. Please contact the author before citing this work.**

**论文正在写作中。引用本项工作前，请先联系作者。** [Contact the author through GitHub Issues](https://github.com/BioinfoCenterSYSMH/Modularity-Max-Cluster-Under-Louvain/issues/new)

This project gives a Lean 4 proof that an exact enumeration recovers every final partition returned by a specified deterministic multilevel Louvain algorithm as its resolution ranges over all nonnegative real numbers on a fixed Jaccard shared nearest-neighbor (SNN) graph.

## Main theorem

For every positive neighbor count `k`, every graph encoded by equal-sized neighbor sets and a symmetric pruning mask, and every canonical partition `p`, Lean proves the following equivalence.

```lean
theorem louvain_enumeration_exact (hk : 0 < k) (p : Part n) :
    p ∈ S.graph.localOutputs ↔ ∃ r : ℝ, 0 ≤ r ∧ S.RawReturns r id p
```

The left side computes a finite set using rational arithmetic. The right side runs Louvain at one exact real resolution on the original intersection-over-union weights, starting from singleton cells. Its definition is independent of the enumerator and has no iteration cap. A second theorem proves that each resolution has exactly one final partition. [Main theorem and uniqueness](RawJaccard.lean#L153)

The input numbering fixes the vertex order. Each sweep visits units in increasing order of the smallest original vertex they contain. A unit may stay or move to a neighboring community. Staying wins a zero-gain tie. A positive-gain tie goes to the lowest current community label. Contraction preserves the original weighted degrees. Final labels are the smallest original vertex indices in each community.

## Why the enumeration covers the continuum

1. Each candidate target has a score of the form `a − r b`. At a critical resolution the enumerator evaluates both the point and the choices immediately to its right. Among the targets tied at the point, those with the smallest penalty `b` remain optimal immediately to the right. [One-move interval proof](Path.lean#L89)
2. Along each right-hand execution, the enumerator records the future intersections at which a challenger can overtake the chosen target. Until the earliest such intersection, every choice in every sweep and contraction is preserved. If the set of intersections is empty, the proof covers the whole remaining half-line. Checking the endpoint itself also recovers a partition attained at a single resolution. [Trace and enumeration proofs](Enumeration.lean)
3. The finite set of integer score coefficient pairs gives a decreasing rank for sweeps that accept a move. Every contraction decreases the number of units. These facts prove termination of the uncapped execution. [Termination proof](Graph.lean)
4. The full modularity objective and the local-gain rule give the same point choices, right-hand choices and adaptive intersections. Clearing the Jaccard denominators preserves choices on the original weights. [Gain identity](LocalGain.lean) · [Execution equivalence](Completeness.lean) · [Raw Jaccard semantics](RawJaccard.lean)

## The arithmetic operation bound

For each fixed positive neighbor count $k$ there is a constant $C(k)$ independent of the graph, its pruning mask and the number of cells. The dense algorithm enumerates, deduplicates and scores every reachable partition and collects all ties for highest classical modularity in at most $C(k)n^{14}$ charged operations for $n>0$.

```lean
theorem Louvain.Metered.arithmetic_n14 (k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, ∀ n (S : SNN n k), 0 < n →
      (Louvain.Metered.enumerateAndScore S).steps ≤ C * n^14
```

- The counted input comprises the neighbor sets and symmetric pruning mask. The arithmetic RAM charges table construction once and counts subsequent random accesses and exact scalar arithmetic at unit cost. Straight-line kernels carry explicit constant charges. [Cost semantics](MeteredTables.lean) · [Input and program](JaccardProgram.lean)
- The crossing count is $O(n^6)$. Following an exact point or its right limit costs $O(n^8)$, including sweeps, label changes and level preparation. Deduplication, scoring and collecting all maximizers together cost $O(n^{13})$. [Crossings](BreakpointCount.lean) · [Metered scan](MeteredScan.lean) · [Composition](ArithmeticBound.lean)
- `scores_raw_exact` characterizes every scored row by reachability and classical modularity on the original unscaled Jaccard graph. `distinct_scores` proves that a partition appears only once. `best_exact` characterizes every row tied for highest score. Classical modularity has its usual interpretation for positive total edge weight. [Scored rows](ScoredPath.lean) · [Maximizers](JaccardProgram.lean)

固定近邻数后，$O(n^{14})$ 是上述数学算法的保守最坏情形上界。Lean 验证了算术模型中的运算次数。实际 R/C++ 使用稀疏结构，其结果通过示例单独检验。位运算复杂度的完整形式化仍是独立问题。

## Seurat Louvain with exact arithmetic

The Seurat extension models the weighted-modularity optimizer in Seurat 5.5 (`modularity.fxn = 1`). It uses the seeded Java permutation stream, the unused-label stack, coarsening, optional multilevel refinement (`algorithm = 2`), the outer iteration limit, and the original order of the restarts. A tied restart score keeps the incumbent. The model covers the raw optimizer on the original off-diagonal graph. The double-precision Seurat executable and its `FindClusters` singleton postprocessing have separate semantics. [Seurat local moving and refinement](https://github.com/satijalab/seurat/blob/v5.5.0/src/ModularityOptimizer.cpp#L482-L635) · [Seurat restart selection](https://github.com/satijalab/seurat/blob/v5.5.0/src/RModularityOptimizer.cpp#L99-L141)

- [`enumerate_exact_flow`](SeuratFlow.lean) gives soundness and completeness over all real $r \ge 0$. Each returned partition is attained at some resolution and every attained partition is returned. The scan includes boundary points and decisions immediately to their right, including changes in the winning restart. [Original Jaccard score scaling](SeuratJaccard.lean)
- [`visit_drops`](SeuratLocal.lean) proves strict progress for zero-gain moves as well as positive gains. The lexicographic potential prefers higher modularity, then more occupied labels, then a lower sum of labels over original cells. [Unused-label stack invariants](SeuratStackFlow.lean) · [Uncapped termination and valid contraction fuel](SeuratLevelValidity.lean)
- [`seurat_exact_polynomial`](SeuratCost.lean) bounds the total number of candidate entries across both point and right-limit evaluations by $C(k,R,I)(n+1)^{18}$ for fixed positive $k$, number of restarts $R$, and outer iteration limit $I$. [Breakpoint and output bounds](SeuratRoots.lean) give $O((n+1)^6)$ scan boundaries and distinct outputs. With fixed $k$, score components and rational boundary numerators and denominators have $O(\log(n+1))$ bits. Evaluating a candidate on a dense graph, maintaining the finite cut set and deduplicating outputs each use polynomial work. The formal meter counts candidates and visits. The exponent 18 refers to the candidate meter, while a machine-level bit-cost bound and runtime of the R/C++ package are separate questions.
- [Java permutation stream](SeuratOrder.lean) proves the generated order is a permutation and rejection sampling terminates for positive bounds below $2^{31}$. The [four-cell regression](SeuratExample.lean) checks seed-dependent choices and the complete seed-4 path.

## Reproduce the check

With the Lean toolchain manager `elan` installed, run these commands from this directory (`lean/`). The project pins Lean and mathlib to version 4.19.0.

```sh
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true RawJaccard.lean
lake env lean -DwarningAsError=true ArithmeticBound.lean
lake env lean -DwarningAsError=true ScoredPath.lean
lake env lean -DwarningAsError=true SeuratCost.lean
lake env lean -DwarningAsError=true --run SeuratExample.lean
```

The three source checks print the axiom dependencies of the main completeness, uniqueness, arithmetic-bound and scoring results. They use only `propext`, `Classical.choice` and `Quot.sound`.

Run `lake env lean --run ScoredExample.lean` to verify both reachable partitions of a two-cell graph, their hand-computed scores $0$ and $-1/2$, and the unique winner. [Scoring example](ScoredExample.lean)

A six-cell example exercises the critical resolution `108/95`. Run it with `lake env lean --run Example.lean`. [Example](Example.lean)
