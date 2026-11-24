# Exact Louvain resolution path in Lean 4

**共同开发者 · Developers**　王俊博 (Junbo Wang)、廖建友 (Jianyou Liao)、GPT-6.2 Astra (AI)。

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

For fixed `k`, Lean also verifies polynomial bounds on the score alphabet and the outer search budget. A tight runtime exponent and a bit-operation bound for a compiled R/C++ package remain outside the scope of these theorems. The project verifies the mathematical algorithm at source level in Lean. [Formal bounds](Jaccard.lean#L62)

## Reproduce the check

With the Lean toolchain manager `elan` installed, run these commands from this directory (`lean/`). The project pins Lean and mathlib to version 4.19.0.

```sh
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true RawJaccard.lean
```

The final command prints the axiom dependencies of the main completeness and uniqueness theorems. Both use only `propext`, `Classical.choice` and `Quot.sound`.

A six-cell example exercises the critical resolution `108/95`. Run it with `lake env lean --run Example.lean`. [Example](Example.lean)
