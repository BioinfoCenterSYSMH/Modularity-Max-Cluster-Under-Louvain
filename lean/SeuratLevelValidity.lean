import SeuratFlow

namespace Louvain.SeuratExact

/-- A coarsening call is only made on a strict decrease of the occupied unit
count. Any two fuels that bound that count therefore give the same plan. -/
theorem multilevel_fuel_irrelevant {n : ℕ} {State : Type}
    (G : Graph n) (rng : OrderSource State n) (refine : Bool)
    (first second : ℕ) (u p : Part n) (state : State)
    (firstEnough : Graph.count u ≤ first) (secondEnough : Graph.count u ≤ second) :
    multilevel G rng refine first u p state = multilevel G rng refine second u p state := by
  induction first generalizing second u p state with
  | zero =>
    cases second with
    | zero => rfl
    | succ second =>
      have stop : Graph.count u ≤ 1 := by omega
      simp [multilevel, stop]
  | succ first ih =>
    cases second with
    | zero =>
      have stop : Graph.count u ≤ 1 := by omega
      simp [multilevel, stop]
    | succ second =>
      by_cases stop : Graph.count u ≤ 1
      · simp [multilevel, stop]
      · simp only [multilevel, if_neg stop]
        apply congrArg (Plan.bind (localPhase G rng u p state))
        funext result
        obtain ⟨⟨moved, didMove⟩, afterLocal⟩ := result
        dsimp only
        by_cases contracts : Graph.count moved < Graph.count u
        · simp only [if_pos contracts]
          have firstBound : Graph.count moved ≤ first := by omega
          have secondBound : Graph.count moved ≤ second := by omega
          rw [ih second moved moved afterLocal firstBound secondBound]
        · simp only [if_neg contracts]

/-- The finite local plan corresponds to the uncapped cyclic loop at the
permutation's actual size. Only the final compaction changes label IDs. -/
theorem local_phase_quiesces {n : ℕ} {State : Type}
    (G : Graph n) (rng : OrderSource State n) (u p : Part n) (state : State)
    (r : ℝ) (hr : 0 ≤ r) (hp : Graph.respects u p) :
    let order := (rng.next state (representatives u)).1
    let nextRng := (rng.next state (representatives u)).2
    let initial : ValidLocalState u := ⟨⟨p, initialFree order.length p, false⟩, hp⟩
    order.length = Graph.count u ∧
    ∃ result : Seurat.LocalResult (ValidLocalState u),
      Seurat.LocalQuiesces (step G u order r hr) order.length 0 0 initial result ∧
      result.visits ≤ localFuel G ∧
      (localPhase G rng u p state).run (G.atReal r) =
        ((compact result.state.1.part, result.state.1.changed), nextRng) := by
  let order := (rng.next state (representatives u)).1
  have length : order.length = Graph.count u :=
    (rng.perm state (representatives u)).length_eq.trans (representatives_length_eq u)
  have lengthBound : order.length ≤ n :=
    (rng.perm state (representatives u)).length_eq.le.trans (representatives_length_le u)
  obtain ⟨result, executes, bound, reports⟩ :=
    localLoop_quiesces G u order lengthBound r hr ⟨p, initialFree order.length p, false⟩ hp
  refine ⟨length, result, executes, bound, ?_⟩
  change (localPhase G rng u p state).run (G.atReal r) =
    ((compact result.state.1.part, result.state.1.changed), (rng.next state (representatives u)).2)
  rw [reports]
  cases h : rng.next state (representatives u)
  simp only [localPhase, h, Plan.run_bind, Plan.run]
  simp only [order, h]

end Louvain.SeuratExact
