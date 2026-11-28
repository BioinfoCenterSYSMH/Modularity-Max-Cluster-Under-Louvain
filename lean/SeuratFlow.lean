import SeuratLocal
import SeuratFuel
import SeuratRoots
import SeuratLabels
import SeuratOrder

namespace Louvain.SeuratExact

open Finset

structure LocalState (n : ℕ) where
  part : Part n
  free : List (Fin n)
  changed : Bool
  deriving DecidableEq

/-- Available slots are the first `m` IDs of the current level, initially pushed
in increasing order, so the head is the top of Seurat's unused-label stack. -/
def initialFree {n : ℕ} (m : ℕ) (p : Part n) : List (Fin n) :=
  ((List.finRange n).filter (fun label : Fin n => label.val < m ∧ label ∉ units p)).reverse

def prepareFree {n : ℕ} (u : Part n) (a : Fin n) (state : LocalState n) : List (Fin n) :=
  if state.part a ∈ remaining u state.part a then state.free else state.part a :: state.free

def localVisit {n : ℕ} (G : Graph n) (u : Part n) (a : Fin n) (state : LocalState n) :
    Plan G.Code (LocalState n) :=
  let free := prepareFree u a state
  match free with
  | [] => .done state
  | empty :: tail =>
      if empty ∈ remaining u state.part a then .done state else
      (visit G u state.part a empty).bind fun p =>
        if p = state.part then .done state else
        .done ⟨p, if p a = empty then tail else free, true⟩

def orderedVisit {n : ℕ} (G : Graph n) (u : Part n) (order : List (Fin n))
    (cursor : ℕ) (state : LocalState n) : Plan G.Code (LocalState n) :=
  match order[cursor % order.length]? with
  | none => .done state
  | some a => localVisit G u a state

def localLoop {n : ℕ} (G : Graph n) (u : Part n) (order : List (Fin n)) :
    ℕ → ℕ → ℕ → LocalState n → Plan G.Code (LocalState n)
  | 0, _, _, state => .done state
  | fuel + 1, cursor, stable, state =>
      if order.length ≤ stable then .done state else
      (orderedVisit G u order cursor state).bind fun next =>
        localLoop G u order fuel (cursor + 1) (if next = state then stable + 1 else 1) next

/-- The ceiling counts possible lexicographic local potentials, independently
of the sequence of permutations, the seed, or the chosen resolution. -/
def localCeiling {n : ℕ} (G : Graph n) : ℕ := (G.budget + 1) * (n + 1) * (n * n + 1)

def localFuel {n : ℕ} (G : Graph n) : ℕ := (localCeiling G + 1) * n

private theorem localVisit_spec {n : ℕ} (G : Graph n) (u : Part n) (a : Fin n)
    (state : LocalState n) (r : ℝ) (hr : 0 ≤ r) (hp : Graph.respects u state.part) :
    let next := (localVisit G u a state).run (G.atReal r)
    Graph.respects u next.part ∧ (next ≠ state → rank G r next.part < rank G r state.part) := by
  cases hf : prepareFree u a state with
  | nil => simpa [localVisit, hf, Plan.run] using hp
  | cons empty tail =>
    by_cases he : empty ∈ remaining u state.part a
    · simpa [localVisit, hf, he, Plan.run] using hp
    have hlifo : state.part a ∉ remaining u state.part a → empty = state.part a := by
      intro hs
      have hh := hf
      rw [prepareFree, if_neg hs] at hh
      exact (List.cons.inj hh).1.symm
    let p := (visit G u state.part a empty).run (G.atReal r)
    have hres : Graph.respects u p := visit_respects G u state.part a empty hp _
    have hmove : p = state.part ∨ rank G r p < rank G r state.part :=
      visit_drops G u state.part a empty r hr hp he hlifo
    let movedState : LocalState n := ⟨p, if p a = empty then tail else empty :: tail, true⟩
    have hstep : (localVisit G u a state).run (G.atReal r) =
        if p = state.part then state else movedState := by
      simp only [localVisit, hf, if_neg he, Plan.run_bind]
      change (if p = state.part then Plan.done state else Plan.done movedState).run (G.atReal r) = _
      split <;> rfl
    dsimp only
    rw [hstep]
    by_cases hs : p = state.part
    · rw [if_pos hs]
      exact ⟨hp, fun h => (h rfl).elim⟩
    · rw [if_neg hs]
      exact ⟨hres, fun _ => hmove.resolve_left hs⟩

private theorem orderedVisit_spec {n : ℕ} (G : Graph n) (u : Part n) (order : List (Fin n))
    (cursor : ℕ) (state : LocalState n) (r : ℝ) (hr : 0 ≤ r)
    (hp : Graph.respects u state.part) :
    let next := (orderedVisit G u order cursor state).run (G.atReal r)
    Graph.respects u next.part ∧ (next ≠ state → rank G r next.part < rank G r state.part) := by
  unfold orderedVisit
  split
  · simpa [Plan.run] using hp
  · exact localVisit_spec G u _ state r hr hp

abbrev ValidLocalState {n : ℕ} (u : Part n) := {state : LocalState n // Graph.respects u state.part}

noncomputable def step {n : ℕ} (G : Graph n) (u : Part n) (order : List (Fin n))
    (r : ℝ) (hr : 0 ≤ r) (cursor : ℕ) (state : ValidLocalState u) : ValidLocalState u :=
  ⟨(orderedVisit G u order cursor state.1).run (G.atReal r),
    (orderedVisit_spec G u order cursor state.1 r hr state.2).1⟩

private noncomputable def increasingRank {n : ℕ} (G : Graph n) (r : ℝ) (state : LocalState n) : ℕ :=
  localCeiling G - rank G r state.part

private theorem increasingRank_rises {n : ℕ} (G : Graph n) (u : Part n) (order : List (Fin n))
    (r : ℝ) (hr : 0 ≤ r) (cursor : ℕ) (state : ValidLocalState u) :
    step G u order r hr cursor state ≠ state →
    increasingRank G r state.1 < increasingRank G r (step G u order r hr cursor state).1 := by
  intro changeState
  have hne : (orderedVisit G u order cursor state.1).run (G.atReal r) ≠ state.1 :=
    fun h => changeState (Subtype.ext h)
  have hd := (orderedVisit_spec G u order cursor state.1 r hr state.2).2 hne
  have hb : rank G r state.1.part < localCeiling G := by
    simpa [localCeiling, width, Nat.mul_assoc] using rank_lt G r state.1.part
  change localCeiling G - rank G r state.1.part < localCeiling G -
    rank G r ((orderedVisit G u order cursor state.1).run (G.atReal r)).part
  omega

private theorem localLoop_run {n : ℕ} (G : Graph n) (u : Part n) (order : List (Fin n))
    (r : ℝ) (hr : 0 ≤ r) (fuel cursor stable : ℕ) (state : ValidLocalState u) :
    (localLoop G u order fuel cursor stable state.1).run (G.atReal r) =
      (Seurat.localRun (step G u order r hr) order.length fuel cursor stable state).state.1 := by
  induction fuel generalizing cursor stable state with
  | zero => rfl
  | succ fuel ih =>
    by_cases quiet : order.length ≤ stable
    · simp [localLoop, Seurat.localRun, quiet, Plan.run]
    simp only [localLoop, Seurat.localRun, if_neg quiet, Plan.run_bind]
    let next := step G u order r hr cursor state
    have he : (orderedVisit G u order cursor state.1).run (G.atReal r) = state.1 ↔ next = state :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [if_congr he rfl rfl]
    exact ih _ _ next

/-- The local plan agrees with the unique uncapped cyclic execution and uses at
most `localFuel` visits. Thus its fuel is a proof bound rather than a rule for
stopping early. -/
theorem localLoop_quiesces {n : ℕ} (G : Graph n) (u : Part n) (order : List (Fin n))
    (lengthBound : order.length ≤ n) (r : ℝ) (hr : 0 ≤ r) (state : LocalState n)
    (hp : Graph.respects u state.part) :
    ∃ result : Seurat.LocalResult (ValidLocalState u),
      Seurat.LocalQuiesces (step G u order r hr) order.length 0 0 ⟨state, hp⟩ result ∧
      result.visits ≤ localFuel G ∧
      result.state.1 = (localLoop G u order (localFuel G) 0 0 state).run (G.atReal r) := by
  let valid : ValidLocalState u := ⟨state, hp⟩
  let result := Seurat.localRun (step G u order r hr) order.length (localFuel G) 0 0 valid
  have enough : Seurat.visitBudget order.length (localCeiling G) (increasingRank G r state) 0 ≤
      localFuel G :=
    (Seurat.visitBudget_le_fuel _ _ _ _).trans (Nat.mul_le_mul_left _ lengthBound)
  have spec := Seurat.localRun_spec (step G u order r hr) order.length (localCeiling G)
    (fun s => increasingRank G r s.1) (fun s => Nat.sub_le _ _)
    (increasingRank_rises G u order r hr) (localFuel G) 0 0 valid enough
  refine ⟨result, Seurat.localRun_quiesces_of_finished _ _ _ _ _ _ spec.1, spec.2.trans enough, ?_⟩
  exact (localLoop_run G u order r hr _ _ _ valid).symm

abbrev LocalResult (n : ℕ) := Part n × Bool

def localPhase {n : ℕ} {State : Type} (G : Graph n) (rng : OrderSource State n)
    (u p : Part n) (rngState : State) : Plan G.Code (LocalResult n × State) :=
  let (order, nextState) := rng.next rngState (representatives u)
  (localLoop G u order (localFuel G) 0 0 ⟨p, initialFree order.length p, false⟩).bind fun result =>
    .done ((compact result.part, result.changed), nextState)

/-- The contraction is represented on original cells. A coarsened vertex's ID
is its community ID at the previous level, and its volume is the sum of its cells'
original degrees. A refinement, when requested, reuses the parent's units. -/
def multilevel {n : ℕ} {State : Type} (G : Graph n) (rng : OrderSource State n) (refine : Bool) :
    ℕ → Part n → Part n → State → Plan G.Code (LocalResult n × State)
  | 0, _, p, state => .done ((p, false), state)
  | fuel + 1, u, p, state =>
    if Graph.count u ≤ 1 then .done ((p, false), state) else
    (localPhase G rng u p state).bind fun ((moved, didMove), afterLocal) =>
      if Graph.count moved < Graph.count u then
        (multilevel G rng refine fuel moved moved afterLocal).bind fun ((coarse, didCoarse), afterCoarse) =>
          if didCoarse then
            if refine then
              (localPhase G rng u coarse afterCoarse).bind fun ((refined, _), afterRefine) =>
                .done ((refined, true), afterRefine)
            else .done ((coarse, true), afterCoarse)
          else .done ((moved, didMove), afterCoarse)
      else .done ((moved, didMove), afterLocal)

def iterations {n : ℕ} {State : Type} (G : Graph n) (rng : OrderSource State n) (refine : Bool) :
    ℕ → Part n → State → Plan G.Code (Part n × State)
  | 0, p, state => .done (p, state)
  | count + 1, p, state =>
    (multilevel G rng refine n id p state).bind fun ((q, changed), next) =>
      if changed then iterations G rng refine count q next else .done (q, next)

/-- Option zero is the incumbent. It wins exactly equal restart scores, as in
the source optimizer's strictly greater comparison. -/
def incumbentMenu {n : ℕ} (G : Graph n) (best trial : Part n) : Menu G.Code :=
  ⟨{0, 1}, by simp, fun option => G.code (if option = 0 then best else trial)⟩

def restarts {n : ℕ} {State : Type} (G : Graph n) (rng : OrderSource State n) (refine : Bool)
    (nIterations : ℕ) : ℕ → State → Option (Part n) → Plan G.Code (Part n)
  | 0, _, best => .done (Graph.canon (best.getD id))
  | count + 1, state, best =>
    (iterations G rng refine nIterations id state).bind fun (trial, next) =>
      match best with
      | none => restarts G rng refine nIterations count next (some trial)
      | some incumbent => .ask (incumbentMenu G incumbent trial) fun option =>
          restarts G rng refine nIterations count next (some (if option = 0 then incumbent else trial))

def exactPlan {n : ℕ} {State : Type} (G : Graph n) (rng : OrderSource State n)
    (seed : State) (refine : Bool) (nStarts nIterations : ℕ) : Plan G.Code (Part n) :=
  restarts G rng refine nIterations nStarts seed none

/-- Completeness and soundness for the exact weighted-modularity optimizer
model over the entire nonnegative real resolution domain. -/
theorem enumerate_exact_flow {n : ℕ} {State : Type} (G : Graph n) (rng : OrderSource State n)
    (seed : State) (refine : Bool) (nStarts nIterations : ℕ) (p : Part n) :
    p ∈ SeuratRoots.enumerate G (exactPlan G rng seed refine nStarts nIterations) ↔
      ∃ r : ℝ, 0 ≤ r ∧
        (exactPlan G rng seed refine nStarts nIterations).run (fun m => point G.form m r) = p :=
  SeuratRoots.enumerate_exact G _ p

end Louvain.SeuratExact
