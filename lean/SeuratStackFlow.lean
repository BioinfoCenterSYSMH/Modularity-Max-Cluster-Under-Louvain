import SeuratFlow

namespace Louvain.SeuratExact

open Finset

/-- The clustering respects the coarsened units, and the free-label stack is
their current complement inside the level's label space. -/
structure StackStateValid {n : ℕ} (u : Part n) (state : LocalState n) : Prop where
  respects : Graph.respects u state.part
  stack : ValidStack (Graph.count u) (univ.image state.part) state.free

theorem initial_stack_state_valid {n : ℕ} (u p : Part n) (hp : Graph.respects u p)
    (hlabels : ∀ a, (p a).val < Graph.count u) :
    StackStateValid u ⟨p, initialFree (Graph.count u) p, false⟩ :=
  ⟨hp, initialStack_valid _ p hlabels⟩

/-- Both guards used to totalize `localVisit` are unreachable on a valid state. -/
theorem local_visit_has_valid_head {n : ℕ} (u : Part n) (a : Fin n) (state : LocalState n)
    (hs : StackStateValid u state) :
    ∃ empty tail, prepareFree u a state = empty :: tail ∧
      empty ∉ remaining u state.part a ∧
      (state.part a ∉ remaining u state.part a → empty = state.part a) := by
  obtain ⟨empty, tail, h⟩ := removeSource_has_head u state.part a state.free hs.respects hs.stack
  have hvalid := removeSource_head _ u state.part a empty state.free tail hs.respects hs.stack h
  exact ⟨empty, tail, h, hvalid⟩

/-- On valid states, the guarded plan performs the same stack update as remove,
then reinsert. If the label stays put, remove and reinsert restore the old stack. -/
theorem local_visit_exact_update {n : ℕ} (G : Graph n) (u : Part n) (a : Fin n)
    (r : ℝ) (state : LocalState n) (hs : StackStateValid u state) :
    ∃ empty tail, prepareFree u a state = empty :: tail ∧
      (let q := (visit G u state.part a empty).run (G.atReal r)
       (localVisit G u a state).run (G.atReal r) =
         ⟨q, if q a = empty then tail else empty :: tail,
           if q = state.part then state.changed else true⟩) := by
  obtain ⟨empty, tail, hhead, hempty, hsame⟩ := local_visit_has_valid_head u a state hs
  refine ⟨empty, tail, hhead, ?_⟩
  let q := (visit G u state.part a empty).run (G.atReal r)
  change (localVisit G u a state).run (G.atReal r) =
    ⟨q, if q a = empty then tail else empty :: tail,
      if q = state.part then state.changed else true⟩
  simp only [localVisit, hhead, if_neg hempty, Plan.run_bind]
  change ((if q = state.part then Plan.done state else
    Plan.done ⟨q, if q a = empty then tail else empty :: tail, true⟩).run (G.atReal r)) = _
  by_cases hq : q = state.part
  · simp only [hq, if_pos rfl, Plan.run]
    by_cases hoccupied : state.part a ∈ remaining u state.part a
    · have hne : state.part a ≠ empty := fun he => hempty (he ▸ hoccupied)
      have freeEq : state.free = empty :: tail := by simpa [prepareFree, hoccupied] using hhead
      cases state
      simp [Plan.run, hne]
      exact freeEq
    · have he : empty = state.part a := hsame hoccupied
      have freeEq : state.free = tail := by
        have hcons : state.part a :: state.free = empty :: tail := by
          simpa [prepareFree, hoccupied] using hhead
        exact (List.cons.inj hcons).2
      cases state
      simp [Plan.run, he]
      exact freeEq
  · simp [hq, Plan.run]

theorem local_visit_preserves_stack {n : ℕ} (G : Graph n) (u : Part n) (a : Fin n)
    (r : ℝ) (state : LocalState n) (hs : StackStateValid u state) :
    StackStateValid u ((localVisit G u a state).run (G.atReal r)) := by
  obtain ⟨empty, tail, hhead, hempty, _⟩ := local_visit_has_valid_head u a state hs
  have hrest := removeSource_valid _ u state.part a state.free hs.respects hs.stack
  change ValidStack _ _ (prepareFree u a state) at hrest
  rw [hhead] at hrest
  simp only [localVisit, hhead, if_neg hempty, Plan.run_bind]
  let q := (visit G u state.part a empty).run (G.atReal r)
  change StackStateValid u ((if q = state.part then Plan.done state else
    Plan.done ⟨q, if q a = empty then tail else empty :: tail, true⟩).run (G.atReal r))
  by_cases hq : q = state.part
  · simpa [hq, Plan.run] using hs
  · simp only [if_neg hq, Plan.run]
    exact ⟨visit_respects G u state.part a empty hs.respects _,
      visit_stack_valid G _ u state.part a empty r tail hrest⟩

theorem ordered_visit_preserves_stack {n : ℕ} (G : Graph n) (u : Part n)
    (order : List (Fin n)) (cursor : ℕ) (r : ℝ) (state : LocalState n)
    (hs : StackStateValid u state) :
    StackStateValid u ((orderedVisit G u order cursor state).run (G.atReal r)) := by
  unfold orderedVisit
  split
  · exact hs
  · exact local_visit_preserves_stack G u _ r state hs

theorem local_loop_preserves_stack {n : ℕ} (G : Graph n) (u : Part n)
    (order : List (Fin n)) (fuel cursor stable : ℕ) (r : ℝ) (state : LocalState n)
    (hs : StackStateValid u state) :
    StackStateValid u ((localLoop G u order fuel cursor stable state).run (G.atReal r)) := by
  induction fuel generalizing cursor stable state with
  | zero => exact hs
  | succ fuel ih =>
    by_cases quiet : order.length ≤ stable
    · simpa [localLoop, if_pos quiet, Plan.run] using hs
    · simp only [localLoop, if_neg quiet, Plan.run_bind]
      exact ih _ _ _ (ordered_visit_preserves_stack G u order cursor r state hs)

theorem local_phase_preserves_units {n : ℕ} {State : Type} (G : Graph n)
    (rng : OrderSource State n) (u p : Part n) (rngState : State) (r : ℝ)
    (hp : Graph.respects u p) (hlabels : ∀ a, (p a).val < Graph.count u) :
    Graph.respects u ((localPhase G rng u p rngState).run (G.atReal r)).1.1 := by
  have hm : (rng.next rngState (representatives u)).1.length = Graph.count u :=
    (rng.perm rngState (representatives u)).length_eq.trans (representatives_length_eq u)
  unfold localPhase
  simp only [Plan.run_bind, Plan.run, hm]
  exact compact_respects (local_loop_preserves_stack G u _ _ 0 0 r _
    (initial_stack_state_valid u p hp hlabels)).respects

theorem compact_lt_own_count {n : ℕ} (p : Part n) (a : Fin n) :
    (compact p a).val < Graph.count (compact p) := by
  rw [compact_count]
  change ((units p).filter (· < p a)).card < (units p).card
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro same
  have witness : p a ∈ units p := by simp [units]
  rw [← same] at witness
  exact (lt_irrefl _) (mem_filter.mp witness).2

theorem count_le_units {n : ℕ} {u p : Part n} (hp : Graph.respects u p) :
    Graph.count p ≤ Graph.count u := by
  classical
  let representative (label : Fin n) : Fin n :=
    if h : ∃ a, u a = label then h.choose else label
  change (units p).card ≤ (units u).card
  apply card_le_card_of_surjOn (p ∘ representative)
  intro c hc
  obtain ⟨a, _, ha⟩ := mem_image.mp hc
  have hrepr : u (representative (u a)) = u a := by
    unfold representative
    split
    · rename_i h
      exact h.choose_spec
    · rename_i h
      exact (h ⟨a, rfl⟩).elim
  exact ⟨u a, mem_image_of_mem _ (mem_univ _), (hp _ _ hrepr).trans ha⟩

theorem local_phase_compacted {n : ℕ} {State : Type} (G : Graph n)
    (rng : OrderSource State n) (u p : Part n) (rngState : State) (r : ℝ) :
    let q := ((localPhase G rng u p rngState).run (G.atReal r)).1.1
    ∀ a, (q a).val < Graph.count q := by
  unfold localPhase
  simp only [Plan.run_bind, Plan.run]
  exact compact_lt_own_count _

/-- All recursive levels and the refinement use valid label ranges. -/
theorem multilevel_preserves_level_input {n : ℕ} {State : Type} (G : Graph n)
    (rng : OrderSource State n) (refine : Bool) (r : ℝ) (fuel : ℕ)
    (u p : Part n) (rngState : State) (hp : Graph.respects u p)
    (hlabels : ∀ a, (p a).val < Graph.count u) :
    let q := ((multilevel G rng refine fuel u p rngState).run (G.atReal r)).1.1
    Graph.respects u q ∧ ∀ a, (q a).val < Graph.count u := by
  induction fuel generalizing u p rngState with
  | zero => exact ⟨hp, hlabels⟩
  | succ fuel ih =>
    by_cases hstop : Graph.count u ≤ 1
    · simpa [multilevel, hstop, Plan.run] using And.intro hp hlabels
    simp only [multilevel, if_neg hstop, Plan.run_bind]
    let result := (localPhase G rng u p rngState).run (G.atReal r)
    let moved := result.1.1
    have hres : Graph.respects u moved := local_phase_preserves_units G rng u p rngState r hp hlabels
    have hm : ∀ a, (moved a).val < Graph.count moved := local_phase_compacted G rng u p rngState r
    have hm' : ∀ a, (moved a).val < Graph.count u :=
      fun a => (hm a).trans_le (count_le_units hres)
    by_cases hcontract : Graph.count moved < Graph.count u
    · have htest := hcontract
      dsimp only [moved, result] at htest
      simp only [if_pos htest, Plan.run_bind]
      let coarseResult := (multilevel G rng refine fuel moved moved result.2).run (G.atReal r)
      let coarse := coarseResult.1.1
      have hc : Graph.respects moved coarse ∧ ∀ a, (coarse a).val < Graph.count moved :=
        ih moved moved result.2 (Graph.respects_self moved) hm
      have hcu : Graph.respects u coarse := fun a b hab => hc.1 a b (hres a b hab)
      have hcu' : ∀ a, (coarse a).val < Graph.count u := fun a => (hc.2 a).trans hcontract
      cases hcoarse : coarseResult.1.2 with
      | false =>
        dsimp only [coarseResult, moved, result] at hcoarse
        simpa [hcoarse, Plan.run] using And.intro hres hm'
      | true =>
        dsimp only [coarseResult, moved, result] at hcoarse
        cases refine with
        | false => simpa [hcoarse, Plan.run] using And.intro hcu hcu'
        | true =>
          simp only [hcoarse, if_true, Plan.run_bind, Plan.run]
          have hru := local_phase_preserves_units G rng u coarse coarseResult.2 r hcu hcu'
          have hrl := local_phase_compacted G rng u coarse coarseResult.2 r
          exact ⟨hru, fun a => (hrl a).trans_le (count_le_units hru)⟩
    · dsimp only [moved, result] at hcontract
      simpa [hcontract, Plan.run] using And.intro hres hm'

theorem singleton_count (n : ℕ) : Graph.count (id : Part n) = n := by
  simp [Graph.count]

/-- Any starting partition is valid on the original singleton units, including
those carried over by the next outer iteration. -/
theorem singleton_input_valid {n : ℕ} (p : Part n) :
    Graph.respects (id : Part n) p ∧ ∀ a, (p a).val < Graph.count (id : Part n) := by
  refine ⟨fun a b hab => congrArg p hab, fun a => ?_⟩
  rw [singleton_count]
  exact (p a).isLt

end Louvain.SeuratExact
