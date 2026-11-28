import SeuratFlow

namespace Louvain.SeuratExact

open SeuratRoots

variable {n : ℕ} {State : Type} (G : Graph n) (choose : Menu G.Code → ℕ)

private theorem localVisit_entries (u : Part n) (a : Fin n) (state : LocalState n) :
    menuEntries G choose (localVisit G u a state) ≤ n + 1 := by
  cases hf : prepareFree u a state with
  | nil => simp [localVisit, hf, menuEntries]
  | cons empty tail =>
    by_cases he : empty ∈ remaining u state.part a
    · simp [localVisit, hf, he, menuEntries]
    simp only [localVisit, hf, if_neg he, menuEntries_bind]
    have menuBound : (menu G u state.part a empty).options.card ≤ n + 1 := by
      unfold menu
      apply (Finset.card_insert_le _ _).trans
      apply Nat.add_le_add_right
      exact Finset.card_image_le.trans (by simpa using Finset.card_le_univ (targets G u state.part a))
    split <;> simpa [visit, menuEntries] using menuBound

private theorem orderedVisit_entries (u : Part n) (order : List (Fin n)) (cursor : ℕ)
    (state : LocalState n) : menuEntries G choose (orderedVisit G u order cursor state) ≤ n + 1 := by
  unfold orderedVisit
  split
  · simp [menuEntries]
  · exact localVisit_entries G choose u _ state

private theorem localLoop_entries (u : Part n) (order : List (Fin n)) (fuel cursor stable : ℕ)
    (state : LocalState n) :
    menuEntries G choose (localLoop G u order fuel cursor stable state) ≤ fuel * (n + 1) := by
  induction fuel generalizing cursor stable state with
  | zero => simp [localLoop, menuEntries]
  | succ fuel ih =>
    by_cases h : order.length ≤ stable
    · simp [localLoop, if_pos h, menuEntries]
    simp only [localLoop, if_neg h, menuEntries_bind, Nat.succ_mul]
    calc _ ≤ (n + 1) + fuel * (n + 1) := Nat.add_le_add (orderedVisit_entries G choose u order cursor state) (ih _ _ _)
         _ = _ := Nat.add_comm _ _

def phaseEntries : ℕ := localFuel G * (n + 1)

private theorem localPhase_entries (rng : OrderSource State n) (u p : Part n) (s : State) :
    menuEntries G choose (localPhase G rng u p s) ≤ phaseEntries G := by
  unfold localPhase
  rcases rng.next s (representatives u) with ⟨order, next⟩
  simpa [menuEntries, phaseEntries] using
    localLoop_entries G choose u order (localFuel G) 0 0 ⟨p, initialFree order.length p, false⟩

private theorem multilevel_entries (rng : OrderSource State n) (refine : Bool) (fuel : ℕ)
    (u p : Part n) (s : State) :
    menuEntries G choose (multilevel G rng refine fuel u p s) ≤ fuel * (2 * phaseEntries G) := by
  induction fuel generalizing u p s with
  | zero => simp [multilevel, menuEntries]
  | succ fuel ih =>
    by_cases hu : Graph.count u ≤ 1
    · simp [multilevel, hu, menuEntries]
    simp only [multilevel, if_neg hu, menuEntries_bind]
    rw [Nat.succ_mul fuel (2 * phaseEntries G)]
    have hlocal := localPhase_entries G choose rng u p s
    rcases (localPhase G rng u p s).run choose with ⟨⟨moved, didMove⟩, afterLocal⟩
    simp only
    split
    · rw [menuEntries_bind]
      have hcoarse := ih moved moved afterLocal
      rcases (multilevel G rng refine fuel moved moved afterLocal).run choose with
        ⟨⟨coarse, didCoarse⟩, afterCoarse⟩
      simp only
      have hrefine := localPhase_entries G choose rng u coarse afterCoarse
      cases didCoarse <;> cases refine <;> simp [menuEntries] <;> omega
    · simp only [menuEntries]
      omega

private theorem iterations_entries (rng : OrderSource State n) (refine : Bool) (count : ℕ)
    (p : Part n) (s : State) : menuEntries G choose (iterations G rng refine count p s) ≤
    count * (n * (2 * phaseEntries G)) := by
  induction count generalizing p s with
  | zero => simp [iterations, menuEntries]
  | succ count ih =>
    simp only [iterations, menuEntries_bind]
    rw [Nat.succ_mul count (n * (2 * phaseEntries G))]
    have hpass := multilevel_entries G choose rng refine n id p s
    rcases (multilevel G rng refine n id p s).run choose with ⟨⟨part, changed⟩, next⟩
    simp only
    split
    · exact (Nat.add_le_add hpass (ih _ _)).trans_eq (Nat.add_comm _ _)
    · simp only [menuEntries, Nat.add_zero]
      omega

def runEntries (starts iterations : ℕ) : ℕ := starts * (2 + iterations * (n * (2 * phaseEntries G)))

private theorem restarts_entries (rng : OrderSource State n) (refine : Bool) (nIterations nStarts : ℕ)
    (s : State) (best : Option (Part n)) :
    menuEntries G choose (restarts G rng refine nIterations nStarts s best) ≤ runEntries G nStarts nIterations := by
  induction nStarts generalizing s best with
  | zero => simp [restarts, menuEntries, runEntries]
  | succ starts ih =>
    simp only [restarts, menuEntries_bind]
    have htrial := iterations_entries G choose rng refine nIterations id s
    rcases (iterations G rng refine nIterations id s).run choose with ⟨trial, next⟩
    cases best with
    | none =>
      have hr := ih next (some trial)
      simp only [runEntries] at hr ⊢
      rw [Nat.succ_mul starts (2 + nIterations * (n * (2 * phaseEntries G)))]
      omega
    | some incumbent =>
      let winner := if choose (incumbentMenu G incumbent trial) = 0 then incumbent else trial
      have hr := ih next (some winner)
      simp only [menuEntries, runEntries] at hr ⊢
      rw [Nat.succ_mul starts (2 + nIterations * (n * (2 * phaseEntries G)))]
      have hm : (incumbentMenu G incumbent trial).options.card = 2 := by simp [incumbentMenu]
      rw [hm]
      change _ + (2 + menuEntries G choose (restarts G rng refine nIterations starts next (some winner))) ≤ _
      omega

theorem exactPlan_entries (rng : OrderSource State n) (seed : State) (refine : Bool)
    (nStarts nIterations : ℕ) : menuEntries G choose (exactPlan G rng seed refine nStarts nIterations) ≤
    runEntries G nStarts nIterations :=
  restarts_entries G choose rng refine nIterations nStarts seed none

end Louvain.SeuratExact

namespace Louvain.SNN

open SeuratExact SeuratRoots

/-- Polynomial bound in cell count for the actual adaptive scan, measured in
candidate entries at comparison menus. Stage limits and `k` are parameters of
the constant. This is an upper bound, not a measured implementation runtime. -/
theorem seurat_exact_polynomial {n k : ℕ} {State : Type} (S : SNN n k) (hk : 0 < k)
    (rng : OrderSource State n) (seed : State) (refine : Bool) (starts iterations : ℕ) :
    scanEntries S.graph (exactPlan S.graph rng seed refine starts iterations) (attemptBudget S.graph) 0 ≤
      2 * (seuratAttemptsConstant k * starts * (2 + 2 * iterations * (seuratScoreConstant k + 2))) *
        (n + 1)^18 := by
  have meter := enumeration_entries_le S.graph (exactPlan S.graph rng seed refine starts iterations)
    (runEntries S.graph starts iterations)
    (fun r _ => exactPlan_entries S.graph (fun m => point S.graph.form m r) rng seed refine starts iterations)
  have poly := seurat_fixed_k_control_budget S hk starts iterations 2
  apply meter.trans
  calc 2 * runEntries S.graph starts iterations * attemptBudget S.graph =
      2 * (attemptBudget S.graph * (starts * (2 + iterations *
        (2 * n * (((S.graph.budget + 1) * (n + 1) * (n * n + 1) + 1) * n) * (n + 1))))) := by
          simp only [runEntries, phaseEntries, localFuel, localCeiling]
          ring
       _ ≤ _ := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 poly

#print axioms seurat_exact_polynomial

end Louvain.SNN
