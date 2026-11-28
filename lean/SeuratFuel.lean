import Mathlib.Data.Nat.Basic

namespace Louvain.Seurat

/-- Each rank increase can reset the stability counter, so allot one full
cycle per remaining rank and one final cycle. -/
def visitBudget (period ceiling rank stable : ℕ) : ℕ :=
  (ceiling - rank) * period + (period - stable)

theorem visitBudget_lt {period ceiling rank nextRank stable : ℕ}
    (active : stable < period) (bounded : nextRank ≤ ceiling) :
    (nextRank = rank →
      visitBudget period ceiling nextRank (stable + 1) <
        visitBudget period ceiling rank stable) ∧
    (rank < nextRank →
      visitBudget period ceiling nextRank 1 < visitBudget period ceiling rank stable) := by
  constructor
  · intro same
    subst nextRank
    unfold visitBudget
    omega
  · intro rises
    have space : ceiling - nextRank + 1 ≤ ceiling - rank := by omega
    have slots := Nat.mul_le_mul_right period space
    rw [Nat.add_mul, Nat.one_mul] at slots
    unfold visitBudget
    omega

theorem visitBudget_le_fuel (period ceiling rank stable : ℕ) :
    visitBudget period ceiling rank stable ≤ (ceiling + 1) * period := by
  unfold visitBudget
  rw [Nat.add_mul, Nat.one_mul]
  have first := Nat.mul_le_mul_right period (Nat.sub_le ceiling rank)
  have second := Nat.sub_le period stable
  omega

/-- Rank increase is allowed to depend on the node in the fixed cyclic visit
order. The cursor is separate from the mutable clustering state. -/
structure LocalResult (σ : Type) where
  state : σ
  stable : ℕ
  visits : ℕ

/-- A bounded local moving loop. After a changed label, the C++ optimizer
sets its stability counter to one. Exhaustion and stability remain separately
observable so the fuel sufficiency theorem rules out active exhaustion. -/
def localRun {σ : Type} [DecidableEq σ] (step : ℕ → σ → σ) (period : ℕ) :
    ℕ → ℕ → ℕ → σ → LocalResult σ
  | 0, _, stable, state => ⟨state, stable, 0⟩
  | fuel + 1, cursor, stable, state =>
    if period ≤ stable then ⟨state, stable, 0⟩ else
      let next := step cursor state
      let quiet := if next = state then stable + 1 else 1
      let rest := localRun step period fuel (cursor + 1) quiet next
      { rest with visits := rest.visits + 1 }

/-- Operational semantics with no fuel. A finite execution must end with
enough stable visits. -/
inductive LocalQuiesces {σ : Type} [DecidableEq σ] (step : ℕ → σ → σ) (period : ℕ) :
    ℕ → ℕ → σ → LocalResult σ → Prop where
  | stop {cursor stable state} (quiet : period ≤ stable) :
    LocalQuiesces step period cursor stable state ⟨state, stable, 0⟩
  | visit {cursor stable state rest} (active : stable < period)
    (tail : LocalQuiesces step period (cursor + 1)
      (if step cursor state = state then stable + 1 else 1) (step cursor state) rest) :
    LocalQuiesces step period cursor stable state { rest with visits := rest.visits + 1 }

theorem localRun_quiesces_of_finished {σ : Type} [DecidableEq σ] (step : ℕ → σ → σ)
    (period fuel cursor stable : ℕ) (state : σ)
    (finished : period ≤ (localRun step period fuel cursor stable state).stable) :
    LocalQuiesces step period cursor stable state (localRun step period fuel cursor stable state) := by
  induction fuel generalizing cursor stable state with
  | zero => exact LocalQuiesces.stop finished
  | succ fuel ih =>
    by_cases quiet : period ≤ stable
    · simp only [localRun, if_pos quiet]
      exact LocalQuiesces.stop quiet
    · simp only [localRun, if_neg quiet] at finished ⊢
      exact LocalQuiesces.visit (Nat.lt_of_not_ge quiet) (ih _ _ _ finished)

theorem LocalQuiesces.unique {σ : Type} [DecidableEq σ] {step : ℕ → σ → σ}
    {period cursor stable : ℕ} {state : σ} {a b : LocalResult σ}
    (left : LocalQuiesces step period cursor stable state a)
    (right : LocalQuiesces step period cursor stable state b) : a = b := by
  induction left generalizing b with
  | stop quiet =>
    cases right with
    | stop => rfl
    | visit active _ => omega
  | visit active _ ih =>
    cases right with
    | stop quiet => omega
    | visit _ tail => rw [ih tail]

theorem localRun_spec {σ : Type} [DecidableEq σ] (step : ℕ → σ → σ)
    (period ceiling : ℕ) (rank : σ → ℕ) (bounded : ∀ state, rank state ≤ ceiling)
    (rises : ∀ cursor state, step cursor state ≠ state → rank state < rank (step cursor state))
    (fuel cursor stable : ℕ) (state : σ)
    (enough : visitBudget period ceiling (rank state) stable ≤ fuel) :
    let result := localRun step period fuel cursor stable state
    period ≤ result.stable ∧ result.visits ≤ visitBudget period ceiling (rank state) stable := by
  induction fuel generalizing cursor stable state with
  | zero =>
    have quiet : period ≤ stable := by
      unfold visitBudget at enough
      omega
    simpa [localRun] using quiet
  | succ fuel ih =>
    by_cases quiet : period ≤ stable
    · simp [localRun, quiet]
    · have active : stable < period := Nat.lt_of_not_ge quiet
      let next := step cursor state
      by_cases same : next = state
      · have less := (visitBudget_lt active (bounded next)).1 (congrArg rank same)
        have rest := ih (cursor + 1) (stable + 1) next (by omega)
        change step cursor state = state at same
        simp only [localRun, if_neg quiet, if_pos same]
        exact ⟨rest.1, Nat.le_trans (Nat.succ_le_succ rest.2) less⟩
      · have less := (visitBudget_lt active (bounded next)).2 (rises cursor state same)
        have rest := ih (cursor + 1) 1 next (by omega)
        change step cursor state ≠ state at same
        simp only [localRun, if_neg quiet, if_neg same]
        exact ⟨rest.1, Nat.le_trans (Nat.succ_le_succ rest.2) less⟩

/-- A uniform bound that depends on the rank alphabet and cycle length,
starting from zero stable visits. -/
theorem localRun_uniform {σ : Type} [DecidableEq σ] (step : ℕ → σ → σ)
    (period ceiling : ℕ) (rank : σ → ℕ) (bounded : ∀ state, rank state ≤ ceiling)
    (rises : ∀ cursor state, step cursor state ≠ state → rank state < rank (step cursor state))
    (state : σ) :
    let fuel := (ceiling + 1) * period
    let result := localRun step period fuel 0 0 state
    period ≤ result.stable ∧ result.visits ≤ fuel := by
  let fuel := (ceiling + 1) * period
  have bound := visitBudget_le_fuel period ceiling (rank state) 0
  have spec := localRun_spec step period ceiling rank bounded rises fuel 0 0 state bound
  exact ⟨spec.1, Nat.le_trans spec.2 bound⟩

/-- The uncapped operational loop exists uniquely within the uniform bound. -/
theorem localQuiesces_total_unique {σ : Type} [DecidableEq σ] (step : ℕ → σ → σ)
    (period ceiling : ℕ) (rank : σ → ℕ) (bounded : ∀ state, rank state ≤ ceiling)
    (rises : ∀ cursor state, step cursor state ≠ state → rank state < rank (step cursor state))
    (state : σ) :
    ∃ result, LocalQuiesces step period 0 0 state result ∧ result.visits ≤ (ceiling + 1) * period ∧
      ∀ other, LocalQuiesces step period 0 0 state other → other = result := by
  let fuel := (ceiling + 1) * period
  have spec := localRun_uniform step period ceiling rank bounded rises state
  have run := localRun_quiesces_of_finished step period fuel 0 0 state spec.1
  exact ⟨localRun step period fuel 0 0 state, run, spec.2, fun _ proof => proof.unique run⟩

end Louvain.Seurat
