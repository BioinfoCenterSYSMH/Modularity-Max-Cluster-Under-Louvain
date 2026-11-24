import MeteredDecision
namespace Louvain
open Finset
namespace Metered

/-- Administrative charges occur once at the point where a table/condition is
    evaluated. Decision continuations can materialize the new vertex-label vector. -/
inductive Script (α : Type) where
  | done (a : α)
  | spent (cost : ℕ) (next : Script α)
  | ask (step : ℚ → Bool → Work (ℕ × Option ℚ)) (next : ℕ → Script α) (update : ℕ → ℕ)

namespace Script
variable {α β : Type}
def bind (p : Script α) (k : α → Script β) : Script β :=
  match p with
  | .done a => k a
  | .spent c q => .spent c (q.bind k)
  | .ask st f upd => .ask st (fun j => (f j).bind k) upd

def eval (p : Script α) (x : ℚ) (b : Bool) : Work (α × Option ℚ) :=
  match p with
  | .done a => ⟨(a,none),0⟩
  | .spent c q =>
    let z := q.eval x b
    ⟨z.val,c+z.steps⟩
  | .ask step next upd =>
    let z := step x b
    let q := (next z.val.1).eval x b
    ⟨(q.val.1,LinearMenu.merge z.val.2 q.val.2),z.steps+upd z.val.1+q.steps+4⟩
end Script

def select (x : ℚ) (b : Bool) (m : Menu Form) := if b then right id m x else pointQ id m x
def edgeMin (x : ℚ) (b : Bool) (m : Menu Form) := if b then LinearMenu.lower (hazards id m x) else none

def expected {α} (p : Plan Form α) (x : ℚ) (b : Bool) : α × Option ℚ :=
  match p with
  | .done a => (a,none)
  | .ask m k =>
    let z := expected (k (select x b m)) x b
    (z.1,LinearMenu.merge (edgeMin x b m) z.2)

theorem expected_point {α} (p : Plan Form α) (x : ℚ) :
    expected p x false = (p.run (fun m => pointQ id m x),none) := by
  induction p with
  | done => rfl
  | ask m k ih => simp [expected,select,edgeMin,Plan.run,ih,LinearMenu.merge]

theorem expected_trace {α} (p : Plan Form α) (x : ℚ) :
    expected p x true = ((p.trace id x).1,LinearMenu.lower (p.trace id x).2) := by
  induction p with
  | done => simp [expected,Plan.trace,LinearMenu.lower]
  | ask m k ih => simp [expected,select,edgeMin,Plan.trace,ih,LinearMenu.lower_union]

/-- A compositional resource certificate. The rate is charged per *actual*
    decision; only non-visit administrative work consumes the residual budget. -/
inductive Refines {α : Type} (rate : ℕ) : Script α → Plan Form α → ℕ → Prop
  | done (a) : Refines rate (.done a) (.done a) 0
  | spent {p q h} (c) : Refines rate p q h → Refines rate (.spent c p) q (c+h)
  | ask {step ks upd m k h}
      (agree : ∀ x b, (step x b : Work (ℕ × Option ℚ)).val = (select x b m,edgeMin x b m))
      (cost : ∀ x b, (step x b).steps+upd (select x b m)+4 ≤ rate)
      (rest : ∀ j, Refines rate (ks j) (k j) h) :
      Refines rate (.ask step ks upd) (.ask m k) h
  | more {p q a b} : Refines rate p q a → a ≤ b → Refines rate p q b

namespace Refines
variable {α β : Type} {rate a b : ℕ} {p : Script α} {q : Plan Form α}

theorem bind (h : Refines rate p q a) {k : α → Script β} {j : α → Plan Form β}
    (hk : ∀ t, Refines rate (k t) (j t) b) :
    Refines rate (p.bind k) (q.bind j) (a+b) := by
  induction h with
  | done x => simpa [Script.bind,Plan.bind] using hk x
  | spent c _ ih => simpa [Script.bind,Nat.add_assoc] using Refines.spent c ih
  | ask ok co _ ih => exact Refines.ask ok co ih
  | more _ h ih => exact ih.more (Nat.add_le_add_right h _)

theorem sound (h : Refines rate p q a) (x : ℚ) (b : Bool) :
    (p.eval x b).val = expected q x b ∧
      (p.eval x b).steps ≤ rate*q.visits (select x b)+a := by
  induction h with
  | done v => simp [Script.eval,expected,Plan.visits]
  | spent c _ ih =>
    simp only [Script.eval]; exact ⟨ih.1, by have := ih.2; omega⟩
  | ask ok co rest ih =>
    simp only [Script.eval,ok x b,expected,Plan.visits,Nat.mul_add,Nat.mul_one]
    rcases ih (select x b _) with ⟨hv, hc⟩
    rw [hv]
    exact ⟨rfl, by have := co x b; omega⟩
  | more _ more ih => exact ⟨ih.1,ih.2.trans (Nat.add_le_add_left more _)⟩
end Refines
end Metered
end Louvain
