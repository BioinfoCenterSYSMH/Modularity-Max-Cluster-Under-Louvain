import JaccardProgram
namespace Louvain
namespace Metered

/-- Uniform in n and in every graph / pruning mask of that size; only k is fixed. -/
abbrev Family (k : ℕ) := (n : ℕ) → SNN n k → ℕ

def Bound {k : ℕ} (d : ℕ) (f : Family k) :=
  ∃ C : ℕ, ∀ n (S : SNN n k), f n S ≤ C*(n+1)^d

namespace Bound
variable {k a b : ℕ} {f g : Family k}
theorem constant (c : ℕ) : Bound (k:=k) 0 (fun _ _ => c) :=
  ⟨c,fun _ _ => by simp⟩
theorem size : Bound (k:=k) 1 (fun n _ => n+1) := ⟨1,fun _ _ => by simp⟩
theorem mono (h : Bound a g) (le : ∀ n (S : SNN n k), f n S ≤ g n S) : Bound a f := by
  obtain ⟨C,hC⟩ := h; exact ⟨C,fun n S => (le n S).trans (hC n S)⟩
theorem up (h : Bound a f) (hab : a ≤ b) : Bound b f := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C,fun n S => (hC n S).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hab))⟩
theorem plus (h : Bound a f) (j : Bound a g) : Bound a (fun n S => f n S+g n S) := by
  obtain ⟨C,hC⟩ := h; obtain ⟨D,hD⟩ := j
  exact ⟨C+D,fun n S => by simpa [Nat.add_mul] using Nat.add_le_add (hC n S) (hD n S)⟩
theorem times (h : Bound a f) (j : Bound b g) : Bound (a+b) (fun n S => f n S*g n S) := by
  obtain ⟨C,hC⟩ := h; obtain ⟨D,hD⟩ := j
  refine ⟨C*D,fun n S => (Nat.mul_le_mul (hC n S) (hD n S)).trans_eq ?_⟩
  rw [pow_add]; ring
theorem scale (c : ℕ) (h : Bound a f) : Bound a (fun n S => c*f n S) := by
  simpa using (constant c).times h
theorem addConst (h : Bound a f) (c : ℕ) : Bound a (fun n S => f n S+c) :=
  h.plus ((constant c).up (Nat.zero_le _))
end Bound

private theorem budget_order {k : ℕ} (hk : 0<k) :
    Bound 6 (fun _ (S : SNN _ k) => S.graph.budget) ∧
    Bound 6 (fun _ (S : SNN _ k) => outer S.graph) := by
  have t : Bound 2 (fun _ (S : SNN _ k) => S.graph.total) := by
    refine ⟨SNN.scale k,fun n S => (S.total_le hk).trans ?_⟩
    nlinarith [Nat.zero_le (SNN.scale k*n)]
  exact ⟨(t.addConst 1).times ((t.times t).addConst 1),
    ((((t.scale 2).addConst 1).times (((t.times t).scale 2).addConst 1)).addConst 1)⟩

private theorem run_order {k : ℕ} (hk : 0<k) : Bound 8 (fun _ (S : SNN _ k) => perRun S.graph) := by
  have h := (budget_order hk).1
  have N := Bound.size (k:=k)
  have hn : Bound (k:=k) 1 (fun n _ => n) := N.mono (fun _ _ => Nat.le_succ _)
  have n3 : Bound (k:=k) 3 (fun n _ => (n+1)^3) := ⟨1,fun _ _ => by simp⟩
  have hsum := (h.plus (hn.up (by decide : 1 ≤ 6))).addConst 1
  have visits : Bound 7 (fun _ (S : SNN _ k) => S.graph.visitBudget) := hn.times hsum
  have aux : Bound 7 (fun _ (S : SNN _ k) => overhead S.graph) :=
    ((n3.scale 50).up (by decide)).plus ((h.addConst 1).times ((hn.scale 4).addConst 1))
  exact ((N.scale 250).times visits).plus (N.times aux)

private def rawList {n k} (S : SNN n k) := scan (script S.graph (input S.graph)) (fuel S.graph) 0

private theorem path_orders {k : ℕ} (hk : 0<k) :
    Bound 14 (fun _ (S : SNN _ k) => (rawList S).steps) ∧
    Bound 6 (fun _ (S : SNN _ k) => (rawList S).val.length) := by
  have outerBound := (budget_order hk).2
  have visits : Bound 6 (fun _ (S : SNN _ k) =>
      Plan.boundaries id (S.graph.localLevels id) (fuel S.graph) 0) :=
    outerBound.mono (fun _ S => S.graph.local_boundaries_le _ _)
  exact ⟨((((run_order hk).scale 2).addConst 8).times visits).mono
    (fun _ S => scan_steps S.graph _ _),
    (visits.scale 2).mono (fun _ S => (scan_length S.graph _ _).le)⟩

private theorem ranking_order {k : ℕ} (hk : 0<k) :
    Bound 13 (fun _ (S : SNN _ k) => (rankAll (input S.graph) (rawList S).val).steps) := by
  have len := (path_orders hk).2
  have hn : Bound (k:=k) 1 (fun n _ => n) := Bound.size.mono (fun _ _ => Nat.le_succ _)
  have n2 : Bound (k:=k) 2 (fun n _ => (n+1)^2) := ⟨1,fun _ _ => by simp⟩
  have square : Bound 12 (fun _ (S : SNN _ k) => (rawList S).val.length^2) := by
    simpa only [pow_two] using len.times len
  exact (((((hn.scale 4).addConst 6).times square).plus
    (((((n2.scale 24).addConst 11).times len)).up (by decide))).addConst 2).mono
    (fun _ S => rank_steps _ _)

/-- Complete frontend cost, from neighbour sets and pruning mask through all
    reachable scored partitions and all maximizers. This counts arithmetic RAM
    operations, including table construction, label updates and deduplication. -/
theorem end_to_end_order {k : ℕ} (hk : 0<k) :
    Bound 14 (fun _ (S : SNN _ k) => (enumerateAndScore S).steps) := by
  have n3 : Bound (k:=k) 3 (fun n _ => (n+1)^3) := ⟨1,fun _ _ => by simp⟩
  have n2 : Bound (k:=k) 2 (fun n _ => (n+1)^2) := ⟨1,fun _ _ => by simp⟩
  have decoded : Bound 3 (fun _ (S : SNN _ k) => (inputGraph S).steps) :=
    (n3.scale (32*(k+1))).mono (fun _ S => inputGraph_steps S)
  have prep : Bound 2 (fun _ (S : SNN _ k) => (prepare S.graph).steps) :=
    (n2.scale 5).mono (fun _ S => prepare_steps S.graph)
  have run := (path_orders hk).1
  have ranking := (ranking_order hk).up (by decide : 13 ≤ 14)
  have h := (decoded.up (by decide : 3 ≤ 14)).plus ((prep.up (by decide : 2 ≤ 14)).plus
    ((((Bound.constant (k:=k) 12).up (by decide : 0 ≤ 14)).plus run).plus ranking))
  apply h.mono
  intro n S
  simp only [enumerateAndScore,Work.thenDo,inputGraph_val]
  rfl

/-- A standard asymptotic formulation, with a constant independent of n and S. -/
theorem arithmetic_n14 (k : ℕ) (hk : 0<k) :
    ∃ C : ℕ, ∀ n (S : SNN n k), 0<n → (enumerateAndScore S).steps ≤ C*n^14 := by
  obtain ⟨D,hD⟩ := end_to_end_order hk
  refine ⟨D*2^14,fun n S hn => (hD n S).trans ?_⟩
  have h : n+1 ≤ 2*n := by omega
  simpa only [Nat.mul_pow,Nat.mul_assoc] using Nat.mul_le_mul_left D (Nat.pow_le_pow_left h 14)

end Metered
end Louvain
#print axioms Louvain.Metered.arithmetic_n14
#print axioms Louvain.Metered.scores_exact
#print axioms Louvain.Metered.best_exact
