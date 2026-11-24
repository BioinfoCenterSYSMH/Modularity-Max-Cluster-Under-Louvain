import Graph
import Mathlib.Data.Nat.Factorial.Basic

namespace Louvain
open Finset
open scoped BigOperators
/-- Equal-sized neighbor lists and an optional symmetric edge-pruning mask. -/
structure SNN (n k : ℕ) where
  neighbors : Fin n → Finset (Fin n)
  size_eq : ∀ i, (neighbors i).card = k
  keep : Fin n → Fin n → Bool
  keep_symm : ∀ i j, keep i j = keep j i

namespace SNN
variable {n k : ℕ} (S : SNN n k)
def overlap (i j : Fin n) := (S.neighbors i ∩ S.neighbors j).card
theorem overlap_le (i j : Fin n) : S.overlap i j ≤ k := by
  exact (card_le_card inter_subset_left).trans_eq (S.size_eq i)

def scale (k : ℕ) := (2*k).factorial
def edge (i j : Fin n) :=
  if i ≠ j ∧ S.keep i j = true then
    S.overlap i j * (scale k / (2*k-S.overlap i j)) else 0
def graph : Graph n where
  weight := S.edge
  symm i j := by simp only [edge,overlap,inter_comm (S.neighbors i) (S.neighbors j),S.keep_symm i j,ne_comm]
  loopless i := by simp [edge]

theorem scaling (hk : 0 < k) (i j : Fin n) :
    (S.edge i j : ℚ) =
      (scale k : ℚ) * (if i ≠ j ∧ S.keep i j = true then
        (S.overlap i j : ℚ) / ((2*k - S.overlap i j : ℕ) : ℚ) else 0) := by
  unfold edge
  split
  · have h := S.overlap_le i j
    have hd : 0 < 2*k - S.overlap i j := by omega
    have dvd : (2*k - S.overlap i j) ∣ scale k := Nat.dvd_factorial hd (Nat.sub_le _ _)
    have he := Nat.div_mul_cancel dvd
    push_cast
    rw [mul_div_assoc', eq_div_iff (by exact_mod_cast hd.ne' : ((2*k-S.overlap i j : ℕ) : ℚ) ≠ 0)]
    have heq : ((scale k / (2*k-S.overlap i j) : ℕ) : ℚ) * ((2*k-S.overlap i j : ℕ) : ℚ) = scale k := by exact_mod_cast he
    rw [mul_assoc,heq,mul_comm]
  · simp

theorem edge_le (hk : 0 < k) (i j : Fin n) : S.edge i j ≤ scale k := by
  have h := S.overlap_le i j
  unfold edge; split
  · have hd : 0 < 2*k - S.overlap i j := by omega
    have dvd : (2*k - S.overlap i j) ∣ scale k := Nat.dvd_factorial hd (Nat.sub_le _ _)
    calc
      _ ≤ (2*k-S.overlap i j) * (scale k / (2*k-S.overlap i j)) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = _ := Nat.mul_div_cancel' dvd
  · omega

theorem total_le (hk : 0 < k) : S.graph.total ≤ n * (n * scale k) := by
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, scale k := by
      apply sum_le_sum; intro i _; apply sum_le_sum; intro j _; exact S.edge_le hk i j
    _ = _ := by simp

/-- Upper bounds for the search fuel depend polynomially on n for fixed k;
these deliberately coarse bounds do not express bit-operation complexity. -/
theorem alphabet_bound (hk : 0 < k) :
    let B := n * (n * scale k)
    Fintype.card S.graph.Code ≤ (B+1)*(B*B+1) := by
  have h := S.total_le hk
  change Fintype.card (Fin _ × Fin _) ≤ _
  simp only [Fintype.card_prod,Fintype.card_fin]
  exact Nat.mul_le_mul (Nat.succ_le_succ h) (Nat.succ_le_succ (Nat.mul_le_mul h h))

theorem enumeration_fuel_bound (hk : 0 < k) :
    let B := n * (n * scale k)
    let H := (B+1)*(B*B+1)
    Fintype.card S.graph.Code * Fintype.card S.graph.Code + 1 ≤ H*H + 1 :=
  Nat.succ_le_succ (Nat.mul_le_mul (S.alphabet_bound hk) (S.alphabet_bound hk))

/-- Final statement for fixed-k, possibly pruned, Jaccard SNN graphs.
The reference execution starts with singleton cells and has no iteration cap. -/
theorem no_omissions_iff (p : Part n) :
    p ∈ S.graph.allOutputs ↔ ∃ r : ℝ, 0 ≤ r ∧ S.graph.Returns r id p :=
  S.graph.allOutputs_exact p

end SNN
end Louvain
