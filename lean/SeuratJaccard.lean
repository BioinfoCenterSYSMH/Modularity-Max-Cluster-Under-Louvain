import RawJaccard
import SeuratCost

namespace Louvain.SNN

open Finset SeuratExact
open scoped BigOperators

variable {n k : ℕ} (S : SNN n k)

/-- The unnormalized weighted modularity line on the original rational graph.
Its common normalization is independent of the partition. -/
def seuratRawForm (p : Part n) : Form :=
  ⟨S.rawTotal * (∑ a, ∑ b, if p a = p b then S.rawWeight a b else 0),
    ∑ a, ∑ b, if p a = p b then S.rawDeg a * S.rawDeg b else 0⟩

theorem seurat_full_score_scaling (hk : 0 < k) (p : Part n) (r : ℝ) :
    S.graph.score r p = (scale k : ℝ)^2 * (S.seuratRawForm p).v r := by
  have edges : (Graph.inside p S.graph.weight : ℚ) =
      (scale k : ℚ) * ∑ a, ∑ b, if p a = p b then S.rawWeight a b else 0 := by
    simp only [Graph.inside, Nat.cast_sum, mul_sum, Nat.cast_ite, Nat.cast_zero, S.scale_weight hk,
      mul_ite, mul_zero]
  have nullModel : (Graph.inside p (fun a b => S.graph.deg a * S.graph.deg b) : ℚ) =
      (scale k : ℚ)^2 * ∑ a, ∑ b, if p a = p b then S.rawDeg a * S.rawDeg b else 0 := by
    simp only [Graph.inside, Nat.cast_sum, mul_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul,
      S.scale_deg hk, mul_ite, mul_zero]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    split <;> ring
  simp only [Graph.score, Graph.form, Graph.code, Form.v, seuratRawForm, edges, nullModel,
    S.scale_total hk, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
  ring

/-- The same exact-arithmetic order and ties apply before and after clearing
the Jaccard denominators, including comparisons between different restarts. -/
theorem seurat_raw_score_order (hk : 0 < k) (p q : Part n) (r : ℝ) :
    S.graph.score r p ≤ S.graph.score r q ↔ (S.seuratRawForm p).v r ≤ (S.seuratRawForm q).v r := by
  rw [S.seurat_full_score_scaling hk, S.seurat_full_score_scaling hk]
  have h : 0 < (scale k : ℝ) := by exact_mod_cast scale_posQ k
  exact mul_le_mul_left (pow_pos h 2)

end Louvain.SNN
