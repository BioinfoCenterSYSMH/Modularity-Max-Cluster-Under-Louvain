import ArithmeticBound

namespace Louvain.Metered
open Finset
open scoped BigOperators
variable {n k : ℕ}

/-- Score the unscaled Jaccard graph, in the standard ordered-pair convention.
    As usual, interpretation as modularity requires positive total edge weight. -/
def rawClassical (S : SNN n k) (p : Part n) : ℚ :=
  let a := ∑ i, ∑ j, if p i=p j then S.rawWeight i j else 0
  let b := ∑ i, ∑ j, if p i=p j then S.rawDeg i*S.rawDeg j else 0
  (S.rawTotal*a-b)/(S.rawTotal*S.rawTotal)

private theorem liftInside {s : ℚ} (p : Part n) (w : Fin n → Fin n → ℕ)
    (v : Fin n → Fin n → ℚ) (h : ∀ i j, (w i j:ℚ)=s*v i j) :
    ((∑ i, ∑ j, if p i=p j then w i j else 0 : ℕ):ℚ) =
      s*(∑ i, ∑ j, if p i=p j then v i j else 0) := by
  simp only [Nat.cast_sum,Finset.mul_sum]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  split <;> simp_all

theorem classical_raw (S : SNN n k) (hk : 0<k) (p : Part n) :
    classical (input S.graph) p = rawClassical S p := by
  let s : ℚ := SNN.scale k
  have hs : s ≠ 0 := ne_of_gt (SNN.scale_posQ k)
  have ha := liftInside p S.graph.weight S.rawWeight (S.scale_weight hk)
  have hb := liftInside (s:=s*s) p (fun i j => S.graph.deg i*S.graph.deg j)
      (fun i j => S.rawDeg i*S.rawDeg j) (fun i j => by
        simp only [Nat.cast_mul,S.scale_deg hk]; dsimp [s]; ring)
  simp only [classical,input,prepare_val,rawClassical,Nat.cast_mul,ha,hb,S.scale_total hk]
  by_cases ht : S.rawTotal = 0
  · simp [ht]
  · dsimp [s] at hs ⊢; field_simp; ring

theorem scores_raw_exact (S : SNN n k) (hk : 0<k) (p : Part n) (q : ℚ) :
    (p,q) ∈ (enumerateAndScore S).val.scores ↔
    (∃ r : ℝ, 0 ≤ r ∧ S.RawReturns r id p) ∧ q = rawClassical S p := by
  rw [scores_exact S hk,classical_raw S hk]

theorem distinct_scores (S : SNN n k) :
    ((enumerateAndScore S).val.scores.map Prod.fst).Nodup := by
  rw [program_contents]; simp only [rankAll,Work.thenDo,Work.ret,Work.mapL_val,List.map_map]
  change (List.map id _).Nodup
  rw [List.map_id]
  exact (unique_spec _).1

end Louvain.Metered
#print axioms Louvain.Metered.scores_raw_exact
#print axioms Louvain.Metered.distinct_scores
