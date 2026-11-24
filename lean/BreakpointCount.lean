import RawJaccard

namespace Louvain
open Finset

namespace Plan
variable {ι α : Type} (f : ι → Form)

/-- Number of boundary points actually visited by the recursion in collect. -/
def boundaries (p : Plan ι α) : ℕ → ℚ → ℕ
  | 0, _ => 0
  | fuel+1, x =>
    let s := (p.trace f x).2
    1 + if h : s.Nonempty then boundaries p fuel (s.min' h) else 0

theorem boundaries_le {p : Plan ι α} (s : Finset ℚ)
    (cover : ∀ x, (p.trace f x).2 ⊆ s) (fuel : ℕ) (x : ℚ) :
    boundaries f p fuel x ≤ (above s x).card + 1 := by
  induction fuel generalizing x with
  | zero => simp [boundaries]
  | succ fuel ih =>
    unfold boundaries
    dsimp only
    split
    · rename_i h
      let t := (p.trace f x).2.min' h
      have hm : t ∈ (p.trace f x).2 := min'_mem _ h
      have hd := drop_count (cover x hm) (trace_gt f p x t hm)
      have hb := ih t
      change 1 + boundaries f p fuel t ≤ _
      omega
    · omega
end Plan

namespace Graph
variable {n : ℕ} (G : Graph n)

private def dif {b : ℕ} (i j : Fin (b+1)) : Fin (2*b+1) :=
  ⟨i.val + b - j.val, by have := i.isLt; omega⟩

private theorem dif_cast {b : ℕ} (i j : Fin (b+1)) :
    ((dif i j).val : ℚ) - b = (i.val : ℚ) - j.val := by
  have h : j.val ≤ i.val+b := by have := j.isLt; omega
  simp only [dif, Nat.cast_sub h, Nat.cast_add]
  ring

/-- Numerator and denominator differences index every possible intersection. -/
def breakSet : Finset ℚ :=
  let T := G.total
  (univ : Finset (Fin (2*T+1) × Fin (2*(T*T)+1))).image fun d =>
    (T : ℚ) * ((d.1.val : ℚ) - T) / ((d.2.val : ℚ) - (T*T : ℕ))

theorem roots_covered : Plan.roots G.form ⊆ G.breakSet := by
  intro z hz
  obtain ⟨⟨a,b⟩, _, rfl⟩ := mem_image.mp hz
  apply mem_image.mpr
  refine ⟨(dif a.1 b.1,dif a.2 b.2),mem_univ _,?_⟩
  change (G.total : ℚ) * (((dif a.1 b.1).val : ℚ) - G.total) /
      (((dif a.2 b.2).val : ℚ) - (G.total*G.total : ℕ)) = _
  rw [dif_cast, dif_cast]
  simp only [root,form]
  ring

theorem breakSet_card : G.breakSet.card ≤ (2*G.total+1)*(2*(G.total*G.total)+1) := by
  apply Finset.card_image_le.trans_eq
  simp

theorem local_boundaries_le (fuel : ℕ) (x : ℚ) :
    Plan.boundaries id (G.localLevels id) fuel x ≤ (2*G.total+1)*(2*(G.total*G.total)+1)+1 := by
  have h := G.levels_sync id (fun _ => rfl)
  apply (Plan.boundaries_le _ G.breakSet (fun y => ?_) fuel x).trans
  · exact Nat.add_le_add_right ((card_filter_le _ _).trans G.breakSet_card) 1
  · rw [← h.rightTrace y]
    exact (Plan.trace_roots _ _ _).trans G.roots_covered

end Graph
end Louvain
