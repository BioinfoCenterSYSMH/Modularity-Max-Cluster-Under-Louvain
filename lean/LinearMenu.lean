import CandidateCount

namespace Louvain
open Finset
namespace LinearMenu

/-- Count exact scalar comparisons in a left-to-right maximum reduction.
    The input list (with possible duplicate keys) is scanned only once. -/
def maximum {A : Type} [LinearOrder A] (best : A) : List A → A × ℕ
  | [] => (best,0)
  | a::l =>
    let (v,c) := maximum (max best a) l
    (v,c+1)

theorem maximum_count {A : Type} [LinearOrder A] (a : A) (l : List A) :
    (maximum a l).2 = l.length := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp [maximum,ih]

theorem maximum_le_iff {A : Type} [LinearOrder A] (a : A) (l : List A) (z : A) :
    (maximum a l).1 ≤ z ↔ a ≤ z ∧ ∀ b ∈ l, b ≤ z := by
  induction l generalizing a with
  | nil => simp [maximum]
  | cons b l ih => simp [maximum,ih, max_le_iff, and_assoc]

theorem maximum_mem {A : Type} [LinearOrder A] (a : A) (l : List A) :
    (maximum a l).1 = a ∨ (maximum a l).1 ∈ l := by
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons b l ih =>
    simp only [maximum]
    rcases ih (max a b) with h | h
    · rcases max_choice a b with e | e
      · exact Or.inl (h.trans e)
      · exact Or.inr (List.mem_cons.mpr (.inl (h.trans e)))
    · exact Or.inr (List.mem_cons.mpr (.inr h))

/-- Compute the maximum, then evaluate candidates again to keep all ties.
    Each pass is linear in the candidate list length. -/
def topList {A : Type} [LinearOrder A] (first : ℕ) (l : List ℕ) (v : ℕ → A) :
    List ℕ × ℕ :=
  let scores := l.map v
  let m := maximum (v first) scores
  (l.filter (fun i => v i = m.1), m.2+l.length)

theorem top_count {A : Type} [LinearOrder A] (first : ℕ) (l : List ℕ) (v : ℕ → A) :
    (topList first l v).2 = 2*l.length := by simp [topList,maximum_count,two_mul]

theorem top_spec {A : Type} [LinearOrder A] {i first : ℕ} {l : List ℕ}
    (hf : first ∈ l) (v : ℕ → A) :
    i ∈ (topList first l v).1 ↔ i ∈ l ∧ ∀ j ∈ l, v j ≤ v i := by
  let m := maximum (v first) (l.map v)
  have hm : ∀ j ∈ l, v j ≤ m.1 := by
    have hh := (maximum_le_iff (v first) (l.map v) m.1).mp le_rfl
    exact fun j hj => hh.2 _ (List.mem_map.mpr ⟨j,hj,rfl⟩)
  simp only [topList,List.mem_filter,decide_eq_true_eq]
  change (i ∈ l ∧ v i = m.1) ↔ _
  constructor
  · rintro ⟨hi,hei⟩; exact ⟨hi,by rw [hei]; exact hm⟩
  · rintro ⟨hi,hmax⟩
    refine ⟨hi,le_antisymm (hm i hi) ?_⟩
    apply (maximum_le_iff _ _ _).mpr
    exact ⟨hmax _ hf, fun _ h => by
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h; exact hmax _ hj⟩

end LinearMenu
end Louvain
