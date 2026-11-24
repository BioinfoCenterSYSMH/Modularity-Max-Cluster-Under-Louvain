import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Louvain
@[ext] structure Form where
  a : ℚ
  b : ℚ
  deriving DecidableEq

def Form.q (f : Form) (x : ℚ) := f.a - x * f.b
noncomputable def Form.v (f : Form) (r : ℝ) := (f.a : ℝ) - r * (f.b : ℝ)
def root (f g : Form) : ℚ := (f.a - g.a) / (f.b - g.b)

@[simp] theorem Form.cast_q (f : Form) (x : ℚ) : ((f.q x : ℚ) : ℝ) = f.v x := by
  simp [Form.q, Form.v]

structure Menu (ι : Type) where
  options : Finset ℕ
  nonempty : options.Nonempty
  form : ℕ → ι

def tops {α : Type*} [LinearOrder α] (s : Finset ℕ) (v : ℕ → α) : Finset ℕ :=
  s.filter fun i => ∀ j ∈ s, v j ≤ v i

theorem tops_ne {α : Type*} [LinearOrder α] {s : Finset ℕ} (hs : s.Nonempty) (v : ℕ → α) :
    (tops s v).Nonempty := by
  obtain ⟨i, hi, him⟩ := s.exists_max_image v hs
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, him⟩⟩

variable {ι P : Type} (f : ι → Form)
def line (m : Menu ι) (i : ℕ) := f (m.form i)
noncomputable def maxima (m : Menu ι) (r : ℝ) := tops m.options fun i => (line f m i).v r
noncomputable def point (m : Menu ι) (r : ℝ) :=
  (maxima f m r).min' (tops_ne m.nonempty _)
def maximaQ (m : Menu ι) (x : ℚ) := tops m.options fun i => (line f m i).q x
def pointQ (m : Menu ι) (x : ℚ) := (maximaQ f m x).min' (tops_ne m.nonempty _)
def rightSet (m : Menu ι) (x : ℚ) :=
  tops (maximaQ f m x) fun i => -(line f m i).b
def right (m : Menu ι) (x : ℚ) :=
  (rightSet f m x).min' (tops_ne (tops_ne m.nonempty _) _)

theorem pointQ_eq (m : Menu ι) (x : ℚ) : pointQ f m x = point f m x := by
  have h : maximaQ f m x = maxima f m x := by
    ext i
    simp only [maximaQ, maxima, tops, Finset.mem_filter]
    constructor <;> rintro ⟨hi,h⟩ <;> refine ⟨hi,fun j hj => ?_⟩
    · simpa only [Form.cast_q] using (Rat.cast_le (K := ℝ)).mpr (h j hj)
    · apply (Rat.cast_le (K := ℝ)).mp
      simpa only [Form.cast_q] using h j hj
  unfold pointQ point
  congr 1

def hazards (m : Menu ι) (x : ℚ) : Finset ℚ :=
  let w := line f m (right f m x)
  (m.options.filter fun j => (line f m j).b < w.b).image fun j => root w (line f m j)

theorem right_data (m : Menu ι) (x : ℚ) :
    let w := right f m x
    w ∈ m.options ∧ (∀ j ∈ m.options, (line f m j).q x ≤ (line f m w).q x) ∧
    (∀ j ∈ m.options, (line f m j).q x = (line f m w).q x →
      (line f m w).b ≤ (line f m j).b) := by
  let w := right f m x
  have hw : w ∈ rightSet f m x := Finset.min'_mem _ _
  obtain ⟨hm,hs⟩ := Finset.mem_filter.mp hw
  obtain ⟨ho,hv⟩ := Finset.mem_filter.mp hm
  refine ⟨ho,hv,fun j hj he => ?_⟩
  have hjm : j ∈ maximaQ f m x := Finset.mem_filter.mpr
    ⟨hj, fun t ht => (hv t ht).trans he.ge⟩
  exact neg_le_neg_iff.mp (hs j hjm)

theorem root_strict (m : Menu ι) (x : ℚ) {t : ℚ} (ht : t ∈ hazards f m x) : x < t := by
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hjo,hb⟩ := Finset.mem_filter.mp hj
  obtain ⟨_,hm,hs⟩ := right_data f m x
  have hv := lt_of_le_of_ne (hm j hjo) (fun he => (not_le_of_gt hb) (hs j hjo he))
  rw [root, lt_div_iff₀ (sub_pos.mpr hb)]
  unfold Form.q at hv
  linarith only [hv]

/-- Up to the first overtake, the exact maximizers are precisely the lines
identical to the right winner. This also preserves the fixed tie priority. -/
theorem replay_menu (m : Menu ι) (x : ℚ) (r : ℝ) (hx : (x : ℝ) < r)
    (hh : ∀ t ∈ hazards f m x, r < (t : ℝ)) : point f m r = right f m x := by
  let w := right f m x
  let W := line f m w
  obtain ⟨hwo,hm,hs⟩ := right_data f m x
  have dominance (j : ℕ) (hj : j ∈ m.options) :
      line f m j = W ∨ (line f m j).v r < W.v r := by
    let J := line f m j
    have hv : J.q x ≤ W.q x := hm j hj
    have vx : J.v x ≤ W.v x := by simpa only [Form.cast_q] using (Rat.cast_le (K := ℝ)).mpr hv
    by_cases hb : J.b < W.b
    · right
      have ht : root W J ∈ hazards f m x :=
        Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj,hb⟩,rfl⟩
      have hr := hh _ ht
      have hd : (0 : ℝ) < (W.b : ℝ) - J.b := by exact_mod_cast sub_pos.mpr hb
      simp only [root, Rat.cast_div, Rat.cast_sub] at hr
      have h := (lt_div_iff₀ hd).mp hr
      change J.v r < W.v r
      unfold Form.v
      linarith only [h]
    · have hble : W.b ≤ J.b := le_of_not_gt hb
      rcases lt_or_eq_of_le hble with hlt | heq
      · right
        have hd : (0 : ℝ) < (J.b : ℝ) - W.b := by exact_mod_cast sub_pos.mpr hlt
        have h := mul_pos (sub_pos.mpr hx) hd
        change J.v r < W.v r
        unfold Form.v at vx ⊢
        linarith only [vx,h]
      · rcases lt_or_eq_of_le hv with hlt | hsame
        · right
          have h : J.a < W.a := by unfold Form.q at hlt; rw [heq] at hlt; linarith only [hlt]
          change J.v r < W.v r
          simp only [Form.v,heq,sub_lt_sub_iff_right]
          exact_mod_cast h
        · left
          have h : J.a = W.a := by unfold Form.q at hsame; rw [heq] at hsame; linarith only [hsame]
          change J = W
          exact Form.ext h heq.symm
  have sets : maxima f m r = rightSet f m x := by
    ext j
    constructor
    · intro hj
      obtain ⟨ho,hmax⟩ := Finset.mem_filter.mp hj
      have he : line f m j = W := (dominance j ho).resolve_right (not_lt_of_ge (hmax w hwo))
      have hq : j ∈ maximaQ f m x := Finset.mem_filter.mpr ⟨ho,by simpa [he,W,w] using hm⟩
      refine Finset.mem_filter.mpr ⟨hq,fun i hi => ?_⟩
      obtain ⟨hio,him⟩ := Finset.mem_filter.mp hi
      have hval := le_antisymm (hm i hio) (him w hwo)
      simpa [he,W,w] using neg_le_neg (hs i hio hval)
    · intro hj
      obtain ⟨hq,hsmall⟩ := Finset.mem_filter.mp hj
      obtain ⟨ho,hmax⟩ := Finset.mem_filter.mp hq
      have heq := le_antisymm (hm j ho) (hmax w hwo)
      have hwq : w ∈ maximaQ f m x := Finset.mem_filter.mpr ⟨hwo,hm⟩
      have hb := le_antisymm (neg_le_neg_iff.mp (hsmall w hwq)) (hs j ho heq)
      have he : line f m j = W := by
        have ha : (line f m j).a = W.a := by
          change (line f m j).q x = W.q x at heq
          unfold Form.q at heq
          change (line f m j).b = W.b at hb
          rw [hb] at heq
          linarith only [heq]
        exact Form.ext ha hb
      refine Finset.mem_filter.mpr ⟨ho,fun i hi => ?_⟩
      change (line f m i).v r ≤ (line f m j).v r
      rw [he]
      rcases dominance i hi with h | h
      · rw [h]
      · exact h.le
  unfold point right
  congr 1

end Louvain
