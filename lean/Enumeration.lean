import Path
import Mathlib.Data.Fintype.Prod

namespace Louvain

/-- A terminating deterministic computation. All decisions depending on the
resolution go through a menu. Branch continuations are evaluated on demand. -/
inductive Plan (ι α : Type) where
  | done (value : α)
  | ask (menu : Menu ι) (next : ℕ → Plan ι α)

namespace Plan
variable {ι α β : Type}
def bind (p : Plan ι α) (k : α → Plan ι β) : Plan ι β :=
  match p with
  | .done a => k a
  | .ask m next => .ask m fun i => (next i).bind k

def run (choose : Menu ι → ℕ) : Plan ι α → α
  | .done a => a
  | .ask m next => (next (choose m)).run choose

@[simp] theorem run_bind (p : Plan ι α) (k : α → Plan ι β) (c : Menu ι → ℕ) :
    (p.bind k).run c = (k (p.run c)).run c := by
  induction p with
  | done a => rfl
  | ask m next ih => exact ih (c m)

def trace (f : ι → Form) (x : ℚ) : Plan ι α → α × Finset ℚ
  | .done a => (a, ∅)
  | .ask m next =>
    let (a,s) := (next (right f m x)).trace f x
    (a, hazards f m x ∪ s)

variable (f : ι → Form)
theorem replay (p : Plan ι α) (x : ℚ) (r : ℝ) (hx : (x : ℝ) < r)
    (h : ∀ z ∈ (p.trace f x).2, r < (z : ℝ)) :
    p.run (fun m => point f m r) = (p.trace f x).1 := by
  induction p with
  | done a => rfl
  | ask m next ih =>
    simp only [trace,run] at h ⊢
    rw [replay_menu f m x r hx (fun z hz => h z (Finset.mem_union_left _ hz))]
    exact ih _ (fun z hz => h z (Finset.mem_union_right _ hz))

theorem trace_gt (p : Plan ι α) (x : ℚ) :
    ∀ z ∈ (p.trace f x).2, x < z := by
  induction p with
  | done a => simp [trace]
  | ask m next ih =>
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact root_strict f m x h
    · exact ih _ z h

def roots [Fintype ι] : Finset ℚ :=
  (Finset.univ : Finset (ι × ι)).image fun ij => root (f ij.1) (f ij.2)

theorem trace_roots [Fintype ι] (p : Plan ι α) (x : ℚ) :
    (p.trace f x).2 ⊆ roots f := by
  induction p with
  | done a => simp [trace]
  | ask m next ih =>
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨(m.form (right f m x),m.form j),Finset.mem_univ _,rfl⟩
    · exact ih _ h

/-- Only a numeric upper bound on the possible breakpoints is needed.
The implementation does not visit the proof-only universe of roots. -/
def collect [DecidableEq α] (p : Plan ι α) : ℕ → ℚ → Finset α
  | 0, _ => ∅
  | fuel+1, x =>
    let (a,s) := p.trace f x
    insert (p.run (fun m => pointQ f m x)) (insert a
      (if h : s.Nonempty then collect p fuel (s.min' h) else ∅))

def above (s : Finset ℚ) (x : ℚ) := s.filter fun z => x < z
theorem drop_count {s : Finset ℚ} {x t : ℚ} (ht : t ∈ s) (hlt : x < t) :
    (above s t).card < (above s x).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro i hi
    obtain ⟨his,hit⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨his,hlt.trans hit⟩
  · intro he
    have hx : t ∈ above s x := Finset.mem_filter.mpr ⟨ht,hlt⟩
    rw [← he] at hx
    exact (lt_irrefl t) (Finset.mem_filter.mp hx).2

theorem collect_exact [Fintype ι] [DecidableEq α] (p : Plan ι α) (fuel : ℕ)
    (x : ℚ) (enough : (above (roots f) x).card < fuel) (y : α) :
    y ∈ collect f p fuel x ↔ ∃ r : ℝ, (x : ℝ) ≤ r ∧ p.run (fun m => point f m r) = y := by
  have hp (z : ℚ) : p.run (fun m => pointQ f m z) = p.run (fun m => point f m z) := by
    congr 1; funext m; exact pointQ_eq f m z
  induction fuel generalizing x with
  | zero => omega
  | succ fuel ih =>
    let s := (p.trace f x).2
    let a := (p.trace f x).1
    have start : ∀ t ∈ s, x < t := trace_gt f p x
    change y ∈ insert (p.run (fun m => pointQ f m x)) (insert a
      (if h : s.Nonempty then collect f p fuel (s.min' h) else ∅)) ↔ _
    rw [hp]
    by_cases hn : s.Nonempty
    · let t := s.min' hn
      have ht : t ∈ s := Finset.min'_mem _ _
      have hxt : x < t := start t ht
      have hrank := drop_count (trace_roots f p x ht) hxt
      have rec := ih t (by omega : (above (roots f) t).card < fuel)
      have near (r : ℝ) (hx : (x : ℝ) < r) (hr : r < (t : ℝ)) :
          p.run (fun m => point f m r) = a := replay f p x r hx fun z hz =>
        hr.trans_le (by exact_mod_cast s.min'_le z hz)
      rw [dif_pos hn, Finset.mem_insert, Finset.mem_insert]
      have hrt : (x : ℝ) < (t : ℝ) := by exact_mod_cast hxt
      constructor
      · rintro (h | h | h)
        · exact ⟨x,le_rfl,h.symm⟩
        · obtain ⟨r,h1,h2⟩ := exists_between hrt
          exact ⟨r,h1.le,(near r h1 h2).trans h.symm⟩
        · obtain ⟨r,hr,hy⟩ := rec.mp h
          exact ⟨r,hrt.le.trans hr,hy⟩
      · rintro ⟨r,hr,hy⟩
        rcases eq_or_lt_of_le hr with he | he
        · subst r; exact Or.inl hy.symm
        · by_cases z : r < (t : ℝ)
          · exact Or.inr (Or.inl (hy.symm.trans (near r he z)))
          · exact Or.inr (Or.inr (rec.mpr ⟨r,le_of_not_gt z,hy⟩))
    · have near (r : ℝ) (hx : (x : ℝ) < r) :
          p.run (fun m => point f m r) = a := replay f p x r hx fun z hz => (hn ⟨z,hz⟩).elim
      rw [dif_neg hn, Finset.mem_insert, Finset.mem_insert]
      constructor
      · rintro (h | h | h)
        · exact ⟨x,le_rfl,h.symm⟩
        · have hx : (x : ℝ) < x + 1 := by linarith
          exact ⟨_,hx.le,(near _ hx).trans h.symm⟩
        · simp at h
      · rintro ⟨r,hr,hy⟩
        rcases eq_or_lt_of_le hr with he | he
        · subst r; exact Or.inl hy.symm
        · exact Or.inr (Or.inl (hy.symm.trans (near r he)))

/-- The candidate alphabet supplies a numeric polynomial stopping bound.
Only exact rational operations are used by collect. -/
def enumerate [Fintype ι] [DecidableEq α] (p : Plan ι α) :=
  collect f p (Fintype.card ι * Fintype.card ι + 1) 0

theorem enumerate_exact [Fintype ι] [DecidableEq α] (p : Plan ι α) (y : α) :
    y ∈ enumerate f p ↔ ∃ r : ℝ, 0 ≤ r ∧ p.run (fun m => point f m r) = y := by
  have h1 := Finset.card_filter_le (roots f) (fun z : ℚ => 0 < z)
  have h2 : (roots f).card ≤ Fintype.card ι * Fintype.card ι :=
    Finset.card_image_le.trans_eq (by simp)
  simpa [enumerate] using collect_exact f p _ 0 (by unfold above; omega) y
end Plan
end Louvain
