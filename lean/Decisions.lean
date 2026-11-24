import DenseMenu
namespace Louvain
open Finset
namespace LinearMenu

/-- Empty means no future intersection. -/
def lower {A : Type} [LinearOrder A] (s : Finset A) :=
  if h : s.Nonempty then some (s.min' h) else none

def merge {A : Type} [LinearOrder A] : Option A → Option A → Option A
  | none,b => b
  | a,none => a
  | some a,some b => some (min a b)

theorem lower_union {A : Type} [LinearOrder A] (s t : Finset A) :
    lower (s ∪ t) = merge (lower s) (lower t) := by
  by_cases hs : s.Nonempty <;> by_cases ht : t.Nonempty
  · simp [lower,hs,ht,Finset.Nonempty.inl hs,min'_union hs ht,merge]
  · have := Finset.not_nonempty_iff_eq_empty.mp ht; subst t; simp [lower,hs,merge]
  · have := Finset.not_nonempty_iff_eq_empty.mp hs; subst s; simp [lower,ht,merge]
  · have := Finset.not_nonempty_iff_eq_empty.mp hs; subst s
    have := Finset.not_nonempty_iff_eq_empty.mp ht; subst t; simp [lower,merge]

theorem min_spec {A : Type} [LinearOrder A] (l : List A) : l.min? = lower l.toFinset := by
  by_cases h : l.toFinset.Nonempty
  · rw [lower,dif_pos h,List.min?_eq_some_iff le_refl min_choice (fun _ _ _ => le_min_iff)
      (fun _ _ _ _ hab hba => le_antisymm hab hba)]
    exact ⟨List.mem_toFinset.mp (min'_mem _ _),fun b hb => l.toFinset.min'_le b (List.mem_toFinset.mpr hb)⟩
  · rw [lower,dif_neg h,List.min?_eq_none_iff]; simpa using Finset.not_nonempty_iff_eq_empty.mp h

/-- Include a seed already present in the input, so maximum needs no bottom value. -/
def selectTop {A : Type} [LinearOrder A] (l : List ℕ) (v : ℕ → A) : List ℕ :=
  match l with
  | [] => []
  | i::is => (topList i (i::is) v).1

theorem selectTop_spec {A : Type} [LinearOrder A] (l : List ℕ) (v : ℕ → A) :
    (selectTop l v).toFinset = tops l.toFinset v := by
  ext j
  cases l with
  | nil => simp [selectTop,tops]
  | cons i is =>
    simp only [selectTop,List.mem_toFinset,tops,mem_filter]
    rw [top_spec (List.mem_cons_self)]

theorem selectTop_length {A : Type} [LinearOrder A] (l : List ℕ) (v : ℕ → A) :
    (selectTop l v).length ≤ l.length := by
  cases l with
  | nil => rfl
  | cons i is => apply List.length_filter_le

def shortlist (m : Menu Form) (x : ℚ) (infinitesimal : Bool) (l : List ℕ) :=
  let hi := selectTop l (fun j => (m.form j).q x)
  if infinitesimal then selectTop hi (fun j => -(m.form j).b) else hi

def choose (m : Menu Form) (x : ℚ) (b : Bool) (l : List ℕ) :=
  ((shortlist m x b l).min?).getD 0

theorem choose_spec (m : Menu Form) (x : ℚ) (b : Bool) (l : List ℕ) (hl : l.toFinset = m.options) :
    choose m x b l = if b then right id m x else pointQ id m x := by
  cases b
  · simp only [choose,shortlist,Bool.false_eq_true,↓reduceIte,min_spec,selectTop_spec,hl]
    change (lower (maximaQ id m x)).getD 0 = _
    have h : (maximaQ id m x).Nonempty := tops_ne m.nonempty _
    simp [lower,pointQ,h]
  · simp only [choose,shortlist,↓reduceIte,min_spec,selectTop_spec,hl]
    change (lower (rightSet id m x)).getD 0 = _
    have h : (rightSet id m x).Nonempty := tops_ne (tops_ne m.nonempty _) _
    simp [lower,right,h]

def crossings (m : Menu Form) (l : List ℕ) (w : ℕ) :=
  (l.filter (fun j => (m.form j).b < (m.form w).b)).map (fun j => root (m.form w) (m.form j))

theorem crossings_spec (m : Menu Form) (x : ℚ) (l : List ℕ) (hl : l.toFinset = m.options) :
    (crossings m l (right id m x)).min? = lower (hazards id m x) := by
  rw [min_spec]
  congr 1
  ext y
  simp only [crossings,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq,hazards,
    mem_image,mem_filter,line,id_eq,← hl,List.mem_toFinset]

end LinearMenu
end Louvain
