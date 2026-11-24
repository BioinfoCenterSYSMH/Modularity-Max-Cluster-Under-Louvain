import MeteredScan
namespace Louvain
open Finset
open scoped BigOperators
namespace Metered
variable {n : ℕ}

/-- Exact classical Newman--Girvan modularity using ordered pairs. The public
    theorem assumes positive total weight; there is no zero denominator there. -/
def classical (g : Input n) (p : Part n) : ℚ :=
  let a := ∑ i, ∑ j, if p i = p j then g.w i j else 0
  let b := ∑ i, ∑ j, if p i = p j then g.d i * g.d j else 0
  ((g.t:ℚ)*a-b)/(g.t*g.t : ℕ)

def scoreRow (g : Input n) (p : Part n) : Work ℚ :=
  (Work.sum (fun i : Fin n => Work.sum (fun j : Fin n =>
     (⟨if p i = p j then g.w i j else 0,4⟩ : Work ℕ)))).thenDo fun a =>
  (Work.sum (fun i : Fin n => Work.sum (fun j : Fin n =>
     (⟨if p i = p j then g.d i * g.d j else 0,6⟩ : Work ℕ)))).thenDo fun b =>
    ⟨((g.t:ℚ)*a-b)/(g.t*g.t : ℕ),8⟩

theorem score_val (g : Input n) (p : Part n) : (scoreRow g p).val = classical g p := rfl
theorem score_steps (g : Input n) (p : Part n) : (scoreRow g p).steps ≤ 24*(n+1)^2 := by
  simp [scoreRow,Work.sum,Work.thenDo]; nlinarith [Nat.zero_le (n*n)]

/-- A deliberately simple deduplicator. At most one label-vector equality test
    per retained row per insertion. -/
def fresh (x : Part n) : List (Part n) → Work Bool
  | [] => ⟨true,1⟩
  | a::l =>
    let h := same x a
    if h.val then ⟨false,h.steps+2⟩
    else let t := fresh x l; ⟨t.val,h.steps+t.steps+2⟩

theorem fresh_spec (x : Part n) (l : List (Part n)) : (fresh x l).val = true ↔ x ∉ l := by
  induction l with
  | nil => simp [fresh]
  | cons a l ih =>
    by_cases h : x=a
    · subst a; simp [fresh,(same_iff x x).mpr rfl]
    · have hn := mt (same_iff x a).mp h; simp [fresh,hn,h,ih]
theorem fresh_steps (x : Part n) (l : List (Part n)) :
    (fresh x l).steps ≤ (4*n+3)*l.length+1 := by
  induction l with
  | nil => simp [fresh]
  | cons a l ih =>
    simp only [fresh,List.length_cons,Nat.mul_succ]; split <;> simp only [same] <;> omega

def uniqueRows : List (Part n) → Work (List (Part n))
  | [] => ⟨[],0⟩
  | x::l =>
    let t := uniqueRows l
    let h := fresh x t.val
    ⟨if h.val then x::t.val else t.val,t.steps+h.steps+2⟩

theorem unique_spec (l : List (Part n)) :
    (uniqueRows l).val.Nodup ∧ ∀ x, x ∈ (uniqueRows l).val ↔ x ∈ l := by
  induction l with
  | nil => simp [uniqueRows]
  | cons a l ih =>
    simp only [uniqueRows]; split
    · rename_i h
      exact ⟨List.nodup_cons.mpr ⟨(fresh_spec ..).mp h,ih.1⟩,by simp [ih.2]⟩
    · rename_i h; have hm : a ∈ (uniqueRows l).val := by simpa [fresh_spec] using h
      exact ⟨ih.1,fun x => by
        rw [List.mem_cons,← ih.2]; constructor
        · exact Or.inr
        · rintro (rfl|h); exact hm; exact h⟩

theorem unique_length (l : List (Part n)) : (uniqueRows l).val.length ≤ l.length := by
  induction l with
  | nil => simp [uniqueRows]
  | cons a l ih =>
    simp only [uniqueRows,List.length_cons]; split <;> simp_all
    omega

theorem unique_steps (l : List (Part n)) :
    (uniqueRows l).steps ≤ (4*n+6)*l.length^2 := by
  induction l with
  | nil => simp [uniqueRows]
  | cons a l ih =>
    have hs := fresh_steps a (uniqueRows l).val
    have hl := Nat.mul_le_mul_left (4*n+3) (unique_length l)
    simp only [uniqueRows,List.length_cons]
    nlinarith [Nat.zero_le (n*l.length),Nat.zero_le l.length]

structure Result (n : ℕ) where
  scores : List (Part n × ℚ)
  best : List (Part n × ℚ)

def bestRows (s : List (Part n × ℚ)) : Work (List (Part n × ℚ)) :=
  match s with
  | [] => Work.ret []
  | a::l =>
    let values := (a::l).map Prod.snd
    let m := LinearMenu.maximum a.2 values
    let keep := Work.filterL (fun row : Part n × ℚ => (⟨decide (row.2=m.1),2⟩ : Work Bool)) (a::l)
    ⟨keep.val,2*values.length+2*m.2+keep.steps+2⟩

theorem best_spec (s : List (Part n × ℚ)) (v : Part n × ℚ) :
    v ∈ (bestRows s).val ↔ v ∈ s ∧ ∀ w ∈ s, w.2 ≤ v.2 := by
  cases s with
  | nil => simp [bestRows,Work.ret]
  | cons a l =>
    let s := a::l
    let m := LinearMenu.maximum a.2 (s.map Prod.snd)
    have ub : ∀ w ∈ s, w.2 ≤ m.1 := fun w hw =>
      ((LinearMenu.maximum_le_iff _ _ m.1).mp le_rfl).2 _ (List.mem_map.mpr ⟨w,hw,rfl⟩)
    simp only [bestRows,Work.filterL_val,List.mem_filter,decide_eq_true_eq]
    change (v ∈ s ∧ v.2 = m.1) ↔ _
    constructor
    · rintro ⟨hv,he⟩; exact ⟨hv,by rw [he]; exact ub⟩
    · rintro ⟨hv,h⟩
      refine ⟨hv,le_antisymm (ub v hv) ?_⟩
      apply (LinearMenu.maximum_le_iff ..).mpr
      exact ⟨h a List.mem_cons_self,fun _ hj => by
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hj; exact h w hw⟩

theorem best_steps (s : List (Part n × ℚ)) : (bestRows s).steps ≤ 8*s.length+2 := by
  cases s with
  | nil => simp [bestRows,Work.ret]
  | cons a l =>
    simp only [bestRows,LinearMenu.maximum_count,List.length_map]
    have h := Work.filterL_bound (b:=2)
      (fun row : Part n × ℚ => (⟨decide (row.2 = (LinearMenu.maximum a.2 ((a::l).map Prod.snd)).1),2⟩ : Work Bool))
      (fun _ => le_rfl) (a::l)
    omega

def rankAll (g : Input n) (l : List (Part n)) : Work (Result n) :=
  (uniqueRows l).thenDo fun ps =>
  (Work.mapL (fun p => let q := scoreRow g p; (⟨(p,q.val),q.steps+1⟩ : Work (Part n × ℚ))) ps).thenDo
    fun s => (bestRows s).thenDo (fun b => Work.ret ⟨s,b⟩)

theorem rank_scores (g : Input n) (l : List (Part n)) (p : Part n) (q : ℚ) :
    (p,q) ∈ (rankAll g l).val.scores ↔ p ∈ l ∧ q = classical g p := by
  simp [rankAll,Work.thenDo,Work.ret,Work.mapL_val,score_val,(unique_spec l).2,eq_comm]
theorem rank_best (g : Input n) (l : List (Part n)) (p : Part n) (q : ℚ) :
    (p,q) ∈ (rankAll g l).val.best ↔
      (p,q) ∈ (rankAll g l).val.scores ∧ ∀ w ∈ (rankAll g l).val.scores, w.2 ≤ q := by
  exact best_spec _ _

theorem rank_steps (g : Input n) (l : List (Part n)) :
    (rankAll g l).steps ≤ (4*n+6)*l.length^2 + (24*(n+1)^2+11)*l.length+2 := by
  let ps := uniqueRows l
  let entry := fun p : Part n => let q := scoreRow g p; (⟨(p,q.val),q.steps+1⟩ : Work (Part n × ℚ))
  let ss := Work.mapL entry ps.val
  have hx := Work.mapL_bound entry (b:=24*(n+1)^2+1) (fun p => Nat.add_le_add_right (score_steps g p) 1) ps.val
  have hs := best_steps ss.val
  have hslen : ss.val.length = ps.val.length := by simp [ss,Work.mapL_val]
  rw [hslen] at hs
  have hl := unique_length l
  have hu := unique_steps l
  change ps.steps ≤ _ at hu
  change ps.val.length ≤ _ at hl
  change ss.steps ≤ _ at hx
  change ps.steps+(ss.steps+((bestRows ss.val).steps+0)) ≤ _
  have hprod := Nat.mul_le_mul_left (24*(n+1)^2+11) hl
  calc _ ≤ (4*n+6)*l.length^2 + ((24*(n+1)^2+1+2)*ps.val.length + (8*ps.val.length+2)) := by omega
       _ = (4*n+6)*l.length^2 + (24*(n+1)^2+11)*ps.val.length+2 := by ring
       _ ≤ _ := by gcongr
end Metered
end Louvain
