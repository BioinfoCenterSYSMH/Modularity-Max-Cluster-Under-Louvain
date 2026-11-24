import MeteredTables
namespace Louvain
namespace Work
variable {α β : Type}
def mapL (f : α → Work β) : List α → Work (List β)
  | [] => ret []
  | a::l =>
    let b := f a
    let t := mapL f l
    ⟨b.val :: t.val,b.steps+t.steps+2⟩
def filterL (f : α → Work Bool) : List α → Work (List α)
  | [] => ret []
  | a::l =>
    let b := f a
    let t := filterL f l
    ⟨if b.val then a::t.val else t.val,b.steps+t.steps+2⟩
theorem mapL_val (f : α → Work β) (l : List α) :
    (mapL f l).val = l.map (fun a => (f a).val) := by
  induction l <;> simp_all [mapL,ret]
theorem filterL_val (f : α → Work Bool) (l : List α) :
    (filterL f l).val = l.filter (fun a => (f a).val) := by
  induction l <;> simp_all [filterL,ret,List.filter_cons]
theorem mapL_bound (f : α → Work β) {b : ℕ} (h : ∀ a, (f a).steps ≤ b) (l : List α) :
    (mapL f l).steps ≤ (b+2)*l.length := by
  induction l with
  | nil => simp [mapL,ret]
  | cons a l ih => simp only [mapL,List.length_cons,Nat.mul_succ]; have := h a; omega
theorem filterL_bound (f : α → Work Bool) {b : ℕ} (h : ∀ a, (f a).steps ≤ b) (l : List α) :
    (filterL f l).steps ≤ (b+2)*l.length := by
  induction l with
  | nil => simp [filterL,ret]
  | cons a l ih => simp only [filterL,List.length_cons,Nat.mul_succ]; have := h a; omega

def minL [LinearOrder α] : List α → Work (Option α)
  | [] => ret none
  | a::l =>
    let t := minL l
    ⟨some (t.val.elim a (min a)),t.steps+2⟩
theorem minL_val [LinearOrder α] (l : List α) : (minL l).val = l.min? := by
  induction l <;> simp_all [minL,ret,List.min?_cons]
theorem minL_steps [LinearOrder α] (l : List α) : (minL l).steps = 2*l.length := by
  induction l <;> simp_all [minL,ret,Nat.mul_succ]

def top [LinearOrder α] (v : ℕ → Work α) : List ℕ → Work (List ℕ)
  | [] => ret []
  | a::l =>
    let xs := a::l
    let scores := mapL v xs
    let seed := v a
    let m := LinearMenu.maximum seed.val scores.val
    let ans := filterL (fun i => let z := v i; ⟨decide (z.val=m.1),z.steps+1⟩) xs
    ⟨ans.val, scores.steps+seed.steps+2*m.2+ans.steps+1⟩
theorem top_val [LinearOrder α] (v : ℕ → Work α) (l : List ℕ) :
    (top v l).val = LinearMenu.selectTop l (fun i => (v i).val) := by
  cases l <;> simp [top,ret,LinearMenu.selectTop,LinearMenu.topList,mapL_val,filterL_val]

theorem top_steps [LinearOrder α] (v : ℕ → Work α) (h : ∀ i, (v i).steps ≤ 8) (l : List ℕ) :
    (top v l).steps ≤ 24*l.length+10 := by
  cases l with
  | nil => simp [top,ret]
  | cons a l =>
    let xs := a::l
    let m := LinearMenu.maximum (v a).val ((mapL v xs).val)
    let good := fun i => (⟨decide ((v i).val=m.1),(v i).steps+1⟩ : Work Bool)
    have hf := filterL_bound good (b:=9) (fun i => Nat.add_le_add_right (h i) 1) xs
    have hm := mapL_bound v h xs
    have hw : m.2 = xs.length := by simp [m,LinearMenu.maximum_count,mapL_val]
    change (mapL v xs).steps+(v a).steps+2*m.2+(filterL good xs).steps+1 ≤ 24*xs.length+10
    have := h a
    omega
end Work

namespace Metered
open LinearMenu

def qkey (f : ℕ → Form) (x : ℚ) (j : ℕ) : Work ℚ := ⟨(f j).q x,8⟩
def slope (f : ℕ → Form) (j : ℕ) : Work ℚ := ⟨-(f j).b,6⟩

def finalists (z : Rows) (x : ℚ) (b : Bool) :=
  (Work.top (qkey z.form x) z.labels).thenDo (fun hi =>
     if b then Work.top (slope z.form) hi else Work.ret hi)

def overtake (z : Rows) (w : ℕ) : Work (Option ℚ) :=
  (Work.filterL (fun j => (⟨decide ((z.form j).b < (z.form w).b),10⟩ : Work Bool)) z.labels).thenDo
    fun fits => (Work.mapL (fun j => (⟨root (z.form w) (z.form j),12⟩ : Work ℚ)) fits).thenDo Work.minL

/-- The selected target and the minimum future crossing (right trace only). -/
def decision (z : Rows) (x : ℚ) (b : Bool) : Work (ℕ × Option ℚ) :=
  (finalists z x b).thenDo fun l =>
    (Work.minL l).thenDo fun a =>
    let w := a.getD 0
    if b then (overtake z w).thenDo fun t => Work.ret (w,t)
    else Work.ret (w,none)

theorem finalists_spec (m : Menu Form) (z : Rows) (hf : z.form = m.form) (x : ℚ) (b : Bool) :
    (finalists z x b).val = shortlist m x b z.labels := by
  cases b <;> simp [finalists,shortlist,Work.thenDo,Work.top_val,Work.ret,hf,qkey,slope]

theorem finalists_length (z : Rows) (x : ℚ) (b : Bool) :
    (finalists z x b).val.length ≤ z.labels.length := by
  have h := selectTop_length z.labels (fun i => (qkey z.form x i).val)
  cases b <;> simp only [finalists,Work.thenDo,Work.top_val,Work.ret,Bool.false_eq_true,↓reduceIte]
  · exact h
  · exact (selectTop_length ..).trans h

theorem finalists_steps (z : Rows) (x : ℚ) (b : Bool) :
    (finalists z x b).steps ≤ 48*z.labels.length+20 := by
  let t := Work.top (qkey z.form x) z.labels
  have h : t.steps ≤ 24*z.labels.length+10 := Work.top_steps _ (fun _ => le_rfl) _
  have hl : t.val.length ≤ z.labels.length := by rw [show t.val = _ from Work.top_val ..]; apply selectTop_length
  have hs := Work.top_steps (slope z.form) (fun _ => by change 6 ≤ 8; decide) t.val
  cases b
  · change t.steps+0 ≤ _; omega
  · change t.steps+(Work.top (slope z.form) t.val).steps ≤ _; omega

theorem overtake_steps (z : Rows) (w : ℕ) : (overtake z w).steps ≤ 28*z.labels.length := by
  let ok := fun j => (⟨decide ((z.form j).b < (z.form w).b),10⟩ : Work Bool)
  let rt := fun j => (⟨root (z.form w) (z.form j),12⟩ : Work ℚ)
  let fits := Work.filterL ok z.labels
  let rr := Work.mapL rt fits.val
  have hf := Work.filterL_bound ok (b:=10) (fun _ => le_rfl) z.labels
  have hm := Work.mapL_bound rt (b:=12) (fun _ => le_rfl) fits.val
  have hl : fits.val.length ≤ z.labels.length := by simp only [fits,Work.filterL_val]; apply List.length_filter_le
  have hr : rr.val.length = fits.val.length := by simp [rr,Work.mapL_val]
  change fits.steps+(rr.steps+(Work.minL rr.val).steps) ≤ _
  rw [Work.minL_steps,hr]
  change fits.steps ≤ _ at hf
  change rr.steps ≤ _ at hm
  omega

theorem decision_steps (z : Rows) (x : ℚ) (b : Bool) :
    (decision z x b).steps ≤ 80*(z.labels.length+1) := by
  have hf := finalists_steps z x b
  have hl := finalists_length z x b
  unfold decision Work.thenDo Work.ret
  dsimp only
  rw [Work.minL_steps]
  split
  · rename_i hb
    have hh := overtake_steps z ((Work.minL (finalists z x b).val).val.getD 0)
    dsimp only; omega
  · dsimp only; omega

theorem decision_spec (m : Menu Form) (z : Rows) (hl : z.labels.toFinset=m.options)
    (hf : z.form = m.form) (x : ℚ) (b : Bool) :
    (decision z x b).val =
      (if b then right id m x else pointQ id m x,
       if b then lower (hazards id m x) else none) := by
  have hw := choose_spec m x b z.labels hl
  unfold choose at hw
  cases b <;> simp only [decision,Work.thenDo,Work.ret,Work.minL_val,finalists_spec m z hf,
    Bool.false_eq_true,↓reduceIte] at hw ⊢
  · rw [hw]
  · rw [hw]; congr 1
    simp only [overtake,Work.thenDo,Work.minL_val,Work.mapL_val,Work.filterL_val,hf]
    exact crossings_spec m x z.labels hl
end Metered
end Louvain
