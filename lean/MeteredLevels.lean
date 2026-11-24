import MeteredControl
namespace Louvain
open Finset
namespace Metered
variable {n : ℕ}

def moveTable (u p : Part n) (i : Fin n) (j : ℕ) : Work (Part n) :=
  Work.tab fun a : Fin n => (⟨Graph.moved u p i j a,8⟩ : Work (Fin n))

def same (p q : Part n) : Work Bool :=
  ⟨(List.finRange n).all (fun i => decide (p i = q i)),4*n+1⟩
theorem same_iff (p q : Part n) : (same p q).val = true ↔ p=q := by
  simp [same,funext_iff]

def canonRow (p : Part n) (v : Fin n) : Work (Fin n) :=
  (Work.filterL (fun j : Fin n => (⟨decide (p j = p v),3⟩ : Work Bool)) (List.finRange n)).thenDo
    fun l => (Work.minL l).thenDo fun a => Work.ret (a.getD v)

def canonicalize (p : Part n) := Work.tab (canonRow p)
theorem canonRow_val (p : Part n) (v : Fin n) : (canonRow p v).val = Graph.canon p v := by
  simp only [canonRow,Work.thenDo,Work.filterL_val,Work.minL_val,Work.ret]
  generalize hl : (List.filter _ (List.finRange n)) = l
  suffices h : l.min? = some (Graph.canon p v) by rw [h]; rfl
  apply (List.min?_eq_some_iff le_refl min_choice (fun _ _ _ => le_min_iff)
      (fun _ _ _ _ hab hba => le_antisymm hab hba)).mpr
  subst l
  have hm := Finset.min'_mem (univ.filter (fun j => p j = p v)) (show _ from ⟨v,by simp⟩)
  constructor
  · simpa [Graph.canon] using hm
  · intro j hj
    apply Finset.min'_le
    simpa using hj

theorem canonicalize_val (p : Part n) : (canonicalize p).val = Graph.canon p :=
  funext (canonRow_val p)

theorem canonicalize_steps (p : Part n) : (canonicalize p).steps ≤ 10*(n+1)^2 := by
  have row (i : Fin n) : (canonRow p i).steps ≤ 7*n := by
    let test := fun j : Fin n => (⟨decide (p j=p i),3⟩ : Work Bool)
    let l := Work.filterL test (List.finRange n)
    have h := Work.filterL_bound test (b:=3) (fun _ => le_rfl) (List.finRange n)
    have hl : l.val.length ≤ n := by simp only [l,Work.filterL_val]; exact (List.length_filter_le ..).trans_eq List.length_finRange
    change l.steps + ((Work.minL l.val).steps+0) ≤ _
    change l.steps ≤ _ at h
    simp only [List.length_finRange] at h
    rw [Work.minL_steps]; omega
  have h := Work.bounded_sum _ row
  change (∑ i, (canonRow p i).steps)+n ≤ _
  nlinarith [Nat.zero_le (n*n)]

def occupied (p : Part n) (j : Fin n) : Work Bool :=
  ⟨(List.finRange n).any (fun i => decide (p i=j)),4*n+1⟩

def countGroups (p : Part n) : Work ℕ :=
  let z := Work.filterL (occupied p) (List.finRange n)
  ⟨z.val.length,z.steps+z.val.length+1⟩

theorem countGroups_val (p : Part n) : (countGroups p).val = Graph.count p := by
  let l := (List.finRange n).filter (fun j => (occupied p j).val)
  have hset : l.toFinset = univ.image p := by ext j; simp [l,occupied]
  have nd : l.Nodup := (List.nodup_finRange n).filter _
  change (Work.filterL (occupied p) _).val.length = _
  rw [Work.filterL_val,← List.toFinset_card_of_nodup nd,hset]
  rfl

theorem countGroups_steps (p : Part n) : (countGroups p).steps ≤ 10*(n+1)^2 := by
  let z := Work.filterL (occupied p) (List.finRange n)
  have h := Work.filterL_bound (occupied p) (b:=4*n+1) (fun _ => le_rfl) (List.finRange n)
  change z.steps ≤ _ at h
  simp only [List.length_finRange] at h
  have hl : z.val.length ≤ n := by simp only [z,Work.filterL_val]; exact (List.length_filter_le ..).trans_eq List.length_finRange
  change z.steps+z.val.length+1 ≤ _
  nlinarith [Nat.zero_le (n*n)]

def perVisit (n : ℕ) := 250*(n+1)
def visit (g : Input n) (c : Cache n) (u p : Part n) (i : Fin n) : Script (Part n) :=
  .ask (fun x b => (rows g c u p i).thenDo (fun z => decision z x b))
    (fun j => .done (moveTable u p i j).val) (fun j => (moveTable u p i j).steps)

theorem visit_refines (G : Graph n) (u p : Part n) (i : Fin n) :
    Refines (perVisit n) (visit (input G) (cache G u) u p i) (G.localVisit u p i) 0 := by
  apply Refines.ask
  · intro x b
    exact decision_spec _ _ (rows_labels G u p i) (funext (rows_form G u p i)) x b
  · intro x b
    let z := rows (input G) (cache G u) u p i
    have ⟨h1,h2⟩ := rows_bounds (input G) (cache G u) u p i
    have h3 := decision_steps z.val x b
    change z.steps ≤ _ at h1
    change z.val.labels.length ≤ _ at h2
    simp only [Work.thenDo,moveTable,Work.tab,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,perVisit]
    change z.steps+(decision z.val x b).steps+(n*8+n)+4 ≤ _
    omega
  · intro j; exact Refines.done _

def sweep (g : Input n) (c : Cache n) (u : Part n) : List (Fin n) → Part n → Script (Part n)
  | [],p => .done p
  | i::is,p => (visit g c u p i).bind fun q => sweep g c u is q

theorem sweep_refines (G : Graph n) (u : Part n) (l : List (Fin n)) (p : Part n) :
    Refines (perVisit n) (sweep (input G) (cache G u) u l p) (G.localSweepList u l p) 0 := by
  induction l generalizing p with
  | nil => exact .done _
  | cons i is ih => exact (visit_refines G u p i).bind ih

def settle (g : Input n) (c : Cache n) (u : Part n) : ℕ → Part n → Script (Part n)
  | 0,p => .done p
  | fuel+1,p => (sweep g c u (List.finRange n) p).bind fun q =>
    let z := same q p
    .spent z.steps (if z.val then .done p else settle g c u fuel q)

theorem settle_refines (G : Graph n) (u : Part n) (f : ℕ) (p : Part n) :
    Refines (perVisit n) (settle (input G) (cache G u) u f p) (G.localSettle u f p)
      (f*(4*n+1)) := by
  induction f generalizing p with
  | zero => simpa [settle,Graph.localSettle] using Refines.done (rate:=perVisit n) p
  | succ f ih =>
    unfold settle Graph.localSettle
    rw [Nat.succ_mul, Nat.add_comm]
    rw [← Nat.zero_add ((4*n+1)+f*(4*n+1))]
    apply (sweep_refines G u _ p).bind (b := (4*n+1)+f*(4*n+1))
    intro q
    dsimp only
    simp only [same_iff]
    apply Refines.spent
    by_cases h : q=p
    · simp only [if_pos h]; exact (Refines.done (rate:=perVisit n) p).more (Nat.zero_le _)
    · simp only [if_neg h]; apply ih

/-- An explicit level counter is initialized to n+1. The refinement proof below
    discharges the counter for the reference execution's original stopping rule. -/
def levels (g : Input n) (sweepFuel : ℕ) : ℕ → Part n → Script (Part n)
  | 0,u => .done u
  | levelFuel+1,u =>
    let c := build g u
    .spent c.steps ((settle g c.val u sweepFuel u).bind fun p =>
      let z := canonicalize p
      let a := countGroups z.val
      let b := countGroups u
      .spent (z.steps+a.steps+b.steps+1)
        (if a.val < b.val then levels g sweepFuel levelFuel z.val else .done z.val))

def overhead (G : Graph n) := 50*(n+1)^3+(G.budget+1)*(4*n+1)

theorem levels_refines (G : Graph n) (f : ℕ) (u : Part n) (enough : Graph.count u < f) :
    Refines (perVisit n) (levels (input G) (G.budget+1) f u) (G.localLevels u)
      (f*overhead G) := by
  induction f generalizing u with
  | zero => omega
  | succ f ih =>
    rw [levels,Graph.localLevels]
    apply Refines.more
    · apply Refines.spent
      apply (settle_refines G u (G.budget+1) u).bind (b:=31*(n+1)^2+f*overhead G)
      intro p
      dsimp only
      apply Refines.more
      · apply Refines.spent
        rw [canonicalize_val,countGroups_val,countGroups_val]
        split
        · rename_i h
          apply ih _ (by omega)
        · exact (Refines.done (rate:=perVisit n) _).more (Nat.zero_le (f*overhead G))
      · have h1 := canonicalize_steps p
        have h2 := countGroups_steps (canonicalize p).val
        have h3 := countGroups_steps u
        nlinarith [Nat.zero_le (n*n)]
    · have hb := build_steps (input G) u
      simp only [Nat.succ_mul,overhead] at *
      nlinarith [Nat.zero_le (n*n*n),Nat.zero_le (n*n)]
end Metered
end Louvain
