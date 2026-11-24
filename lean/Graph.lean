import Enumeration
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Louvain
open scoped BigOperators
open Finset
abbrev Part (n : ℕ) := Fin n → Fin n

structure Graph (n : ℕ) where
  weight : Fin n → Fin n → ℕ
  symm : ∀ i j, weight i j = weight j i
  loopless : ∀ i, weight i i = 0

namespace Graph
variable {n : ℕ} (G : Graph n)
def deg (i : Fin n) := ∑ j, G.weight i j
def total := ∑ i, G.deg i

/-- Sum over ordered pairs in the same group, lifted to the original cells.
This permits contraction without discarding internal edges or their degrees. -/
def inside (p : Part n) (h : Fin n → Fin n → ℕ) :=
  ∑ i, ∑ j, if p i = p j then h i j else 0
theorem inside_le (p : Part n) (h : Fin n → Fin n → ℕ) :
    inside p h ≤ ∑ i, ∑ j, h i j := by
  apply sum_le_sum; intro i _
  apply sum_le_sum; intro j _
  split <;> simp_all

abbrev Code := Fin (G.total + 1) × Fin (G.total * G.total + 1)
def budget := (G.total + 1) * (G.total * G.total + 1)
theorem budget_eq : G.budget = Fintype.card G.Code := by simp [budget,Code]
def code (p : Part n) : G.Code :=
  (⟨inside p G.weight, Nat.lt_succ_of_le (inside_le p _)⟩,
   ⟨inside p (fun i j => G.deg i * G.deg j), Nat.lt_succ_of_le (by
     apply (inside_le p _).trans_eq
     simp only [← Finset.mul_sum, ← Finset.sum_mul, total])⟩)
def form (i : G.Code) : Form := ⟨(G.total : ℚ) * i.1.val, i.2.val⟩
noncomputable def score (r : ℝ) (p : Part n) := (G.form (G.code p)).v r

/-- Canonical labels are the smallest original cell indices in each community. -/
def canon (p : Part n) (v : Fin n) : Fin n :=
  (univ.filter (fun j => p j = p v)).min' ⟨v,by simp⟩
theorem canon_same (p : Part n) (i j : Fin n) : canon p i = canon p j ↔ p i = p j := by
  have h (v : Fin n) : p (canon p v) = p v := by
    have hm : canon p v ∈ univ.filter (fun j => p j = p v) := min'_mem _ _
    exact (mem_filter.mp hm).2
  constructor
  · intro he; rw [← h i,← h j,he]
  · intro he; unfold canon; congr 1; ext v; simp [he]

/-- 0 has first priority and means stay. Target t has index t+1.
The original node order and the order of canonical contracted blocks agree. -/
def moved (u p : Part n) (i : Fin n) (t : ℕ) : Part n :=
  if h : 0 < t ∧ t ≤ n then fun v => if u v = i then ⟨t-1,by omega⟩ else p v
  else p
@[simp] theorem moved_zero (u p : Part n) (i : Fin n) : moved u p i 0 = p := by simp [moved]

def targets (u p : Part n) (i : Fin n) : Finset ℕ :=
  insert 0 (((univ : Finset (Fin n × Fin n)).filter (fun ij =>
    u ij.1 = i ∧ u ij.2 ≠ i ∧ 0 < G.weight ij.1 ij.2)).image (fun ij => (p ij.2).val + 1))

def menu (u p : Part n) (i : Fin n) : Menu G.Code where
  options := G.targets u p i
  nonempty := ⟨0, mem_insert_self ..⟩
  form t := G.code (moved u p i t)

def visit (u p : Part n) (i : Fin n) : Plan G.Code (Part n) :=
  .ask (G.menu u p i) fun t => .done (moved u p i t)

def sweepList (u : Part n) : List (Fin n) → Part n → Plan G.Code (Part n)
  | [], p => .done p
  | i::is, p => (G.visit u p i).bind fun q => sweepList u is q

def sweep (u p : Part n) := G.sweepList u (List.finRange n) p

noncomputable def atReal (G : Graph n) (r : ℝ) : Menu G.Code → ℕ := fun m => point G.form m r

theorem visit_rises (u p : Part n) (i : Fin n) (r : ℝ) :
    let q := (G.visit u p i).run (G.atReal r)
    q = p ∨ G.score r p < G.score r q := by
  let m := G.menu u p i
  let w := point G.form m r
  have hw : w ∈ maxima G.form m r := min'_mem _ _
  obtain ⟨_,hm⟩ := mem_filter.mp hw
  have h0 : 0 ∈ m.options := mem_insert_self ..
  have hle := hm 0 h0
  by_cases he : (line G.form m 0).v r = (line G.form m w).v r
  · have z : 0 ∈ maxima G.form m r := mem_filter.mpr ⟨h0,fun j hj => (hm j hj).trans he.ge⟩
    have hz : w ≤ 0 := min'_le _ _ z
    have hw0 : w = 0 := by omega
    left
    change moved u p i w = p
    simp [hw0]
  · right
    have h := lt_of_le_of_ne hle he
    change G.score r p < G.score r (moved u p i w)
    change G.score r (moved u p i 0) < G.score r (moved u p i w) at h
    simpa only [moved_zero] using h

theorem sweepList_rises (u : Part n) (l : List (Fin n)) (p : Part n) (r : ℝ) :
    let q := (G.sweepList u l p).run (G.atReal r)
    q = p ∨ G.score r p < G.score r q := by
  induction l generalizing p with
  | nil => exact Or.inl rfl
  | cons i is ih =>
    simp only [sweepList,Plan.run_bind]
    rcases G.visit_rises u p i r with h | h
    · rw [h]; apply ih
    · rcases ih ((G.visit u p i).run (G.atReal r)) with h' | h'
      · right; rw [h']; exact h
      · exact Or.inr (h.trans h')

/-- Finitely many possible score pairs. The rank is used in the proof only. -/
noncomputable def rank (r : ℝ) (p : Part n) :=
  (univ.filter (fun c : G.Code => G.score r p < (G.form c).v r)).card
theorem rank_drops {p q : Part n} {r : ℝ} (h : G.score r p < G.score r q) :
    G.rank r q < G.rank r p := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  constructor
  · intro c hc
    exact mem_filter.mpr ⟨mem_univ _,h.trans (mem_filter.mp hc).2⟩
  · intro he
    have hc : G.code q ∈ univ.filter (fun c : G.Code => G.score r p < (G.form c).v r) :=
      mem_filter.mpr ⟨mem_univ _, h⟩
    rw [← he] at hc
    exact (lt_irrefl _) (mem_filter.mp hc).2

def settle (u : Part n) : ℕ → Part n → Plan G.Code (Part n)
  | 0, p => .done p
  | t+1, p => (G.sweep u p).bind fun q => if q = p then .done p else settle u t q

def settled (u : Part n) := G.settle u (G.budget + 1) u

/-- Uncapped operational semantics of the local moving phase. Finishing is
allowed only after a sweep returns unchanged. -/
inductive Quiesces (u : Part n) (r : ℝ) : Part n → Part n → Prop where
  | stable {p} : (G.sweep u p).run (G.atReal r) = p → Quiesces u r p p
  | again {p q z} : (G.sweep u p).run (G.atReal r) = q → q ≠ p →
      Quiesces u r q z → Quiesces u r p z

theorem settle_quiesces (u : Part n) (r : ℝ) (fuel : ℕ) (p : Part n) (h : G.rank r p < fuel) :
    G.Quiesces u r p ((G.settle u fuel p).run (G.atReal r)) := by
  induction fuel generalizing p with
  | zero => omega
  | succ t ih =>
    simp only [settle,Plan.run_bind]
    let q := (G.sweep u p).run (G.atReal r)
    by_cases he : q = p
    · rw [if_pos he]; exact .stable he
    · rw [if_neg he]
      have hs := (G.sweepList_rises u (List.finRange n) p r).resolve_left he
      have hd : G.rank r q < G.rank r p := G.rank_drops hs
      exact .again rfl he (ih q (by omega))

theorem settled_quiesces (u : Part n) (r : ℝ) :
    G.Quiesces u r u ((G.settled u).run (G.atReal r)) := by
  apply G.settle_quiesces
  rw [G.budget_eq]
  exact Nat.lt_succ_of_le ((card_filter_le _ _).trans_eq card_univ)

theorem Quiesces.unique {u p a b : Part n} {r : ℝ} (h : G.Quiesces u r p a)
    (g : G.Quiesces u r p b) : a = b := by
  induction h with
  | stable h => cases g with
    | stable => rfl
    | again he hn _ => exact (hn (he.symm.trans h)).elim
  | again he hn _ ih => cases g with
    | stable h => exact (hn (he.symm.trans h)).elim
    | again he' _ hh => exact ih (he.symm.trans he' ▸ hh)

def count (p : Part n) := (univ.image p).card

/-- Conceptual contraction: the new atomic units are the communities on the
original vertex set. Working on this lifting keeps all original degrees. -/
def levels (u : Part n) : Plan G.Code (Part n) :=
  (G.settled u).bind fun p =>
    let v := canon p
    if count v < count u then levels v else .done v
termination_by count u

/-- Uncapped multilevel execution, independently of enumeration and its fuel. -/
inductive Returns (r : ℝ) : Part n → Part n → Prop where
  | finish {u p} : G.Quiesces u r u p → ¬ count (canon p) < count u → Returns r u (canon p)
  | contract {u p z} : G.Quiesces u r u p → count (canon p) < count u →
      Returns r (canon p) z → Returns r u z

theorem levels_returns (r : ℝ) (u : Part n) :
    G.Returns r u ((G.levels u).run (G.atReal r)) := by
  rw [levels,Plan.run_bind]
  have hq := G.settled_quiesces u r
  dsimp only
  split
  · exact .contract hq ‹_› (levels_returns r _)
  · exact .finish hq ‹_›
termination_by count u

theorem Returns.unique {u a b : Part n} {r : ℝ} (h : G.Returns r u a)
    (g : G.Returns r u b) : a = b := by
  induction h with
  | finish hp hn => cases g with
    | finish hq _ => rw [hp.unique G hq]
    | contract hq hy _ => exact (hn ((hp.unique G hq).symm ▸ hy)).elim
  | contract hp hy _ ih => cases g with
    | finish hq hn => exact (hn (hp.unique G hq ▸ hy)).elim
    | contract hq _ hz => exact ih ((hp.unique G hq).symm ▸ hz)

def allOutputs : Finset (Part n) := Plan.enumerate G.form (G.levels id)

/-- No omissions and no false positives, for every nonnegative real resolution. -/
theorem allOutputs_exact (p : Part n) :
    p ∈ G.allOutputs ↔ ∃ r : ℝ, 0 ≤ r ∧ G.Returns r id p := by
  rw [allOutputs,Plan.enumerate_exact]
  constructor
  · rintro ⟨r,hr,rfl⟩; exact ⟨r,hr,G.levels_returns r id⟩
  · rintro ⟨r,hr,hp⟩; exact ⟨r,hr,(G.levels_returns r id).unique G hp⟩

end Graph
end Louvain
