import LinearMenu

namespace Louvain
open Finset
open scoped BigOperators
namespace Dense
variable {n : ℕ}

/-- Group n scalar values by current labels. One indexed read, one addition
    and one indexed write per element on a mutable random-access vector. -/
def scatter (label : Fin n → Fin n) (w : Fin n → ℕ) (l : List (Fin n))
    (initial : Vector ℕ n) : Vector ℕ n × ℕ :=
  match l with
  | [] => (initial,0)
  | i::is =>
    let j := label i
    let rest := scatter label w is (initial.set j.val (initial[j.val]+w i) j.isLt)
    (rest.1,rest.2+1)

theorem scatter_adds (label : Fin n → Fin n) (w) (l) (buf) :
    (scatter label w l buf).2 = l.length := by
  induction l generalizing buf <;> simp_all [scatter]

theorem scatter_get (label : Fin n → Fin n) (w) (l) (buf) (t : Fin n) :
    (scatter label w l buf).1[t.val] = buf[t.val] +
       (l.map (fun i => if label i = t then w i else 0)).sum := by
  induction l generalizing buf with
  | nil => simp [scatter]
  | cons a l ih =>
    simp only [scatter,ih,Vector.getElem_set,List.map_cons,List.sum_cons]
    by_cases h : label a = t
    · simp [h,Nat.add_assoc]
    · have hv : (label a).val ≠ t.val := fun e => h (Fin.ext e)
      simp [h,hv]

def bucket (p : Part n) (w : Fin n → ℕ) := scatter p w (List.finRange n) (Vector.replicate n 0)
theorem bucket_val (p : Part n) (w) (t : Fin n) :
    (bucket p w).1[t.val] = ∑ b, if p b = t then w b else 0 := by
  rw [bucket,scatter_get]
  simp only [Vector.getElem_replicate,Nat.zero_add]
  rw [← List.toFinset_finRange n]
  exact (List.sum_toFinset _ (List.nodup_finRange n)).symm

end Dense
namespace Graph
variable {n : ℕ} (G : Graph n)

/-- Materializable once per level. Each entry is the sum of a column over the
    original cells in a block; an internal block edge contributes zero. -/
def column (u : Part n) (i b : Fin n) : ℕ :=
  if u b = i then 0 else ∑ a, if u a = i then G.weight a b else 0

def linksTable (u p : Part n) (i : Fin n) := Dense.bucket p (G.column u i)
def volumesTable (u p : Part n) (i : Fin n) :=
  Dense.bucket p (fun b => if u b = i then 0 else G.deg b)

theorem links_correct (u p : Part n) (i t : Fin n) :
    (G.linksTable u p i).1[t.val] = cross u p i t G.weight := by
  rw [linksTable,Dense.bucket_val,cross,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  unfold column term
  by_cases hb : u b = i <;> by_cases hp : p b = t <;> simp [hb,hp]

theorem volumes_correct (u p : Part n) (i t : Fin n) :
    (G.volumesTable u p i).1[t.val] = G.volT u p i t := by
  rw [volumesTable,Dense.bucket_val,volT]
  apply Finset.sum_congr rfl; intro b _
  by_cases hb : u b = i <;> by_cases hp : p b = t <;> simp [hb,hp]

def fastLine (v links : Vector ℕ n) (total blockVol : ℕ) (t : Fin n) : Form :=
  ⟨(total : ℚ)*links[t.val], (blockVol : ℚ)*v[t.val]⟩

theorem fastLine_correct (u p : Part n) (i t : Fin n) :
    fastLine (G.volumesTable u p i).1 (G.linksTable u p i).1 G.total (G.volU u i) t =
      G.localLine u p i t := by
  simp only [fastLine,G.links_correct,G.volumes_correct,localLine]

theorem links_positive (u p : Part n) (i t : Fin n) :
    0 < cross u p i t G.weight ↔ ∃ a b, u a = i ∧ u b ≠ i ∧ p b = t ∧ 0 < G.weight a b := by
  simp only [cross, Nat.pos_iff_ne_zero, ne_eq, Finset.sum_eq_zero_iff, mem_univ, true_implies]
  push_neg
  simp [term,ite_eq_right_iff,and_assoc]

theorem fastTargets_correct (u p : Part n) (i : Fin n) :
    insert 0 ((univ.filter (fun t : Fin n => 0 < (G.linksTable u p i).1[t.val])).image
      (fun t => t.val+1)) = G.targets u p i := by
  ext j
  simp only [targets,mem_insert,mem_image,mem_filter,mem_univ,true_and,G.links_correct,G.links_positive]
  constructor
  · rintro (h | ⟨t,⟨a,b,ha,hb,hp,hw⟩,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(a,b),⟨ha,hb,hw⟩,hp ▸ he⟩
  · rintro (h | ⟨⟨a,b⟩,⟨ha,hb,hw⟩,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p b,⟨a,b,ha,hb,rfl,hw⟩,he⟩
end Graph
end Louvain
