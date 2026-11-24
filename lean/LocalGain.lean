import Jaccard
namespace Louvain
open Finset
open scoped BigOperators
namespace Graph
variable {n : ℕ} (G : Graph n)

def assign (u p : Part n) (i t : Fin n) : Part n :=
  fun a => if u a = i then t else p a
def base (u p : Part n) (i : Fin n) (h : Fin n → Fin n → ℕ) :=
  ∑ a, ∑ b, if (u a = i ∧ u b = i) ∨ (u a ≠ i ∧ u b ≠ i ∧ p a = p b) then h a b else 0
def term (u p : Part n) (i t : Fin n) (h : Fin n → Fin n → ℕ) (a b : Fin n) :=
  if u a = i ∧ u b ≠ i ∧ p b = t then h a b else 0
def cross (u p : Part n) (i t : Fin n) (h : Fin n → Fin n → ℕ) :=
  ∑ a, ∑ b, term u p i t h a b

/-- Remove the moving block. Only its two orientations of cross edges
depend on the chosen target. No assumption about equal degrees is used. -/
theorem split_inside (u p : Part n) (i t : Fin n) (h : Fin n → Fin n → ℕ)
    (sym : ∀ a b, h a b = h b a) :
    inside (assign u p i t) h = base u p i h + 2 * cross u p i t h := by
  have swap : (∑ a, ∑ b, term u p i t h b a) = cross u p i t h := Finset.sum_comm
  -- Separate the two equal sums before pushing addition inside.
  have both : base u p i h + (cross u p i t h + cross u p i t h) =
      base u p i h + cross u p i t h + ∑ a, ∑ b, term u p i t h b a := by rw [swap,add_assoc]
  rw [two_mul,both]
  unfold inside base cross
  simp only [← Finset.sum_add_distrib]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro b _
  by_cases ha : u a = i <;> by_cases hb : u b = i <;>
    simp [assign,term,ha,hb,(@eq_comm _ t (p b)),sym b a]

def volU (u : Part n) (i : Fin n) := ∑ a, if u a = i then G.deg a else 0
def volT (u p : Part n) (i t : Fin n) :=
  ∑ b, if u b ≠ i ∧ p b = t then G.deg b else 0

theorem cross_deg (u p : Part n) (i t : Fin n) :
    cross u p i t (fun a b => G.deg a * G.deg b) = G.volU u i * G.volT u p i t := by
  unfold volU volT cross
  rw [Finset.sum_mul]
  apply sum_congr rfl; intro a _
  rw [Finset.mul_sum]
  apply sum_congr rfl; intro b _
  by_cases h1 : u a = i <;> by_cases h2 : u b = i <;> by_cases h3 : p b = t <;>
    simp [term,h1,h2,h3]

def offset (u p : Part n) (i : Fin n) : Form :=
  ⟨(G.total : ℚ) * base u p i G.weight, base u p i (fun a b => G.deg a * G.deg b)⟩
def localLine (u p : Part n) (i t : Fin n) : Form :=
  ⟨(G.total : ℚ) * cross u p i t G.weight, (G.volU u i : ℚ) * G.volT u p i t⟩
def shift (c l : Form) : Form := ⟨c.a + 2*l.a, c.b + 2*l.b⟩

theorem full_eq_local (u p : Part n) (i t : Fin n) :
    G.form (G.code (assign u p i t)) = shift (G.offset u p i) (G.localLine u p i t) := by
  have h1 := split_inside u p i t G.weight G.symm
  have h2 := split_inside u p i t (fun a b => G.deg a * G.deg b) (fun a b => Nat.mul_comm _ _)
  rw [G.cross_deg] at h2
  apply Form.ext
  · change (G.total : ℚ) * (inside (assign u p i t) G.weight : ℕ) = _
    rw [h1]; simp [shift,offset,localLine]; ring
  · change (inside (assign u p i t) (fun a b => G.deg a * G.deg b) : ℕ) = (_ : ℚ)
    rw [h2]; simp [shift,offset,localLine]

def respects (u p : Part n) := ∀ a b, u a = u b → p a = p b
def canonical (u : Part n) := ∀ a, u (u a) = u a
theorem respects_self (u : Part n) : respects u u := fun _ _ h => h
theorem canonical_canon (p : Part n) : canonical (canon p) := by
  intro a; apply (canon_same ..).mpr
  have h : canon p a ∈ univ.filter (fun j => p j = p a) := min'_mem _ _
  exact (mem_filter.mp h).2

theorem moved_respects (u p : Part n) (i : Fin n) (t : ℕ) (hp : respects u p) :
    respects u (moved u p i t) := by
  intro a b h
  unfold moved
  split
  · by_cases e : u b = i <;> simp [h,e,hp a b h]
  · exact hp a b h

def target (p : Part n) (i : Fin n) (t : ℕ) : Fin n :=
  if h : 0 < t ∧ t ≤ n then ⟨t-1,by omega⟩ else p i
theorem moved_eq_assign (u p : Part n) (i : Fin n) (t : ℕ) (hu : canonical u)
    (hp : respects u p) : moved u p i t = assign u p i (target p i t) := by
  funext a; unfold moved target assign
  split
  · rfl
  · by_cases h : u a = i
    · simp only [if_pos h]
      exact hp a i (h ▸ (hu a).symm)
    · simp [h]

def localMenu (u p : Part n) (i : Fin n) : Menu Form :=
  ⟨(G.menu u p i).options, (G.menu u p i).nonempty,fun t => G.localLine u p i (target p i t)⟩

theorem menu_shift (u p : Part n) (i : Fin n) (hu : canonical u) (hp : respects u p) (t : ℕ) :
    line G.form (G.menu u p i) t = shift (G.offset u p i) (line id (G.localMenu u p i) t) := by
  change G.form (G.code (moved u p i t)) = _
  rw [moved_eq_assign u p i t hu hp]; apply G.full_eq_local

end Graph
end Louvain
