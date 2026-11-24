import LocalGain
namespace Louvain
open Finset
namespace Graph
variable {n : ℕ} (G : Graph n)
theorem shift_q (c l : Form) (x : ℚ) : (shift c l).q x = c.q x + 2 * l.q x := by
  unfold Form.q shift; ring
theorem shift_v (c l : Form) (r : ℝ) : (shift c l).v r = c.v r + 2 * l.v r := by
  simp [Form.v,shift]; ring
theorem shift_root (c a b : Form) : root (shift c a) (shift c b) = root a b := by
  unfold root shift
  simp only
  rw [show c.a + 2*a.a - (c.a+2*b.a) = 2*(a.a-b.a) by ring,
      show c.b + 2*a.b - (c.b+2*b.b) = 2*(a.b-b.b) by ring]
  rw [mul_div_mul_left _ _ (by norm_num : (2:ℚ) ≠ 0)]

structure Agree {ι κ : Type} (f : ι → Form) (g : κ → Form) (m : Menu ι) (l : Menu κ) : Prop where
  exactPoint : ∀ r : ℝ, point f m r = point g l r
  infinitesimal : ∀ x : ℚ, right f m x = right g l x
  overtakes : ∀ x : ℚ, hazards f m x = hazards g l x

theorem affine_agree {ι κ : Type} {f : ι → Form} {g : κ → Form} {m : Menu ι} {l : Menu κ}
    (c : Form) (ho : m.options = l.options) (hl : ∀ t, line f m t = shift c (line g l t)) :
    Agree f g m l := by
  have qr (a b : ℚ) : 2*a ≤ 2*b ↔ a ≤ b := by constructor <;> intro h <;> linarith
  have qt (a b : ℚ) : 2*a < 2*b ↔ a < b := by constructor <;> intro h <;> linarith
  have rr (a b : ℝ) : 2*a ≤ 2*b ↔ a ≤ b := by constructor <;> intro h <;> linarith
  have sb (l : Form) : (shift c l).b = c.b + 2*l.b := rfl
  have mq (x : ℚ) : maximaQ f m x = maximaQ g l x := by
    ext i; simp only [maximaQ,tops,mem_filter,ho,hl,shift_q,add_le_add_iff_left,
      qr]
  have rs (x : ℚ) : rightSet f m x = rightSet g l x := by
    ext i; simp only [rightSet,tops,mem_filter,mq,hl,shift,neg_le_neg_iff,
      add_le_add_iff_left,qr]
  have ri (x : ℚ) : right f m x = right g l x := by unfold right; congr 1; exact rs x
  refine ⟨?_,ri,?_⟩
  · intro r
    have mx : maxima f m r = maxima g l r := by
      ext i; simp only [maxima,tops,mem_filter,ho,hl,shift_v,add_le_add_iff_left,
        rr]
    unfold point; congr 1
  · intro x; unfold hazards
    simp only [hl,ri,ho,shift_root,sb,add_lt_add_iff_left,qt]

/-- Relate the local and full score implementations, including their actual
adaptive jumps, rather than only their final sets of partitions. -/
inductive Sync {ι κ α : Type} (f : ι → Form) (g : κ → Form) (post : α → Prop) :
    Plan ι α → Plan κ α → Prop where
  | done {a} : post a → Sync f g post (.done a) (.done a)
  | ask {m l k k'} : Agree f g m l → (∀ t, Sync f g post (k t) (k' t)) →
      Sync f g post (.ask m k) (.ask l k')

namespace Sync
variable {ι κ α β : Type} {f : ι → Form} {g : κ → Form} {I : α → Prop} {J : β → Prop}
  {p : Plan ι α} {q : Plan κ α}

theorem bind {k : α → Plan ι β} {k' : α → Plan κ β} (h : Sync f g I p q)
    (hk : ∀ a, I a → Sync f g J (k a) (k' a)) : Sync f g J (p.bind k) (q.bind k') := by
  induction h with
  | done ha => exact hk _ ha
  | ask eq _ ih => exact .ask eq ih

theorem realRun (h : Sync f g I p q) (r : ℝ) :
    p.run (fun m => point f m r) = q.run (fun l => point g l r) := by
  induction h with
  | done _ => rfl
  | ask eq _ ih => simp only [Plan.run,eq.exactPoint]; apply ih

theorem rationalRun (h : Sync f g I p q) (x : ℚ) :
    p.run (fun m => pointQ f m x) = q.run (fun l => pointQ g l x) := by
  simp only [pointQ_eq]; exact h.realRun x

theorem rightTrace (h : Sync f g I p q) (x : ℚ) : p.trace f x = q.trace g x := by
  induction h with
  | done _ => rfl
  | ask eq _ ih => simp only [Plan.trace,eq.infinitesimal,eq.overtakes,ih]

theorem collect_eq [DecidableEq α] (h : Sync f g I p q) (fuel : ℕ) (x : ℚ) :
    Plan.collect f p fuel x = Plan.collect g q fuel x := by
  induction fuel generalizing x with
  | zero => rfl
  | succ t ih => simp only [Plan.collect,h.rightTrace,h.rationalRun,ih]
end Sync

def localVisit (u p : Part n) (i : Fin n) : Plan Form (Part n) :=
  .ask (G.localMenu u p i) fun t => .done (moved u p i t)
def localSweepList (u : Part n) : List (Fin n) → Part n → Plan Form (Part n)
  | [],p => .done p
  | i::is,p => (G.localVisit u p i).bind fun q => localSweepList u is q

theorem sweep_sync (u : Part n) (hu : canonical u) (l : List (Fin n)) (p : Part n)
    (hp : respects u p) :
    Sync G.form id (respects u) (G.sweepList u l p) (G.localSweepList u l p) := by
  induction l generalizing p with
  | nil => exact .done hp
  | cons i is ih =>
    apply Sync.bind (I := respects u)
    · exact .ask (affine_agree (G.offset u p i) rfl (G.menu_shift u p i hu hp))
        (fun t => .done (moved_respects u p i t hp))
    · exact ih

def localSettle (u : Part n) : ℕ → Part n → Plan Form (Part n)
  | 0,p => .done p
  | t+1,p => (G.localSweepList u (List.finRange n) p).bind fun q =>
      if q = p then .done p else localSettle u t q

theorem settle_sync (u : Part n) (hu : canonical u) (fuel : ℕ) (p : Part n)
    (hp : respects u p) :
    Sync G.form id (respects u) (G.settle u fuel p) (G.localSettle u fuel p) := by
  induction fuel generalizing p with
  | zero => exact .done hp
  | succ t ih =>
    apply Sync.bind (G.sweep_sync u hu (List.finRange n) p hp)
    intro q hq; dsimp only; split
    · exact .done hp
    · exact ih q hq

def localLevels (u : Part n) : Plan Form (Part n) :=
  (G.localSettle u (G.budget + 1) u).bind fun p =>
    let v := canon p
    if count v < count u then localLevels v else .done v
termination_by count u

theorem levels_sync (u : Part n) (hu : canonical u) :
    Sync G.form id (fun _ => True) (G.levels u) (G.localLevels u) := by
  rw [levels,localLevels]
  apply Sync.bind (G.settle_sync u hu _ u (respects_self u))
  intro p _; dsimp only; split
  · exact levels_sync (canon p) (canonical_canon p)
  · exact .done trivial
termination_by count u

/-- Exact rational adaptive enumerator actually using local link weights and
remaining volumes. Only the bound uses the full-score alphabet. -/
def localOutputs : Finset (Part n) :=
  Plan.collect id (G.localLevels id) (G.budget * G.budget + 1) 0

theorem local_exact (p : Part n) :
    p ∈ G.localOutputs ↔ ∃ r : ℝ, 0 ≤ r ∧ G.Returns r id p := by
  have h := (G.levels_sync id (fun _ => rfl)).collect_eq (Fintype.card G.Code * Fintype.card G.Code + 1) 0
  unfold localOutputs
  rw [G.budget_eq]
  rw [← h]
  exact G.allOutputs_exact p

end Graph
namespace SNN
variable {n k : ℕ} (S : SNN n k)
/-- The adaptive local-score enumeration is sound and complete on a Jaccard SNN graph. -/
theorem adaptive_local_exact (p : Part n) :
    p ∈ S.graph.localOutputs ↔ ∃ r : ℝ, 0 ≤ r ∧ S.graph.Returns r id p :=
  S.graph.local_exact p
end SNN
end Louvain

#print axioms Louvain.SNN.adaptive_local_exact
#print axioms Louvain.SNN.scaling
#print axioms Louvain.SNN.enumeration_fuel_bound
