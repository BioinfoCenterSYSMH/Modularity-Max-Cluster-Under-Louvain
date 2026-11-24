import Completeness
namespace Louvain
open Finset
open scoped BigOperators
namespace SNN
variable {n k : ℕ} (S : SNN n k)

/-- Original unscaled Jaccard data. We allow symmetric pruning and discard loops. -/
def rawWeight (a b : Fin n) : ℚ :=
  if a ≠ b ∧ S.keep a b = true then
    (S.overlap a b : ℚ) / ((S.neighbors a ∪ S.neighbors b).card : ℚ) else 0

theorem union_card (a b : Fin n) :
    (S.neighbors a ∪ S.neighbors b).card = 2*k - S.overlap a b := by
  have h := Finset.card_union_add_card_inter (S.neighbors a) (S.neighbors b)
  rw [S.size_eq,S.size_eq] at h
  unfold overlap; omega

theorem scale_weight (hk : 0 < k) (a b : Fin n) :
    (S.graph.weight a b : ℚ) = (scale k : ℚ) * S.rawWeight a b := by
  simpa [rawWeight,S.union_card] using S.scaling hk a b

def rawDeg (a : Fin n) := ∑ b, S.rawWeight a b
def rawTotal := ∑ a, S.rawDeg a
def rawLinks (u p : Part n) (i t : Fin n) :=
  ∑ a, ∑ b, if u a = i ∧ u b ≠ i ∧ p b = t then S.rawWeight a b else 0
def rawBlockVol (u : Part n) (i : Fin n) := ∑ a, if u a = i then S.rawDeg a else 0
def rawTargetVol (u p : Part n) (i t : Fin n) :=
  ∑ b, if u b ≠ i ∧ p b = t then S.rawDeg b else 0

def rawLine (u p : Part n) (i t : Fin n) : Form :=
  ⟨S.rawTotal * S.rawLinks u p i t, S.rawBlockVol u i * S.rawTargetVol u p i t⟩
def rawTargets (u p : Part n) (i : Fin n) : Finset ℕ :=
  insert 0 (((univ : Finset (Fin n × Fin n)).filter (fun ij =>
    u ij.1 = i ∧ u ij.2 ≠ i ∧ 0 < S.rawWeight ij.1 ij.2)).image (fun ij => (p ij.2).val + 1))
def rawMenu (u p : Part n) (i : Fin n) : Menu Form :=
  ⟨S.rawTargets u p i,⟨0,mem_insert_self ..⟩,fun t => S.rawLine u p i (Graph.target p i t)⟩

theorem scale_posQ (k : ℕ) : (0 : ℚ) < scale k := by exact_mod_cast Nat.factorial_pos (2*k)
theorem opts_eq (hk : 0 < k) (u p : Part n) (i : Fin n) :
    S.graph.targets u p i = S.rawTargets u p i := by
  have edge (a b : Fin n) : 0 < S.graph.weight a b ↔ 0 < S.rawWeight a b := by
    calc
      _ ↔ (0:ℚ) < (S.graph.weight a b:ℚ) := by exact_mod_cast Iff.rfl
      _ ↔ _ := by rw [S.scale_weight hk]; exact mul_pos_iff_of_pos_left (scale_posQ k)
  simp only [Graph.targets,rawTargets,edge]

theorem scale_deg (hk : 0 < k) (a : Fin n) :
    (S.graph.deg a : ℚ) = (scale k : ℚ) * S.rawDeg a := by
  simp only [Graph.deg,rawDeg,Nat.cast_sum,S.scale_weight hk,Finset.mul_sum]
theorem scale_total (hk : 0 < k) :
    (S.graph.total : ℚ) = (scale k : ℚ) * S.rawTotal := by
  simp only [Graph.total,rawTotal,Nat.cast_sum,S.scale_deg hk,Finset.mul_sum]

theorem scale_local_value (hk : 0 < k) (u p : Part n) (i t : Fin n) (r : ℝ) :
    (S.graph.localLine u p i t).v r = ((scale k : ℝ)^2) * (S.rawLine u p i t).v r := by
  have hl : (Graph.cross u p i t S.graph.weight : ℚ) = (scale k : ℚ) * S.rawLinks u p i t := by
    simp only [Graph.cross,Graph.term,rawLinks,Nat.cast_sum,Finset.mul_sum,mul_ite,mul_zero]
    apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _
    split <;> simp_all [S.scale_weight hk]
  have hu : (S.graph.volU u i : ℚ) = (scale k : ℚ) * S.rawBlockVol u i := by
    simp only [Graph.volU,rawBlockVol,Nat.cast_sum,Finset.mul_sum,mul_ite,mul_zero]
    apply sum_congr rfl; intro a _; split <;> simp_all [S.scale_deg hk]
  have ht : (S.graph.volT u p i t : ℚ) = (scale k : ℚ) * S.rawTargetVol u p i t := by
    simp only [Graph.volT,rawTargetVol,Nat.cast_sum,Finset.mul_sum,mul_ite,mul_zero]
    apply sum_congr rfl; intro a _; split <;> simp_all [S.scale_deg hk]
  simp only [Graph.localLine,rawLine,Form.v,hl,hu,ht,S.scale_total hk,Rat.cast_mul,
    Rat.cast_natCast]; ring

theorem raw_point (hk : 0 < k) (u p : Part n) (i : Fin n) (r : ℝ) :
    point id (S.graph.localMenu u p i) r = point id (S.rawMenu u p i) r := by
  have ho : (S.graph.localMenu u p i).options = (S.rawMenu u p i).options := S.opts_eq hk u p i
  have sc t : (line id (S.graph.localMenu u p i) t).v r =
      (scale k : ℝ)^2 * (line id (S.rawMenu u p i) t).v r := S.scale_local_value hk u p i _ r
  have d : 0 < (scale k : ℝ)^2 := by
    have h : 0 < (scale k : ℝ) := by exact_mod_cast scale_posQ k
    positivity
  have hle (a b : ℝ) : (scale k : ℝ)^2*a ≤ (scale k : ℝ)^2*b ↔ a ≤ b := by
    constructor
    · intro h; by_contra! hab; exact (not_lt_of_ge h) (mul_lt_mul_of_pos_left hab d)
    · exact fun h => mul_le_mul_of_nonneg_left h d.le
  have hm : maxima id (S.graph.localMenu u p i) r = maxima id (S.rawMenu u p i) r := by
    ext j; simp only [maxima,tops,mem_filter,ho,sc,hle]
  unfold point; congr 1

/-- Independent single-resolution reference. It only uses raw weights and
the exact real parameter. No breakpoints, path enumerator, or fuel occur here. -/
noncomputable def rawSweep (r : ℝ) (u : Part n) : List (Fin n) → Part n → Part n
  | [],p => p
  | i::is,p =>
    let t := point id (S.rawMenu u p i) r
    rawSweep r u is (Graph.moved u p i t)

theorem sweep_eq_raw (hk : 0 < k) (r : ℝ) (u : Part n) (hu : Graph.canonical u)
    (l : List (Fin n)) (p : Part n) (hp : Graph.respects u p) :
    (S.graph.sweepList u l p).run (S.graph.atReal r) = S.rawSweep r u l p := by
  unfold Graph.atReal
  rw [(S.graph.sweep_sync u hu l p hp).realRun r]
  suffices ∀ p', (S.graph.localSweepList u l p').run (fun m => point id m r) =
      S.rawSweep r u l p' by exact this p
  induction l with
  | nil => exact fun _ => rfl
  | cons i is ih =>
    intro p'; simp only [Graph.localSweepList,Plan.run_bind,Graph.localVisit,Plan.run,rawSweep,
      S.raw_point hk,ih]

theorem raw_respects (r : ℝ) (u : Part n) (l : List (Fin n)) (p : Part n) (hp : Graph.respects u p) :
    Graph.respects u (S.rawSweep r u l p) := by
  induction l generalizing p with
  | nil => exact hp
  | cons i is ih => exact ih _ (Graph.moved_respects u p i _ hp)

inductive RawQuiesces (r : ℝ) (u : Part n) : Part n → Part n → Prop where
  | stable {p} : S.rawSweep r u (List.finRange n) p = p → RawQuiesces r u p p
  | again {p q z} : S.rawSweep r u (List.finRange n) p = q → q ≠ p →
      RawQuiesces r u q z → RawQuiesces r u p z

theorem quiescence_iff (hk : 0 < k) {r : ℝ} {u p z : Part n} (hu : Graph.canonical u)
    (hp : Graph.respects u p) :
    S.graph.Quiesces u r p z ↔ S.RawQuiesces r u p z := by
  constructor
  · intro h; induction h with
    | stable he => exact .stable ((S.sweep_eq_raw hk r u hu _ _ hp).symm.trans he)
    | again he hn _ ih =>
      have eq := (S.sweep_eq_raw hk r u hu _ _ hp).symm.trans he
      exact .again eq hn (ih (eq ▸ S.raw_respects r u _ _ hp))
  · intro h; induction h with
    | stable he => exact .stable ((S.sweep_eq_raw hk r u hu _ _ hp).trans he)
    | again he hn _ ih =>
      exact .again ((S.sweep_eq_raw hk r u hu _ _ hp).trans he) hn
        (ih (he ▸ S.raw_respects r u _ _ hp))

inductive RawReturns (r : ℝ) : Part n → Part n → Prop where
  | finish {u p} : S.RawQuiesces r u u p → ¬ Graph.count (Graph.canon p) < Graph.count u →
      RawReturns r u (Graph.canon p)
  | contract {u p z} : S.RawQuiesces r u u p → Graph.count (Graph.canon p) < Graph.count u →
      RawReturns r (Graph.canon p) z → RawReturns r u z

theorem returns_iff (hk : 0 < k) {r : ℝ} {u p : Part n} (hu : Graph.canonical u) :
    S.graph.Returns r u p ↔ S.RawReturns r u p := by
  constructor
  · intro h; induction h with
    | finish hq hn => exact .finish ((S.quiescence_iff hk hu (Graph.respects_self _)).mp hq) hn
    | contract hq hy _ ih =>
      exact .contract ((S.quiescence_iff hk hu (Graph.respects_self _)).mp hq) hy (ih (Graph.canonical_canon _))
  · intro h; induction h with
    | finish hq hn => exact .finish ((S.quiescence_iff hk hu (Graph.respects_self _)).mpr hq) hn
    | contract hq hy _ ih =>
      exact .contract ((S.quiescence_iff hk hu (Graph.respects_self _)).mpr hq) hy (ih (Graph.canonical_canon _))

/-- Main theorem: exact equality with the image of the independent, uncapped,
raw-Jaccard Louvain execution over the nonnegative real half-line. -/
theorem louvain_enumeration_exact (hk : 0 < k) (p : Part n) :
    p ∈ S.graph.localOutputs ↔ ∃ r : ℝ, 0 ≤ r ∧ S.RawReturns r id p := by
  rw [S.adaptive_local_exact]
  exact exists_congr fun _ => and_congr_right fun _ => S.returns_iff hk (fun _ => rfl)

/-- Every real resolution actually terminates with a unique canonical output. -/
theorem raw_total_unique (hk : 0 < k) (r : ℝ) : ∃! p : Part n, S.RawReturns r id p := by
  let p := (S.graph.levels id).run (S.graph.atReal r)
  have hg : S.graph.Returns r id p := S.graph.levels_returns r id
  have translate (z : Part n) := @returns_iff n k S hk r id z (fun _ => rfl)
  exact ⟨p,(translate p).mp hg,fun q hq => ((translate q).mpr hq).unique S.graph hg⟩

end SNN
end Louvain
#print axioms Louvain.SNN.louvain_enumeration_exact
#print axioms Louvain.SNN.raw_total_unique
