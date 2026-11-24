import BreakpointCount

namespace Louvain
open Finset
namespace Plan
variable {ι α β : Type}

def visits (ch : Menu ι → ℕ) : Plan ι α → ℕ
  | .done _ => 0
  | .ask m k => 1 + visits ch (k (ch m))

theorem visits_bind (p : Plan ι α) (k : α → Plan ι β) (ch : Menu ι → ℕ) :
    (p.bind k).visits ch = p.visits ch + (k (p.run ch)).visits ch := by
  induction p with
  | done => simp [visits,bind,run]
  | ask m next ih => simp [visits,bind,run,ih, Nat.add_assoc]

theorem replay_visits (f : ι → Form) (p : Plan ι α) (x : ℚ) (r : ℝ)
    (hx : (x : ℝ) < r) (hh : ∀ t ∈ (p.trace f x).2, r < (t : ℝ)) :
    p.visits (fun m => right f m x) = p.visits (fun m => point f m r) := by
  induction p with
  | done => rfl
  | ask m k ih =>
    simp only [trace] at hh
    simp only [visits, replay_menu f m x r hx (fun t ht => hh t (mem_union_left _ ht))]
    rw [ih _ (fun t ht => hh t (mem_union_right _ ht))]

theorem visits_right_real (f : ι → Form) (p : Plan ι α) (x : ℚ) :
    ∃ r : ℝ, p.visits (fun m => right f m x) = p.visits (fun m => point f m r) := by
  let s := (p.trace f x).2
  by_cases h : s.Nonempty
  · have hlt := trace_gt f p x (s.min' h) (min'_mem _ _)
    obtain ⟨y,hxy,hyt⟩ := exists_between hlt
    refine ⟨(y:ℝ), replay_visits f p x y (by exact_mod_cast hxy) ?_⟩
    intro t ht
    exact_mod_cast hyt.trans_le (s.min'_le _ ht)
  · exact ⟨(x:ℝ)+1,replay_visits f p x _ (by linarith) (fun t ht => (h ⟨t,ht⟩).elim)⟩
end Plan

namespace Graph
variable {n : ℕ} (G : Graph n)

theorem Sync.visits_point {ι κ α : Type} {f : ι → Form} {g : κ → Form}
    {post : α → Prop} {p : Plan ι α} {q : Plan κ α}
    (h : Sync f g post p q) (r : ℝ) :
    p.visits (fun m => point f m r) = q.visits (fun m => point g m r) := by
  induction h with
  | done => rfl
  | ask eq _ ih => simp only [Plan.visits,eq.exactPoint,ih]

private theorem rank_canon (r : ℝ) (p : Part n) : G.rank r (canon p) = G.rank r p := by
  have h (a : Fin n → Fin n → ℕ) : inside (canon p) a = inside p a := by
    simp only [inside,canon_same]
  have hcode : G.code (canon p) = G.code p := by
    apply Prod.ext <;> apply Fin.ext <;> simp only [code,h]
  simp only [rank,score,hcode]

private theorem sweep_visits (u p : Part n) (l : List (Fin n)) (ch : Menu G.Code → ℕ) :
    (G.sweepList u l p).visits ch = l.length := by
  induction l generalizing p with
  | nil => rfl
  | cons i is ih =>
    simp [sweepList,Plan.visits_bind,visit,Plan.visits,ih,Nat.add_comm]

/-- Charge a changed sweep against a rank decrease, including the rank carried
    through contraction. At most one unchanged sweep is charged per level. -/
private theorem settle_amortized (r : ℝ) (u : Part n) (fuel : ℕ) (p : Part n) :
    let a := G.settle u fuel p
    a.visits (G.atReal r) + n * G.rank r (a.run (G.atReal r)) ≤ n * G.rank r p + n := by
  induction fuel generalizing p with
  | zero => simp [settle,Plan.visits,Plan.run]
  | succ t ih =>
    let ch := G.atReal r
    let q := (G.sweep u p).run ch
    have hs : (G.sweep u p).visits ch = n := by simp [sweep,G.sweep_visits]
    simp only [settle,Plan.visits_bind,Plan.run_bind]
    change (G.sweep u p).visits ch + (if q = p then Plan.done p else G.settle u t q).visits ch +
      n * G.rank r ((if q = p then Plan.done p else G.settle u t q).run ch) ≤ _
    rw [hs]
    by_cases hqp : q = p
    · rw [if_pos hqp]
      simp [hqp,Plan.visits,Plan.run,Nat.add_comm]
    · rw [if_neg hqp]
      have hlt := G.rank_drops ((G.sweepList_rises u (List.finRange n) p r).resolve_left hqp)
      have hpay : n * G.rank r q + n ≤ n * G.rank r p := by
        simpa [Nat.mul_succ] using Nat.mul_le_mul_left n (Nat.succ_le_of_lt hlt)
      have hrec := ih q
      dsimp only at hrec
      change (G.settle u t q).visits ch + n*G.rank r ((G.settle u t q).run ch) ≤ _ at hrec
      omega

theorem levels_visits (r : ℝ) (u : Part n) :
    (G.levels u).visits (G.atReal r) ≤ n*G.rank r u + n*(count u)+n := by
  rw [levels,Plan.visits_bind]
  let p := (G.settled u).run (G.atReal r)
  have hwork := G.settle_amortized r u (G.budget+1) u
  change (G.settled u).visits (G.atReal r) + n*G.rank r p ≤ n*G.rank r u+n at hwork
  change (G.settled u).visits (G.atReal r) + (if count (canon p) < count u then
    G.levels (canon p) else Plan.done (canon p)).visits (G.atReal r) ≤ _
  split
  · rename_i smaller
    have bound := levels_visits r (canon p)
    rw [G.rank_canon] at bound
    have hpay : n*count (canon p)+n ≤ n*count u := by
      simpa [Nat.mul_succ] using Nat.mul_le_mul_left n (Nat.succ_le_of_lt smaller)
    omega
  · simp only [Plan.visits,Nat.add_zero]
    omega
termination_by count u

def visitBudget := n*(G.budget+n+1)

theorem local_point_visits (r : ℝ) :
    (G.localLevels id).visits (fun m => point id m r) ≤ G.visitBudget := by
  rw [← (G.levels_sync id (fun _ => rfl)).visits_point r]
  apply (G.levels_visits r id).trans
  have hr : G.rank r id ≤ G.budget := by
    rw [G.budget_eq]; exact (card_filter_le _ _).trans_eq card_univ
  have hc : count (id : Part n) ≤ n := by simp [count]
  simpa [visitBudget, Nat.mul_add] using
    Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left n hr) (Nat.mul_le_mul_left n hc)) n

theorem local_right_visits (x : ℚ) :
    (G.localLevels id).visits (fun m => right id m x) ≤ G.visitBudget := by
  obtain ⟨r,h⟩ := Plan.visits_right_real id (G.localLevels id) x
  rw [h]; exact G.local_point_visits r

end Graph
end Louvain
