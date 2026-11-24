import VisitCount

namespace Louvain
open Finset
namespace Plan
variable {ι α β : Type}

/-- Sum of menu lengths along this particular execution, including the stay option. -/
def entries (ch : Menu ι → ℕ) : Plan ι α → ℕ
  | .done _ => 0
  | .ask m next => m.options.card + entries ch (next (ch m))

def small (b : ℕ) : Plan ι α → Prop
  | .done _ => True
  | .ask m next => m.options.card ≤ b ∧ ∀ t, (next t).small b

theorem small_bind {b : ℕ} {p : Plan ι α} {k : α → Plan ι β}
    (h : p.small b) (hk : ∀ a, (k a).small b) : (p.bind k).small b := by
  induction p with
  | done a => exact hk a
  | ask m next ih => exact ⟨h.1,fun t => ih t (h.2 t)⟩

theorem entries_le {p : Plan ι α} {b : ℕ} (h : p.small b) (ch : Menu ι → ℕ) :
    p.entries ch ≤ b * p.visits ch := by
  induction p with
  | done => simp [entries,visits]
  | ask m next ih =>
    simpa [entries,visits,Nat.mul_add] using Nat.add_le_add h.1 (ih (ch m) (h.2 _))

/-- Count the exact and right-limit trajectories at each boundary visited by collect. -/
def allEntries (f : ι → Form) (p : Plan ι α) : ℕ → ℚ → ℕ
  | 0,_ => 0
  | fuel+1,x =>
    let s := (p.trace f x).2
    p.entries (fun m => pointQ f m x) + p.entries (fun m => right f m x) +
      if h : s.Nonempty then allEntries f p fuel (s.min' h) else 0

theorem allEntries_le (f : ι → Form) (p : Plan ι α) (c : ℕ)
    (runBound : ∀ x, p.entries (fun m => pointQ f m x) + p.entries (fun m => right f m x) ≤ c)
    (fuel : ℕ) (x : ℚ) : allEntries f p fuel x ≤ c * boundaries f p fuel x := by
  induction fuel generalizing x with
  | zero => simp [allEntries,boundaries]
  | succ fuel ih =>
    simp only [allEntries,boundaries]
    split
    · rename_i h
      simpa [Nat.mul_add] using Nat.add_le_add (runBound x) (ih ((p.trace f x).2.min' h))
    · simpa using runBound x
end Plan

namespace Graph
variable {n : ℕ} (G : Graph n)

private theorem menu_card (u p : Part n) (i : Fin n) :
    (G.localMenu u p i).options.card ≤ n+1 := by
  change (G.targets u p i).card ≤ n+1
  apply (card_le_card (t := range (n+1)) ?_).trans_eq (card_range _)
  intro t ht
  rcases mem_insert.mp ht with rfl | ht
  · simp
  · obtain ⟨ij,_,rfl⟩ := mem_image.mp ht
    simpa only [mem_range, Nat.add_lt_add_iff_right] using (p ij.2).isLt

private theorem sweep_small (u : Part n) (l : List (Fin n)) (p : Part n) :
    (G.localSweepList u l p).small (n+1) := by
  induction l generalizing p with
  | nil => trivial
  | cons i is ih =>
    apply Plan.small_bind
    · exact ⟨G.menu_card u p i,fun _ => trivial⟩
    · exact ih

private theorem settle_small (u : Part n) (fuel : ℕ) (p : Part n) :
    (G.localSettle u fuel p).small (n+1) := by
  induction fuel generalizing p with
  | zero => trivial
  | succ t ih =>
    apply Plan.small_bind (G.sweep_small ..)
    intro q; dsimp only; split
    · trivial
    · apply ih

private theorem levels_small (u : Part n) : (G.localLevels u).small (n+1) := by
  rw [localLevels]
  apply Plan.small_bind (G.settle_small ..)
  intro q; dsimp only; split
  · apply levels_small
  · trivial
termination_by count u

def candidateEntries := Plan.allEntries id (G.localLevels id) (G.budget*G.budget+1) 0

theorem candidate_concrete : G.candidateEntries ≤
    (2*((n+1)*G.visitBudget)) * ((2*G.total+1)*(2*(G.total*G.total)+1)+1) := by
  apply (Plan.allEntries_le _ _ _ ?_ _ _).trans
  · exact Nat.mul_le_mul_left _ (G.local_boundaries_le _ _)
  · intro x
    have h := G.levels_small id
    have hp := Plan.entries_le h (fun m => point id m (x:ℝ))
    have hr := Plan.entries_le h (fun m => right id m x)
    simp only [pointQ_eq]
    have h1 := hp.trans (Nat.mul_le_mul_left _ (G.local_point_visits x))
    have h2 := hr.trans (Nat.mul_le_mul_left _ (G.local_right_visits x))
    omega
end Graph

namespace SNN
/-- An explicit n-independent constant for each fixed neighbour count. -/
def entriesConstant (k : ℕ) :=
  2*((scale k+1)*(scale k*scale k+1)+1)*((2*scale k+1)*(2*(scale k*scale k)+1)+1)

theorem entries_n14 {n k : ℕ} (S : SNN n k) (hk : 0 < k) :
    S.graph.candidateEntries ≤ entriesConstant k * (n+1)^14 := by
  let a := scale k
  let N := n+1
  let T := S.graph.total
  have hn : 1 ≤ N := Nat.le_add_left 1 n
  have bound : T ≤ a*N^2 := by
    calc T ≤ n*(n*a) := S.total_le hk
         _ = a*n^2 := by ring
         _ ≤ a*N^2 := by gcongr; exact Nat.le_succ n
  have one (e : ℕ) : 1 ≤ N^e := Nat.one_le_pow _ _ hn
  have square : T*T ≤ (a*a)*N^4 := by calc
    _ ≤ (a*N^2)*(a*N^2) := Nat.mul_le_mul bound bound
    _ = _ := by ring
  have pad {t c d : ℕ} (h : t ≤ c*N^d) : t+1 ≤ (c+1)*N^d := by
    simpa [Nat.add_mul] using Nat.add_le_add h (one d)
  have b1 := pad bound
  have b2 := pad square
  have budget : S.graph.budget ≤ ((a+1)*(a*a+1))*N^6 := by calc
    _ ≤ ((a+1)*N^2)*((a*a+1)*N^4) := Nat.mul_le_mul b1 b2
    _ = _ := by ring
  have outer1 : 2*T+1 ≤ (2*a+1)*N^2 := pad (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 bound)
  have outer2 : 2*(T*T)+1 ≤ (2*(a*a)+1)*N^4 := pad (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 square)
  have outer : (2*T+1)*(2*(T*T)+1)+1 ≤ ((2*a+1)*(2*(a*a)+1)+1)*N^6 := by
    apply pad
    calc _ ≤ ((2*a+1)*N^2)*((2*(a*a)+1)*N^4) := Nat.mul_le_mul outer1 outer2
         _ = _ := by ring
  have hN : N ≤ N^6 := by simpa using Nat.pow_le_pow_right hn (show 1 ≤ 6 by decide)
  have hsum : S.graph.budget+n+1 ≤ ((a+1)*(a*a+1)+1)*N^6 := by
    calc _ = S.graph.budget + N := by simp [N,Nat.add_assoc]
         _ ≤ ((a+1)*(a*a+1))*N^6 + N^6 := Nat.add_le_add budget hN
         _ = _ := by ring
  have vis : S.graph.visitBudget ≤ ((a+1)*(a*a+1)+1)*N^7 := by calc
    _ ≤ N*(((a+1)*(a*a+1)+1)*N^6) := Nat.mul_le_mul (Nat.le_succ n) hsum
    _ = _ := by ring
  apply S.graph.candidate_concrete.trans
  calc _ ≤ (2*(N*(((a+1)*(a*a+1)+1)*N^7))) * (((2*a+1)*(2*(a*a)+1)+1)*N^6) :=
           Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left N vis)) outer
       _ = _ := by unfold entriesConstant; dsimp [a,N]; ring
end SNN
end Louvain
#print axioms Louvain.SNN.entries_n14
