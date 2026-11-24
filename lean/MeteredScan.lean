import MeteredLevels
namespace Louvain
open Finset
namespace Metered
variable {n : ℕ}

def script (G : Graph n) (g : Input n) :=
  levels g (G.budget+1) (n+1) id

theorem script_refines (G : Graph n) :
    Refines (perVisit n) (script G (input G)) (G.localLevels id) ((n+1)*overhead G) := by
  apply levels_refines
  simp [Graph.count]

def perRun (G : Graph n) := perVisit n * G.visitBudget+(n+1)*overhead G

theorem run_bound (G : Graph n) (x : ℚ) (b : Bool) :
    ((script G (input G)).eval x b).steps ≤ perRun G := by
  apply ((script_refines G).sound x b).2.trans
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  cases b
  · rw [show select x false = (fun m => point id m (x:ℝ)) from funext (fun m => pointQ_eq id m x)]
    exact G.local_point_visits (x:ℝ)
  · simpa [select] using G.local_right_visits x

/-- Preserve exact-point and open-interval outputs separately before deduplicating.
    Only the running minimum crossing is needed, even if many moves propose it. -/
def scan (pg : Script (Part n)) : ℕ → ℚ → Work (List (Part n))
  | 0,_ => Work.ret []
  | fuel+1,x =>
    let a := pg.eval x false
    let b := pg.eval x true
    let next := match b.val.2 with
      | none => Work.ret []
      | some t => scan pg fuel t
    ⟨a.val.1 :: b.val.1 :: next.val,a.steps+b.steps+next.steps+8⟩

private theorem point_sound (G : Graph n) (x : ℚ) :
    ((script G (input G)).eval x false).val = ((G.localLevels id).run (fun m => pointQ id m x),none) :=
  ((script_refines G).sound x false).1.trans (expected_point _ _)

private theorem right_sound (G : Graph n) (x : ℚ) :
    ((script G (input G)).eval x true).val =
      (((G.localLevels id).trace id x).1,LinearMenu.lower ((G.localLevels id).trace id x).2) :=
  ((script_refines G).sound x true).1.trans (expected_trace _ _)

theorem scan_spec (G : Graph n) (fuel : ℕ) (x : ℚ) :
    (scan (script G (input G)) fuel x).val.toFinset =
      Plan.collect id (G.localLevels id) fuel x := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    simp only [scan,point_sound,right_sound,LinearMenu.lower,Plan.collect,List.toFinset_cons]
    by_cases h : ((G.localLevels id).trace id x).2.Nonempty <;> simp [h,ih,Work.ret]

theorem scan_length (G : Graph n) (fuel : ℕ) (x : ℚ) :
    (scan (script G (input G)) fuel x).val.length =
      2*Plan.boundaries id (G.localLevels id) fuel x := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    simp only [scan,right_sound,LinearMenu.lower,Plan.boundaries,List.length_cons]
    by_cases h : ((G.localLevels id).trace id x).2.Nonempty <;> simp [h,ih,Work.ret,Nat.mul_add]
    omega

theorem scan_steps (G : Graph n) (fuel : ℕ) (x : ℚ) :
    (scan (script G (input G)) fuel x).steps ≤
      (2*perRun G+8)*Plan.boundaries id (G.localLevels id) fuel x := by
  induction fuel generalizing x with
  | zero => simp [scan,Work.ret,Plan.boundaries]
  | succ fuel ih =>
    have ha := run_bound G x false
    have hb := run_bound G x true
    simp only [scan,right_sound,LinearMenu.lower,Plan.boundaries]
    by_cases h : ((G.localLevels id).trace id x).2.Nonempty
    · simp only [dif_pos h]
      have hh := ih (((G.localLevels id).trace id x).2.min' h)
      simp only [Nat.mul_add,Nat.mul_one]; omega
    · simp [h,Work.ret]; omega

def outer (G : Graph n) := (2*G.total+1)*(2*(G.total*G.total)+1)+1
def fuel (G : Graph n) := G.budget*G.budget+1

theorem outputs_spec {k : ℕ} (S : SNN n k) (hk : 0<k) (p : Part n) :
    p ∈ (scan (script S.graph (input S.graph)) (fuel S.graph) 0).val ↔
    ∃ r : ℝ, 0 ≤ r ∧ S.RawReturns r id p := by
  rw [← List.mem_toFinset,scan_spec]
  exact S.louvain_enumeration_exact hk p
end Metered
end Louvain
