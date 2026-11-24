import MeteredScores
namespace Louvain
open Finset
namespace Metered
variable {n k : ℕ}

/-- Materialize the fixed-k integer weight matrix once. Each membership test
    may scan k integer neighbour IDs. The symmetric pruning mask is an input. -/
def edgeWork (S : SNN n k) (scale : ℕ) (a b : Fin n) : Work ℕ :=
  if a ≠ b ∧ S.keep a b = true then
    let l := List.finRange n
    let hits := Work.filterL (fun v : Fin n =>
      (⟨decide (v ∈ S.neighbors a ∧ v ∈ S.neighbors b),4*k+4⟩ : Work Bool)) l
    let s := hits.val.length
    ⟨s*(scale/(2*k-s)),hits.steps+l.length+s+10⟩
  else ⟨0,4⟩

theorem edge_answer (S : SNN n k) (a b : Fin n) :
    (edgeWork S (SNN.scale k) a b).val = S.graph.weight a b := by
  change _ = S.edge a b
  simp only [edgeWork,SNN.edge,Work.filterL_val]
  split
  · let hit := fun v : Fin n => decide (v ∈ S.neighbors a ∧ v ∈ S.neighbors b)
    let l := (List.finRange n).filter hit
    have nd : l.Nodup := (List.nodup_finRange n).filter _
    have hs : l.toFinset = S.neighbors a ∩ S.neighbors b := by ext; simp [l,hit]
    have h : l.length = S.overlap a b :=
      (List.toFinset_card_of_nodup nd).symm.trans (congrArg Finset.card hs)
    change l.length * (SNN.scale k / (2*k-l.length)) = _
    rw [h]
  · rfl

theorem edge_steps (S : SNN n k) (s : ℕ) (a b : Fin n) :
    (edgeWork S s a b).steps ≤ 16*(k+1)*(n+1) := by
  unfold edgeWork; split
  · let l := List.finRange n
    let ok := fun v : Fin n => (⟨decide (v ∈ S.neighbors a ∧ v ∈ S.neighbors b),4*k+4⟩ : Work Bool)
    have hf := Work.filterL_bound (b:=4*k+4) ok (fun _ => le_rfl) l
    have hl : l.length = n := List.length_finRange
    have hs : (Work.filterL ok l).val.length ≤ n := by rw [Work.filterL_val]; exact (List.length_filter_le ..).trans_eq hl
    change (Work.filterL ok l).steps+l.length+(Work.filterL ok l).val.length+10 ≤ _
    rw [hl] at hf ⊢; nlinarith [Nat.zero_le (k*n)]
  · dsimp only; nlinarith [Nat.zero_le (k*n)]

def factorialW : ℕ → Work ℕ
  | 0 => ⟨1,1⟩
  | m+1 => let f := factorialW m; ⟨(m+1)*f.val,f.steps+3⟩

theorem factorial_answer (m : ℕ) : (factorialW m).val = m.factorial := by
  induction m <;> simp_all [factorialW,Nat.factorial_succ]
theorem factorial_steps (m : ℕ) : (factorialW m).steps = 3*m+1 := by
  induction m <;> simp_all [factorialW,Nat.mul_succ,Nat.add_assoc]

def matrixWork (S : SNN n k) := (factorialW (2*k)).thenDo fun s =>
  Work.tab fun a => Work.tab fun b => edgeWork S s a b

theorem matrix_val (S : SNN n k) : (matrixWork S).val = S.graph.weight := by
  funext a b
  simp only [matrixWork,Work.thenDo,Work.tab,factorial_answer]
  exact edge_answer S a b

def inputGraph (S : SNN n k) : Work (Graph n) :=
  let m := matrixWork S
  ⟨⟨m.val,by rw [show m.val=S.graph.weight from matrix_val S]; exact S.graph.symm,
          by rw [show m.val=S.graph.weight from matrix_val S]; exact S.graph.loopless⟩,m.steps+2⟩

theorem inputGraph_val (S : SNN n k) : (inputGraph S).val = S.graph := by
  have extW (a b : Graph n) (h : a.weight=b.weight) : a=b := by
    cases a; cases b; congr
  exact extW _ _ (matrix_val S)

theorem inputGraph_steps (S : SNN n k) : (inputGraph S).steps ≤ 32*(k+1)*(n+1)^3 := by
  let s := (factorialW (2*k)).val
  have h (a : Fin n) := Work.bounded_sum _ (edge_steps S s a)
  have hh := Work.bounded_sum _ (fun a => Nat.add_le_add_right (h a) n)
  simp only [inputGraph,matrixWork,Work.thenDo,Work.tab,factorial_steps]
  change 3*(2*k)+1+((∑ a, ((∑ b, (edgeWork S s a b).steps) + n))+n)+2 ≤ _
  nlinarith [Nat.zero_le (k*k*n*n),Nat.zero_le (k*n*n),Nat.zero_le (n*n),
    Nat.zero_le (k*k*n),Nat.zero_le (k*n),Nat.zero_le (k*k),Nat.zero_le (k*n*n*n),Nat.zero_le (n*n*n)]

/-- Fixed point and right-limit scan, deduplication, exact scores, and all ties.
    The actual program computes both fuel values from the cached total weight. -/
def onGraph (G : Graph n) : Work (Result n) :=
  (prepare G).thenDo fun g =>
    let B := (g.t+1)*(g.t*g.t+1)
    let pg := levels g (B+1) (n+1) id
    let l := scan pg (B*B+1) 0
    let ranked := rankAll g l.val
    ⟨ranked.val,12+l.steps+ranked.steps⟩
def enumerateAndScore (S : SNN n k) := (inputGraph S).thenDo onGraph

theorem program_contents (S : SNN n k) :
    (enumerateAndScore S).val =
      (rankAll (input S.graph) (scan (script S.graph (input S.graph)) (fuel S.graph) 0).val).val := by
  simp only [enumerateAndScore,Work.thenDo,inputGraph_val]; rfl

theorem scores_exact (S : SNN n k) (hk : 0<k) (p : Part n) (q : ℚ) :
    (p,q) ∈ (enumerateAndScore S).val.scores ↔
    (∃ r : ℝ, 0 ≤ r ∧ S.RawReturns r id p) ∧ q = classical (input S.graph) p := by
  rw [program_contents,rank_scores,outputs_spec S hk]

theorem best_exact (S : SNN n k) (p : Part n) (q : ℚ) :
    (p,q) ∈ (enumerateAndScore S).val.best ↔
    (p,q) ∈ (enumerateAndScore S).val.scores ∧ ∀ w ∈ (enumerateAndScore S).val.scores, w.2 ≤ q := by
  rw [program_contents]; exact rank_best ..

end Metered
end Louvain
