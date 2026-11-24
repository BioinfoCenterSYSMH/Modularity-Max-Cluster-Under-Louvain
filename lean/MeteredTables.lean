import Decisions

/- A unit-cost arithmetic RAM. Tables are finite indexed values. 'tab' evaluates
   every entry ONCE, paying for all entries; subsequent indexing is a scalar
   read. Writes to a live scratch vector and exact integer/rational operations
   are unit-cost. These are algorithm costs, not Lean VM or bit costs. -/
namespace Louvain
open Finset
open scoped BigOperators

structure Work (α : Type) where
  val : α
  steps : ℕ

namespace Work
variable {α β : Type}
def ret (x : α) : Work α := ⟨x,0⟩
def thenDo (x : Work α) (f : α → Work β) : Work β :=
  let y := f x.val
  ⟨y.val,x.steps+y.steps⟩
def tab {n : ℕ} (f : Fin n → Work α) : Work (Fin n → α) :=
  ⟨fun i => (f i).val, (∑ i, (f i).steps)+n⟩
def sum {n : ℕ} (f : Fin n → Work ℕ) : Work ℕ :=
  ⟨∑ i, (f i).val,(∑ i, (f i).steps)+n⟩
theorem bounded_sum {n a : ℕ} (f : Fin n → ℕ) (h : ∀ i, f i ≤ a) :
    ∑ i, f i ≤ n*a := by
  simpa using (Finset.sum_le_sum (s := (univ : Finset (Fin n))) (g := fun _ => a) (fun i _ => h i))
end Work

namespace Metered
variable {n : ℕ}
structure Input (n : ℕ) where
  w : Fin n → Fin n → ℕ
  d : Fin n → ℕ
  t : ℕ
structure Cache (n : ℕ) where
  col : Fin n → Fin n → ℕ
  vol : Fin n → ℕ

/-- Input is the already integer-weighted adjacency matrix. Reading one entry,
    adding to a row and writing the cached degree are charged by the operators. -/
def prepare (G : Graph n) : Work (Input n) :=
  (Work.tab fun a => Work.sum (fun b => ⟨G.weight a b,1⟩)).thenDo fun ds =>
    (Work.sum (fun a => ⟨ds a,1⟩)).thenDo fun T => Work.ret ⟨G.weight,ds,T⟩

theorem prepare_val (G : Graph n) :
    (prepare G).val = ⟨G.weight,G.deg,G.total⟩ := rfl

/-- Rebuild dense block-to-cell columns on contraction. The cubic construction
    is paid once per level. It keeps the starting graph and its original degrees. -/
def build (g : Input n) (u : Part n) : Work (Cache n) :=
  (Work.tab fun i => Work.tab fun b =>
    if u b = i then (⟨0,2⟩ : Work ℕ)
    else let z := Work.sum (fun a => (⟨if u a = i then g.w a b else 0,3⟩ : Work ℕ))
         ⟨z.val,z.steps+2⟩).thenDo fun c =>
  (Work.tab fun i => Work.sum (fun a => (⟨if u a = i then g.d a else 0,3⟩ : Work ℕ))).thenDo
    fun v => Work.ret ⟨c,v⟩

def input (G : Graph n) : Input n := (prepare G).val
def cache (G : Graph n) (u : Part n) := (build (input G) u).val

theorem col_correct (G : Graph n) (u : Part n) (i b : Fin n) :
    (cache G u).col i b = G.column u i b := by
  simp only [cache,build,Work.tab,Work.sum,Work.thenDo,Work.ret,Graph.column,input,prepare_val]
  split <;> rfl

theorem vol_correct (G : Graph n) (u : Part n) (i : Fin n) :
    (cache G u).vol i = G.volU u i := rfl

theorem prepare_steps (G : Graph n) : (prepare G).steps ≤ 5*(n+1)^2 := by
  simp [prepare,Work.thenDo,Work.ret,Work.sum,Work.tab]; nlinarith

theorem build_steps (g : Input n) (u : Part n) : (build g u).steps ≤ 16*(n+1)^3 := by
  have hb (i b : Fin n) :
      (if u b = i then (⟨0,2⟩ : Work ℕ) else
       let z := Work.sum (fun a => (⟨if u a = i then g.w a b else 0,3⟩ : Work ℕ))
       (⟨z.val,z.steps+2⟩ : Work ℕ)).steps ≤ 4*n+2 := by
    split <;> simp [Work.sum]
    omega
  have hrow (i : Fin n) := Work.bounded_sum _ (hb i)
  unfold build Work.thenDo Work.ret Work.tab
  dsimp only
  have hrows := Work.bounded_sum _ (fun i => Nat.add_le_add_right (hrow i) n)
  simp [Work.sum] at *
  nlinarith [Nat.zero_le (n*n*n), Nat.zero_le (n*n)]

/-- Bucket additions, stack operations, label/degree reads, vector writes and
    initialization are charged here. 'scatter' visits precisely the input list. -/
def bucket (p : Part n) (w : Fin n → ℕ) (readCost : ℕ) : Work (Vector ℕ n) :=
  let b := Dense.bucket p w
  ⟨b.1, n + (readCost+6)*b.2⟩

structure Rows where
  labels : List ℕ
  form : ℕ → Form

/-- Rows for one moving block. Only n original cells and n possible target labels
    are scanned; the cached columns avoid an all-edge scan per target. -/
def rows (g : Input n) (c : Cache n) (u p : Part n) (i : Fin n) : Work Rows :=
  (bucket p (c.col i) 2).thenDo fun links =>
  (bucket p (fun b => if u b = i then 0 else g.d b) 3).thenDo fun vols =>
  (Work.tab fun t : Fin n => (⟨Graph.fastLine vols links g.t (c.vol i) t,7⟩ : Work Form)).thenDo fun fs =>
    let candidates := 0 :: ((List.finRange n).filter (fun t => 0 < links[t.val])).map (fun t => t.val+1)
    -- One pass with at most a read, comparison, increment and list operations per target.
    ⟨⟨candidates,fun j => fs (Graph.target p i j)⟩, 8*n+1⟩

theorem rows_bounds (g : Input n) (c : Cache n) (u p : Part n) (i : Fin n) :
    (rows g c u p i).steps ≤ 40*(n+1) ∧
    (rows g c u p i).val.labels.length ≤ n+1 := by
  constructor
  · simp [rows,Work.thenDo,bucket,Work.tab,Dense.bucket,Dense.scatter_adds]; omega
  · simp only [rows,Work.thenDo,List.length_cons,List.length_map]
    exact Nat.succ_le_succ ((List.length_filter_le _ _).trans_eq List.length_finRange)

theorem rows_form (G : Graph n) (u p : Part n) (i : Fin n) (j : ℕ) :
    (rows (input G) (cache G u) u p i).val.form j = (G.localMenu u p i).form j := by
  simp only [rows,Work.thenDo,Work.tab,bucket,col_correct,vol_correct]
  rw [show (cache G u).col i = G.column u i from funext (col_correct G u i)]
  change Graph.fastLine (G.volumesTable u p i).1 (G.linksTable u p i).1 G.total (G.volU u i) _ = _
  exact G.fastLine_correct ..

theorem rows_labels (G : Graph n) (u p : Part n) (i : Fin n) :
    (rows (input G) (cache G u) u p i).val.labels.toFinset = (G.localMenu u p i).options := by
  rw [← show G.targets u p i = (G.localMenu u p i).options from rfl,← G.fastTargets_correct]
  simp only [rows,Work.thenDo,bucket,List.toFinset_cons,Graph.linksTable]
  rw [show (cache G u).col i = G.column u i from funext (col_correct G u i)]
  congr 1

end Metered
end Louvain
