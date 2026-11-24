import ScoredPath

/- Two vertices joined by one unit Jaccard edge. The reference scores are
   computed by hand: 1 − 1 = 0 and 0 − (1/4 + 1/4) = −1/2. -/
namespace ScoredExample
open Louvain Louvain.Metered

def graph : SNN 2 1 where
  neighbors := fun _ => {0}
  size_eq := by simp
  keep := fun _ _ => true
  keep_symm := fun _ _ => rfl

def labels (p : Part 2) : List ℕ := (List.finRange 2).map fun i => (p i).val

def check : IO Unit := do
  let run := enumerateAndScore graph
  let scored := run.val.scores.map fun (p,q) => (labels p,q)
  let winners := run.val.best.map fun (p,q) => (labels p,q)
  unless scored.length = 2 ∧ ([0,0], (0:ℚ)) ∈ scored ∧ ([0,1], (-1/2:ℚ)) ∈ scored ∧
      winners = [([0,0], (0:ℚ))] do
    throw (IO.userError s!"Unexpected exact scores or maximizers: {scored}, {winners}")
  IO.println s!"scores = {scored}; best = {winners}; arithmetic RAM charge = {run.steps}"

end ScoredExample

def main : IO Unit := ScoredExample.check
