import RawJaccard

/- A six-cell regression example. Cells are numbered 0 through 5.
The proof of the general theorem does not depend on this example. -/
namespace EndpointExample
open Louvain
def neighbors (i : Fin 6) : Finset (Fin 6) :=
  match i.val with
  | 0 => {0,1,2}
  | 1 => {1,2,5}
  | 2 => {0,1,2}
  | 3 => {2,3,4}
  | 4 => {0,4,5}
  | _ => {0,1,5}

def data : SNN 6 3 where
  neighbors := neighbors
  size_eq := by decide
  keep := fun _ _ => true
  keep_symm := fun _ _ => rfl

def runAt (x : ℚ) : Part 6 :=
  (data.graph.localLevels id).run fun m => pointQ id m x
def labels (p : Part 6) := (List.finRange 6).map fun i => (p i).val

def checkFixture : IO Unit := do
  let x : ℚ := 108 / 95
  let left := runAt (x - 1/100000)
  let atX := runAt x
  let rightSide := runAt (x + 1/100000)
  let plan := data.graph.localLevels id
  let leftTrace := plan.trace id (x - 1/100000)
  let rightTrace := plan.trace id x
  let outputs := data.graph.localOutputs
  if h : leftTrace.2.Nonempty then
    unless leftTrace.2.min' h = x do
      throw (IO.userError "Left interval does not end at the expected breakpoint")
  else
    throw (IO.userError "No left breakpoint")
  unless left = leftTrace.1 ∧ left = rightTrace.1 ∧ left = rightSide ∧ atX ≠ left ∧
      atX ∈ outputs ∧ left ∈ outputs do
    throw (IO.userError "Endpoint regression failed")
  IO.println s!"left = {labels left}, point = {labels atX}, right = {labels rightSide}"
  IO.println s!"distinct outputs = {outputs.card}"

end EndpointExample

def main : IO Unit := EndpointExample.checkFixture
