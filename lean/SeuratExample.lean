import SeuratJaccard
import SeuratStackFlow

open Louvain Louvain.SeuratExact

private def cycle : Graph 4 where
  weight i j := if (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val then 1 else 0
  symm i j := by simp [or_comm]
  loopless i := by
    have hi := i.isLt
    have different : (i.val + 1) % 4 ≠ i.val := by omega
    simp [different]

private def labels (p : Part 4) : List ℕ := (List.finRange 4).map (fun i => (p i).val)

private def traceAt (seed : ℕ) (r : ℚ) : Part 4 :=
  (exactPlan cycle JavaRandom.orderSource (JavaRandom.seedState seed) false 10 10).run
    (fun m => pointQ cycle.form m r)

def main : IO Unit := do
  let atZero := labels (traceAt 4 0)
  let seedZero := labels (traceAt 0 1)
  let seedFour := labels (traceAt 4 1)
  let atTwo := labels (traceAt 4 2)
  unless atZero == [0, 0, 0, 0] && seedZero == [0, 0, 2, 2] &&
      seedFour == [0, 1, 1, 0] && atTwo == [0, 1, 2, 3] do
    throw (IO.userError s!"Unexpected cycle partitions {atZero}, {seedZero}, {seedFour}, {atTwo}")
  let path := SeuratRoots.enumerate cycle
    (exactPlan cycle JavaRandom.orderSource (JavaRandom.seedState 4) false 10 10)
  unless path.card == 3 && decide (seedFour ∈ path.image labels) do
    throw (IO.userError s!"Unexpected resolution path with {path.card} partitions")
  IO.println s!"Four-cycle check passed: seed 0 at r=1 gives {seedZero}, seed 4 gives {seedFour}"
  IO.println s!"The full seed-4 path contains {path.card} distinct partitions"
