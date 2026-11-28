import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring

namespace Louvain.SeuratExact

/-- A deterministic source of node orders. Its state is threaded through
levels, iterations and restarts. A seeded shuffle is one instance. -/
structure OrderSource (State : Type) (n : ℕ) where
  next : State → List (Fin n) → List (Fin n) × State
  perm : ∀ state units, (next state units).1.Perm units

private def swapPositions {α : Type} (xs : List α) (i j : ℕ) : List α :=
  if hi : i < xs.length then
    if hj : j < xs.length then
      List.ofFn (fun index => xs.get (Equiv.swap ⟨i, hi⟩ ⟨j, hj⟩ index))
    else xs
  else xs

private theorem swapPositions_perm {α : Type} (xs : List α) (i j : ℕ) :
    (swapPositions xs i j).Perm xs := by
  unfold swapPositions
  split
  · rename_i hi
    split
    · rename_i hj
      simpa only [Function.comp_apply, List.ofFn_get] using
        (Equiv.swap (⟨i, hi⟩ : Fin xs.length) ⟨j, hj⟩).ofFn_comp_perm xs.get
    · exact List.Perm.refl xs
  · exact List.Perm.refl xs

/-- Seurat performs one swap at each position in increasing order. Its random
partner is drawn from the entire list, including positions already visited. -/
private def swapLoop {State α : Type} (draw : State → ℕ → ℕ × State) (size : ℕ) :
    ℕ → ℕ → State → List α → List α × State
  | 0, _, state, xs => (xs, state)
  | remaining + 1, i, state, xs =>
    let (j, state') := draw state size
    swapLoop draw size remaining (i + 1) state' (swapPositions xs i j)

private theorem swapLoop_perm {State α : Type} (draw : State → ℕ → ℕ × State) (size : ℕ)
    (remaining i : ℕ) (state : State) (xs : List α) :
    (swapLoop draw size remaining i state xs).1.Perm xs := by
  induction remaining generalizing i state xs with
  | zero => exact List.Perm.refl xs
  | succ remaining ih =>
    unfold swapLoop
    rcases draw state size with ⟨j, state'⟩
    exact (ih (i + 1) state' (swapPositions xs i j)).trans (swapPositions_perm xs i j)

def swapOrderSource {State : Type} {n : ℕ} (draw : State → ℕ → ℕ × State) : OrderSource State n where
  next state xs := swapLoop draw xs.length xs.length 0 state xs
  perm state xs := swapLoop_perm draw xs.length xs.length 0 state xs

namespace JavaRandom

def multiplier : ℕ := 0x5DEECE66D
def modulus : ℕ := 2^48
def upper31 : ℕ := 2^31

/-- The low 48 bits of the seed after the scramble in `setSeed`. -/
def seedState (seed : ℕ) : ℕ := (seed ^^^ multiplier) % modulus

def step (state : ℕ) : ℕ := (state * multiplier + 11) % modulus

def next31 (state : ℕ) : ℕ × ℕ :=
  let state' := step state
  (state' / 2^17, state')

private def advance (state : ℕ) := state * multiplier + 11

private def jumpMultiplier : ℕ → ℕ
  | 0 => multiplier
  | p + 1 => jumpMultiplier p * jumpMultiplier p

private def jumpIncrement : ℕ → ℕ
  | 0 => 11
  | p + 1 => (jumpMultiplier p + 1) * jumpIncrement p

private theorem advance_jump (p state : ℕ) :
    (advance^[2^p]) state = state * jumpMultiplier p + jumpIncrement p := by
  induction p generalizing state with
  | zero => simp [advance, jumpMultiplier, jumpIncrement]
  | succ p ih =>
    rw [pow_succ, Nat.mul_two, Function.iterate_add_apply, ih, ih]
    simp only [jumpMultiplier, jumpIncrement]
    ring

private theorem jump_coefficients (p : ℕ) :
    ∃ a b : ℕ, jumpMultiplier p = 1 + 4 * 2^p * a ∧ jumpIncrement p = 2^p + 2 * 2^p * b := by
  induction p with
  | zero => exact ⟨6303725979, 5, by decide, by decide⟩
  | succ p ih =>
    obtain ⟨a, b, ha, hb⟩ := ih
    refine ⟨a + 2 * 2^p * a * a, b + 2^p * a * (1 + 2*b), ?_, ?_⟩
    · rw [jumpMultiplier, ha, pow_succ]
      ring
    · rw [jumpIncrement, ha, hb, pow_succ]
      ring

private theorem step_iterate (t state : ℕ) (hs : state < modulus) :
    (step^[t]) state = (advance^[t]) state % modulus := by
  induction t with
  | zero => simp [Nat.mod_eq_of_lt hs]
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    change (((advance^[t]) state % modulus * multiplier + 11) % modulus) =
      (((advance^[t]) state * multiplier + 11) % modulus)
    rw [← Nat.mod_add_mod ((advance^[t]) state % modulus * multiplier),
      Nat.mod_mul_mod, Nat.mod_add_mod]

private theorem advance_bit (p state : ℕ) :
    (advance^[2^p]) state % (2^p * 2) = (state + 2^p) % (2^p * 2) := by
  obtain ⟨a, b, ha, hb⟩ := jump_coefficients p
  rw [advance_jump, ha, hb]
  have he : state * (1 + 4 * 2^p * a) + (2^p + 2 * 2^p * b) =
      (state + 2^p) + (2^p * 2) * (2 * state * a + b) := by ring
  rw [he, Nat.add_mul_mod_self_left]

/-- If two different residues have the same low bits, adding `half` to either
toggles the leading bit and therefore gives the other residue. -/
private theorem toggle (half x y : ℕ) (hpos : 0 < half)
    (hx : x < half * 2) (hy : y < half * 2) (he : x % half = y % half)
    (hne : x ≠ y) : (x + half) % (half * 2) = y := by
  have casesOf (z : ℕ) (hz : z < half * 2) : z = z % half ∨ z = z % half + half := by
    have hd : z / half < 2 := (Nat.div_lt_iff_lt_mul hpos).2 (by omega)
    have hs := Nat.mod_add_div z half
    have hcases : z / half = 0 ∨ z / half = 1 :=
      (Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hd)).imp
        (fun h => Nat.eq_zero_of_le_zero (Nat.lt_succ_iff.mp h)) id
    rcases hcases with h | h
    · left; simp [h] at hs; exact hs.symm
    · right; simp [h] at hs; exact hs.symm
  rcases casesOf x hx with hx' | hx' <;> rcases casesOf y hy with hy' | hy'
  · exfalso; exact hne (hx'.trans (he.trans hy'.symm))
  · have hs : x + half = y := by omega
    rw [hs, Nat.mod_eq_of_lt hy]
  · have hs : x + half = y + half * 2 := by omega
    rw [hs, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
  · exfalso; exact hne (by omega)

private theorem advance_covers (p seed target : ℕ) :
    ∃ t < 2^p, (advance^[t]) seed % (2^p) = target % (2^p) := by
  induction p with
  | zero => exact ⟨0, by decide, by simp [Nat.mod_one]⟩
  | succ p ih =>
    obtain ⟨t, ht, hlow⟩ := ih
    let half := 2^p
    let reached := (advance^[t]) seed
    let first := reached % (half * 2)
    let wanted := target % (half * 2)
    have hp : 0 < half := Nat.pow_pos (by decide)
    have hfix : first % half = wanted % half := by
      dsimp only [first, wanted]
      have hd : half ∣ half * 2 := ⟨2, rfl⟩
      rw [Nat.mod_mod_of_dvd reached hd, Nat.mod_mod_of_dvd target hd]
      exact hlow
    by_cases h : first = wanted
    · exact ⟨t, by rw [pow_succ]; omega, h⟩
    · refine ⟨half + t, by rw [pow_succ]; omega, ?_⟩
      rw [pow_succ, Function.iterate_add_apply, advance_bit, ← Nat.mod_add_mod reached]
      exact toggle half first wanted hp (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hfix h

/-- Every reduced state is visited in at most one period of the 48-bit generator. -/
theorem step_covers {seed target : ℕ} (hs : seed < modulus) (ht : target < modulus) :
    ∃ t < modulus, (step^[t]) seed = target := by
  obtain ⟨t, ht', h⟩ := advance_covers 48 seed target
  refine ⟨t, ht', ?_⟩
  rw [step_iterate t seed hs, modulus, h]
  exact Nat.mod_eq_of_lt ht

/-- The rejection condition from Java's bounded draw, expressed without
signed overflow. An exhausted search reports failure. -/
def accepts (n next : ℕ) : Prop :=
  let bits := next / 2^17
  bits - bits % n + (n - 1) < upper31

instance (n next : ℕ) : Decidable (accepts n next) := by unfold accepts; infer_instance

private def seek (move : ℕ → ℕ) (eligible : ℕ → Prop) [DecidablePred eligible] :
    ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, state =>
    let next := move state
    if eligible next then some next else seek move eligible fuel next

def rejection (n fuel state : ℕ) : Option (ℕ × ℕ) :=
  (seek step (accepts n) fuel state).map fun next => (next / 2^17 % n, next)

private theorem accepts_zero (n : ℕ) (hn : n < upper31) : accepts n 0 := by
  simpa only [accepts, Nat.zero_div, Nat.zero_mod, Nat.sub_zero, Nat.zero_add] using
    (Nat.sub_le n 1).trans_lt hn

private theorem seek_ne_none (move : ℕ → ℕ) (eligible : ℕ → Prop) [DecidablePred eligible]
    {fuel t state target : ℕ} (valid : eligible target) (ht : t < fuel)
    (hit : (move^[t]) (move state) = target) : seek move eligible fuel state ≠ none := by
  induction fuel generalizing state t with
  | zero => exact (Nat.not_lt_zero _ ht).elim
  | succ fuel ih =>
    rw [seek]
    by_cases h : eligible (move state)
    · rw [if_pos h]; exact Option.some_ne_none _
    · rw [if_neg h]
      cases t with
      | zero =>
        change move state = target at hit
        exact (h (hit ▸ valid)).elim
      | succ t =>
        exact ih (Nat.lt_of_succ_lt_succ ht)
          ((Function.iterate_succ_apply move t (move state)).symm.trans hit)

/-- A positive 31-bit bound always has an accepted draw before the rejection
fuel runs out: the generator must reach state zero, whose draw is accepted. -/
theorem rejection_completes (n state : ℕ) (hn : n < upper31) :
    rejection n modulus state ≠ none := by
  have hp : 0 < modulus := by decide
  have hs : step state < modulus := Nat.mod_lt _ hp
  obtain ⟨t, ht, hit⟩ := step_covers hs hp
  have h := seek_ne_none step (accepts n) (accepts_zero n hn) ht hit
  intro contra
  apply h
  simpa only [rejection, Option.map_eq_none_iff] using contra

/-- The set of permitted C++ bounds uses positive 31-bit integers. This
implementation records the finite-state rejection search explicitly. -/
def nextInt (state n : ℕ) : ℕ × ℕ :=
  if n = 0 then (0, state) else
  if n &&& (n - 1) = 0 then
    let (bits, next) := next31 state
    (n * bits / upper31, next)
  else (rejection n modulus state).getD (0, state)

/-- Every draw used by the shuffle is a valid position in Seurat's positive
31-bit bound domain. -/
theorem nextInt_lt (state n : ℕ) (positive : 0 < n) (bounded : n < upper31) :
    (nextInt state n).1 < n := by
  unfold nextInt
  rw [if_neg (Nat.ne_of_gt positive)]
  split
  · have hp : 0 < (2 : ℕ)^17 := by decide
    have hupper : 0 < upper31 := by decide
    have hs : step state < modulus := Nat.mod_lt _ (by decide)
    have hbits : step state / 2^17 < upper31 := by
      apply (Nat.div_lt_iff_lt_mul hp).2
      rw [show upper31 * 2^17 = modulus by decide]
      exact hs
    change n * (step state / 2^17) / upper31 < n
    exact (Nat.div_lt_iff_lt_mul hupper).2 (Nat.mul_lt_mul_of_pos_left hbits positive)
  · cases h : seek step (accepts n) modulus state with
    | none => exact (rejection_completes n state bounded (by simp [rejection, h])).elim
    | some next =>
      simp only [rejection, h, Option.map_some, Option.getD_some]
      exact Nat.mod_lt _ positive

def orderSource {n : ℕ} : OrderSource ℕ n := swapOrderSource nextInt

/-- Seed zero, six positions, then eight positions drawn from the continued
state. The outputs check both bounded draw branches and the swap order. -/
example :
    let first := (orderSource (n := 6)).next (seedState 0) (List.finRange 6)
    let second := (orderSource (n := 8)).next first.2 (List.finRange 8)
    (first.1.map Fin.val, second.1.map Fin.val, second.2) =
      ([0, 2, 4, 5, 3, 1], [1, 4, 5, 3, 7, 2, 6, 0], 172554225307659) := by decide

/-- The first draw for this bound is rejected, so the result exercises the
state update on the rejection branch. -/
example : nextInt (seedState 0) 1073741825 = (516548029, 67704983304270) := by decide

end JavaRandom

end Louvain.SeuratExact
