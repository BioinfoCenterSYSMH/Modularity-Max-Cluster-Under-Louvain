import Jaccard

namespace Louvain.SeuratRoots
open Finset

private def difference {b : ℕ} (i j : Fin (b + 1)) : Fin (2 * b + 1) :=
  ⟨i.val + b - j.val, by have := i.isLt; omega⟩

private theorem difference_cast {b : ℕ} (i j : Fin (b + 1)) :
    ((difference i j).val : ℚ) - b = (i.val : ℚ) - j.val := by
  have h : j.val ≤ i.val + b := by have := j.isLt; omega
  simp only [difference, Nat.cast_sub h, Nat.cast_add]
  ring

variable {n : ℕ} (G : Graph n)

/-- All possible intersections are indexed by the differences of the two
integer coefficients. This is a proof-only set, never materialized by `collect`. -/
def breakpointSet : Finset ℚ :=
  let B := G.total
  (univ : Finset (Fin (2 * B + 1) × Fin (2 * (B * B) + 1))).image fun d =>
    (B : ℚ) * ((d.1.val : ℚ) - B) / ((d.2.val : ℚ) - (B * B : ℕ))

theorem roots_subset : Plan.roots G.form ⊆ breakpointSet G := by
  intro z hz
  obtain ⟨⟨a, b⟩, _, rfl⟩ := mem_image.mp hz
  apply mem_image.mpr
  refine ⟨(difference a.1 b.1, difference a.2 b.2), mem_univ _, ?_⟩
  change (G.total : ℚ) * (((difference a.1 b.1).val : ℚ) - G.total) /
    (((difference a.2 b.2).val : ℚ) - (G.total * G.total : ℕ)) = _
  rw [difference_cast, difference_cast]
  simp only [root, Graph.form]
  ring

/-- Number of critical-point/right-limit pairs sufficient for adaptive scanning. -/
def attemptBudget : ℕ := (2 * G.total + 1) * (2 * (G.total * G.total) + 1) + 1

theorem roots_card_le : (Plan.roots G.form).card < attemptBudget G := by
  have h := card_le_card (roots_subset G)
  have hb : (breakpointSet G).card ≤ (2 * G.total + 1) * (2 * (G.total * G.total) + 1) := by
    apply card_image_le.trans_eq
    simp
  unfold attemptBudget
  omega

variable {α : Type}

/-- Count the actual boundary evaluations used by `Plan.collect`. -/
def boundaries (p : Plan G.Code α) : ℕ → ℚ → ℕ
  | 0, _ => 0
  | fuel + 1, x =>
    let s := (p.trace G.form x).2
    1 + if h : s.Nonempty then boundaries p fuel (s.min' h) else 0

theorem boundaries_le_roots (p : Plan G.Code α) (fuel : ℕ) (x : ℚ) :
    boundaries G p fuel x ≤ (Plan.above (Plan.roots G.form) x).card + 1 := by
  induction fuel generalizing x with
  | zero => simp [boundaries]
  | succ fuel ih =>
    unfold boundaries
    dsimp only
    split
    · rename_i h
      let t := (p.trace G.form x).2.min' h
      have hm : t ∈ (p.trace G.form x).2 := min'_mem _ h
      have hd := Plan.drop_count (Plan.trace_roots G.form p x hm) (Plan.trace_gt G.form p x t hm)
      have hb := ih t
      change 1 + boundaries G p fuel t ≤ _
      omega
    · omega

theorem boundaries_le (p : Plan G.Code α) (fuel : ℕ) (x : ℚ) :
    boundaries G p fuel x ≤ attemptBudget G := by
  have h := (boundaries_le_roots G p fuel x).trans
    (Nat.add_le_add_right (card_filter_le _ _) 1)
  exact h.trans (roots_card_le G)

def enumerate [DecidableEq α] (p : Plan G.Code α) : Finset α :=
  Plan.collect G.form p (attemptBudget G) 0

theorem collect_card_le [DecidableEq α] (p : Plan G.Code α) (fuel : ℕ) (x : ℚ) :
    (Plan.collect G.form p fuel x).card ≤ 2 * boundaries G p fuel x := by
  induction fuel generalizing x with
  | zero => simp [Plan.collect, boundaries]
  | succ fuel ih =>
    let a := p.run (fun m => pointQ G.form m x)
    let b := (p.trace G.form x).1
    let cuts := (p.trace G.form x).2
    let rest : Finset α := if h : cuts.Nonempty then Plan.collect G.form p fuel (cuts.min' h) else ∅
    change (insert a (insert b rest)).card ≤ _
    have cardAB : (insert a (insert b rest)).card ≤ rest.card + 2 := by
      have ha := card_insert_le a (insert b rest)
      have hb := card_insert_le b rest
      omega
    apply cardAB.trans
    change rest.card + 2 ≤ 2 * (1 + if h : cuts.Nonempty then
      boundaries G p fuel (cuts.min' h) else 0)
    by_cases h : cuts.Nonempty
    · have hd := ih (cuts.min' h)
      have hr : rest = Plan.collect G.form p fuel (cuts.min' h) := dif_pos h
      rw [hr, dif_pos h]
      omega
    · have hr : rest = ∅ := dif_neg h
      simp [hr, dif_neg h]

theorem enumerate_card_le [DecidableEq α] (p : Plan G.Code α) :
    (enumerate G p).card ≤ 2 * attemptBudget G :=
  (collect_card_le G p _ _).trans (Nat.mul_le_mul_left 2 (boundaries_le G p _ _))

/-- Soundness and completeness over all nonnegative real resolutions, using the
smaller difference-pair budget. State threaded through the deterministic plan
may include a pseudorandom generator state. -/
theorem enumerate_exact [DecidableEq α] (p : Plan G.Code α) (y : α) :
    y ∈ enumerate G p ↔ ∃ r : ℝ, 0 ≤ r ∧ p.run (fun m => point G.form m r) = y := by
  have h : (Plan.above (Plan.roots G.form) 0).card < attemptBudget G :=
    (card_filter_le _ _).trans_lt (roots_card_le G)
  simpa only [enumerate, Rat.cast_zero] using Plan.collect_exact G.form p (attemptBudget G) 0 h y

/-- Number of candidate entries inspected along a single chosen branch. -/
def menuEntries (choose : Menu G.Code → ℕ) : Plan G.Code α → ℕ
  | .done _ => 0
  | .ask m next => m.options.card + menuEntries choose (next (choose m))

@[simp] theorem menuEntries_bind {β : Type} (choose : Menu G.Code → ℕ)
    (p : Plan G.Code α) (k : α → Plan G.Code β) :
    menuEntries G choose (p.bind k) = menuEntries G choose p +
      menuEntries G choose (k (p.run choose)) := by
  induction p with
  | done _ => simp [Plan.bind, Plan.run, menuEntries]
  | ask m next ih => simp [Plan.bind, Plan.run, menuEntries, ih, Nat.add_assoc]

private theorem replay_entries (p : Plan G.Code α) (x : ℚ) (r : ℝ) (hx : (x : ℝ) < r)
    (h : ∀ z ∈ (p.trace G.form x).2, r < (z : ℝ)) :
    menuEntries G (fun m => point G.form m r) p =
      menuEntries G (fun m => right G.form m x) p := by
  induction p with
  | done _ => rfl
  | ask m next ih =>
    simp only [Plan.trace, menuEntries] at h ⊢
    rw [replay_menu G.form m x r hx (fun z hz => h z (mem_union_left _ hz))]
    rw [ih _ (fun z hz => h z (mem_union_right _ hz))]

theorem rightEntries_le (p : Plan G.Code α) (bound : ℕ)
    (runBound : ∀ r : ℝ, 0 ≤ r → menuEntries G (fun m => point G.form m r) p ≤ bound)
    (x : ℚ) (hx : 0 ≤ x) :
    menuEntries G (fun m => right G.form m x) p ≤ bound := by
  let cuts := (p.trace G.form x).2
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  by_cases h : cuts.Nonempty
  · let t := cuts.min' h
    have hxt : (x : ℝ) < (t : ℝ) := by
      exact_mod_cast Plan.trace_gt G.form p x t (min'_mem _ h)
    obtain ⟨r, hxr, hrt⟩ := exists_between hxt
    rw [← replay_entries G p x r hxr (fun z hz =>
      hrt.trans_le (by exact_mod_cast cuts.min'_le z hz))]
    exact runBound r (hx'.trans hxr.le)
  · let r : ℝ := x + 1
    have hxr : (x : ℝ) < r := by dsimp [r]; linarith
    rw [← replay_entries G p x r hxr (fun z hz => (h ⟨z, hz⟩).elim)]
    exact runBound r (hx'.trans hxr.le)

/-- Entries traversed by the exact evaluation and trace at each visited boundary. -/
def scanEntries (p : Plan G.Code α) : ℕ → ℚ → ℕ
  | 0, _ => 0
  | fuel + 1, x =>
    let s := (p.trace G.form x).2
    menuEntries G (fun m => pointQ G.form m x) p + menuEntries G (fun m => right G.form m x) p +
      if h : s.Nonempty then scanEntries p fuel (s.min' h) else 0

theorem scanEntries_le (p : Plan G.Code α) (bound : ℕ)
    (runBound : ∀ r : ℝ, 0 ≤ r → menuEntries G (fun m => point G.form m r) p ≤ bound)
    (fuel : ℕ) (x : ℚ) (hx : 0 ≤ x) :
    scanEntries G p fuel x ≤ (2 * bound) * boundaries G p fuel x := by
  induction fuel generalizing x with
  | zero => simp [scanEntries, boundaries]
  | succ fuel ih =>
    have hp := runBound (x : ℝ) (by exact_mod_cast hx)
    simp only [pointQ_eq] at hp
    have pair : menuEntries G (fun m => pointQ G.form m x) p +
        menuEntries G (fun m => right G.form m x) p ≤ 2 * bound := by
      have hq : menuEntries G (fun m => pointQ G.form m x) p ≤ bound := by
        simpa only [pointQ_eq] using hp
      have hr := rightEntries_le G p bound runBound x hx
      omega
    simp only [scanEntries, boundaries]
    split
    · rename_i h
      let next := (p.trace G.form x).2.min' h
      have hn := (Plan.trace_gt G.form p x next (min'_mem _ h)).le
      change _ + scanEntries G p fuel next ≤ (2 * bound) * (1 + boundaries G p fuel next)
      simpa only [Nat.mul_add, Nat.mul_one] using Nat.add_le_add pair (ih next (hx.trans hn))
    · simpa using pair

theorem enumeration_entries_le (p : Plan G.Code α) (bound : ℕ)
    (runBound : ∀ r : ℝ, 0 ≤ r → menuEntries G (fun m => point G.form m r) p ≤ bound) :
    scanEntries G p (attemptBudget G) 0 ≤ 2 * bound * attemptBudget G :=
  (scanEntries_le G p bound runBound _ _ (le_refl 0)).trans
    (Nat.mul_le_mul_left _ (boundaries_le G p _ _))

end Louvain.SeuratRoots

namespace Louvain.SNN

def seuratAttemptsConstant (k : ℕ) : ℕ :=
  (2 * scale k + 1) * (2 * (scale k * scale k) + 1) + 1

def seuratScoreConstant (k : ℕ) : ℕ := (scale k + 1) * (scale k * scale k + 1)

theorem seurat_fixed_k_bounds {n k : ℕ} (S : SNN n k) (hk : 0 < k) :
    SeuratRoots.attemptBudget S.graph ≤ seuratAttemptsConstant k * (n + 1)^6 ∧
    S.graph.budget ≤ seuratScoreConstant k * (n + 1)^6 := by
  let a := scale k
  let N := n + 1
  let B := S.graph.total
  have hn : 1 ≤ N := Nat.le_add_left 1 n
  have bound : B ≤ a * N^2 := by
    calc B ≤ n * (n * a) := S.total_le hk
         _ = a * n^2 := by ring
         _ ≤ a * N^2 := by gcongr; exact Nat.le_succ n
  have square : B * B ≤ (a * a) * N^4 := by
    calc _ ≤ (a * N^2) * (a * N^2) := Nat.mul_le_mul bound bound
         _ = _ := by ring
  have pad {t c d : ℕ} (h : t ≤ c * N^d) : t + 1 ≤ (c + 1) * N^d := by
    simpa [Nat.add_mul] using Nat.add_le_add h (Nat.one_le_pow _ _ hn : 1 ≤ N^d)
  have b1 := pad bound
  have b2 := pad square
  have outer1 : 2 * B + 1 ≤ (2 * a + 1) * N^2 :=
    pad (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 bound)
  have outer2 : 2 * (B * B) + 1 ≤ (2 * (a * a) + 1) * N^4 :=
    pad (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 square)
  constructor
  · change (2 * B + 1) * (2 * (B * B) + 1) + 1 ≤
      ((2 * a + 1) * (2 * (a * a) + 1) + 1) * N^6
    apply pad
    calc _ ≤ ((2 * a + 1) * N^2) * ((2 * (a * a) + 1) * N^4) := Nat.mul_le_mul outer1 outer2
         _ = _ := by ring
  · change (B + 1) * (B * B + 1) ≤ ((a + 1) * (a * a + 1)) * N^6
    calc _ ≤ ((a + 1) * N^2) * ((a * a + 1) * N^4) := Nat.mul_le_mul b1 b2
         _ = _ := by ring

/-- If the fixed-resolution engine uses at most `c` times the size of the
score alphabet times `(n+1)^d` candidate entries, then adaptive enumeration
uses polynomially many candidate entries. `c` may depend on fixed restart
and outer-iteration counts. -/
theorem seurat_fixed_k_entries {n k c d : ℕ} (S : SNN n k) (hk : 0 < k)
    {α : Type} (p : Plan S.graph.Code α)
    (runBound : ∀ r : ℝ, 0 ≤ r →
      SeuratRoots.menuEntries S.graph (fun m => point S.graph.form m r) p ≤
        c * S.graph.budget * (n + 1)^d) :
    SeuratRoots.scanEntries S.graph p (SeuratRoots.attemptBudget S.graph) 0 ≤
      (2 * c * seuratScoreConstant k * seuratAttemptsConstant k) * (n + 1)^(d + 12) := by
  obtain ⟨attempts, scores⟩ := seurat_fixed_k_bounds S hk
  apply (SeuratRoots.enumeration_entries_le S.graph p _ runBound).trans
  calc _ ≤ 2 * (c * (seuratScoreConstant k * (n + 1)^6) * (n + 1)^d) *
      (seuratAttemptsConstant k * (n + 1)^6) := by gcongr
       _ = _ := by rw [pow_add]; ring

/-- Arithmetic bound for the full control budget. The local loop's fuel is
the length of a stability cycle times its bound on strictly improving states.
The factor `2*n` allows a local-moving and a refinement phase per level. -/
theorem seurat_fixed_k_control_budget {n k : ℕ} (S : SNN n k) (hk : 0 < k)
    (starts iterations restartOverhead : ℕ) :
    SeuratRoots.attemptBudget S.graph * (starts * (restartOverhead + iterations *
      (2 * n * (((S.graph.budget + 1) * (n + 1) * (n * n + 1) + 1) * n) * (n + 1)))) ≤
    (seuratAttemptsConstant k * starts *
      (restartOverhead + 2 * iterations * (seuratScoreConstant k + 2))) * (n + 1)^18 := by
  obtain ⟨ha, hs⟩ := seurat_fixed_k_bounds S hk
  let N := n + 1
  let C := seuratScoreConstant k
  have hn : n ≤ N := Nat.le_succ n
  have one (e : ℕ) : 1 ≤ N^e := Nat.one_le_pow _ _ (Nat.le_add_left 1 n)
  have square : n * n + 1 ≤ N^2 := by dsimp [N]; nlinarith
  have pad {a c d : ℕ} (h : a ≤ c * N^d) : a + 1 ≤ (c + 1) * N^d := by
    simpa [Nat.add_mul] using Nat.add_le_add h (one d)
  have rank : (S.graph.budget + 1) * N * (n * n + 1) ≤ (C + 1) * N^9 := by
    calc _ ≤ ((C + 1) * N^6) * N * N^2 := Nat.mul_le_mul (Nat.mul_le_mul_right N (pad hs)) square
         _ = _ := by ring
  have localBound : ((S.graph.budget + 1) * N * (n * n + 1) + 1) * n ≤ (C + 2) * N^10 := by
    calc _ ≤ ((C + 1 + 1) * N^9) * N := Nat.mul_le_mul (pad rank) hn
         _ = _ := by ring
  have iteration : 2 * n * (((S.graph.budget + 1) * N * (n * n + 1) + 1) * n) * N ≤
      (2 * (C + 2)) * N^12 := by
    calc _ ≤ 2 * N * ((C + 2) * N^10) * N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) localBound)
         _ = _ := by ring
  have withEntry : restartOverhead + iterations *
        (2 * n * (((S.graph.budget + 1) * N * (n * n + 1) + 1) * n) * N) ≤
      (restartOverhead + 2 * iterations * (C + 2)) * N^12 := by
    calc _ ≤ restartOverhead + iterations * ((2 * (C + 2)) * N^12) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ iteration) restartOverhead
         _ ≤ restartOverhead * N^12 + iterations * ((2 * (C + 2)) * N^12) := by
             have padOverhead := Nat.mul_le_mul_left restartOverhead (one 12)
             exact Nat.add_le_add_right (by simpa using padOverhead) _
         _ = _ := by ring
  calc _ ≤ (seuratAttemptsConstant k * N^6) *
        (starts * ((restartOverhead + 2 * iterations * (C + 2)) * N^12)) :=
        Nat.mul_le_mul ha (Nat.mul_le_mul_left starts withEntry)
       _ = _ := by dsimp [C, N]; ring

end Louvain.SNN
