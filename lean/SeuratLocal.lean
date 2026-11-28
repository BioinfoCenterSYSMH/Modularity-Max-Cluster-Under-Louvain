import LocalGain

namespace Louvain.SeuratExact
open Finset
open scoped BigOperators

variable {n : ℕ}

/-- Labels still occupied after temporarily removing the focal unit. -/
def remaining (u p : Part n) (a : Fin n) : Finset (Fin n) :=
  (univ.filter fun x => u x ≠ u a).image p

def targets (G : Graph n) (u p : Part n) (a : Fin n) : Finset (Fin n) :=
  univ.filter fun t => 0 < Graph.cross u p (u a) t G.weight

def labelAt (empty : Fin n) (index : ℕ) : Fin n :=
  if h : 0 < index ∧ index ≤ n then ⟨index - 1, by omega⟩ else empty

@[simp] theorem labelAt_zero (empty : Fin n) : labelAt empty 0 = empty := by
  simp [labelAt]

@[simp] theorem labelAt_succ (empty t : Fin n) : labelAt empty (t.val + 1) = t := by
  have h : 0 < t.val + 1 ∧ t.val + 1 ≤ n := by have := t.isLt; omega
  simp [labelAt, h]

/-- Zero is the empty label's priority. The other priorities follow occupied label IDs. -/
def menu (G : Graph n) (u p : Part n) (a empty : Fin n) : Menu G.Code := {
  options := insert 0 ((targets G u p a).image fun t => t.val + 1)
  nonempty := ⟨0, by simp⟩
  form := fun j => G.code (Graph.assign u p (u a) (labelAt empty j))
}

def visit (G : Graph n) (u p : Part n) (a empty : Fin n) : Plan G.Code (Part n) :=
  .ask (menu G u p a empty) fun j => .done (Graph.assign u p (u a) (labelAt empty j))

theorem assign_source (u p : Part n) (a : Fin n) (h : Graph.respects u p) :
    Graph.assign u p (u a) (p a) = p := by
  funext x
  by_cases hx : u x = u a
  · simp [Graph.assign, hx, h x a hx]
  · simp [Graph.assign, hx]

theorem occupied_after (u p : Part n) (a t : Fin n) :
    univ.image (Graph.assign u p (u a) t) = insert t (remaining u p a) := by
  ext c
  simp only [mem_image, mem_univ, true_and, mem_insert, remaining, mem_filter]
  constructor
  · rintro ⟨x, hx⟩
    by_cases h : u x = u a
    · exact Or.inl (by simpa [Graph.assign, h] using hx.symm)
    · exact Or.inr ⟨x, h, by simpa [Graph.assign, h] using hx⟩
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact ⟨a, by simp [Graph.assign]⟩
    · exact ⟨x, by simp [Graph.assign, hx]⟩

theorem score_assign (G : Graph n) (u p : Part n) (a t : Fin n) (r : ℝ) :
    G.score r (Graph.assign u p (u a) t) =
      (G.offset u p (u a)).v r + 2 * (G.localLine u p (u a) t).v r := by
  unfold Graph.score
  rw [G.full_eq_local]
  simp only [Graph.shift, Form.v, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  ring

theorem cross_zero (u p : Part n) (a t : Fin n) (h : t ∉ remaining u p a)
    (weights : Fin n → Fin n → ℕ) : Graph.cross u p (u a) t weights = 0 := by
  unfold Graph.cross
  apply sum_eq_zero
  intro x _
  apply sum_eq_zero
  intro y _
  have hy : ¬ (u y ≠ u a ∧ p y = t) := by
    intro hy
    exact h (mem_image.mpr ⟨y, mem_filter.mpr ⟨mem_univ _, hy.1⟩, hy.2⟩)
  simp [Graph.term, hy]

theorem target_occupied (G : Graph n) (u p : Part n) (a t : Fin n)
    (h : t ∈ targets G u p a) : t ∈ remaining u p a := by
  by_contra not_occupied
  have hz := cross_zero u p a t not_occupied G.weight
  simp [targets, hz] at h

theorem local_empty (G : Graph n) (u p : Part n) (a e : Fin n) (r : ℝ)
    (he : e ∉ remaining u p a) : (G.localLine u p (u a) e).v r = 0 := by
  have hz := cross_zero u p a e he G.weight
  have hvol : G.volT u p (u a) e = 0 := by
    unfold Graph.volT
    apply sum_eq_zero
    intro y _
    have hy : ¬ (u y ≠ u a ∧ p y = e) := by
      intro hy
      exact he (mem_image.mpr ⟨y, mem_filter.mpr ⟨mem_univ _, hy.1⟩, hy.2⟩)
    simp [hy]
  simp [Graph.localLine, Form.v, hz, hvol]

theorem local_nonadjacent (G : Graph n) (u p : Part n) (a t : Fin n) (r : ℝ)
    (hr : 0 ≤ r) (ht : t ∉ targets G u p a) : (G.localLine u p (u a) t).v r ≤ 0 := by
  have hz : Graph.cross u p (u a) t G.weight = 0 := by
    by_contra hz
    exact ht (by simp [targets, Nat.pos_of_ne_zero hz])
  simp only [Graph.localLine, Form.v, hz, Nat.cast_zero, mul_zero, Rat.cast_zero, zero_sub]
  have hnonneg : 0 ≤ ((G.volU u (u a) : ℚ) * G.volT u p (u a) t : ℚ) := by positivity
  exact neg_nonpos.mpr (mul_nonneg hr (by exact_mod_cast hnonneg))

def labelSum (p : Part n) : ℕ := ∑ x, (p x).val

theorem labelSum_le (p : Part n) : labelSum p ≤ n * n := by
  calc
    _ ≤ ∑ _x : Fin n, n := by
      exact sum_le_sum (fun x _ => Nat.le_of_lt (p x).isLt)
    _ = _ := by simp

theorem labelSum_drops (u p : Part n) (a t : Fin n) (hp : Graph.respects u p)
    (ht : t < p a) : labelSum (Graph.assign u p (u a) t) < labelSum p := by
  unfold labelSum
  apply sum_lt_sum
  · intro x _
    by_cases hx : u x = u a
    · simpa [Graph.assign, hx, hp x a hx] using (le_of_lt ht : t.val ≤ (p a).val)
    · simp [Graph.assign, hx]
  · exact ⟨a, mem_univ _, by simpa [Graph.assign] using ht⟩

def width (n : ℕ) : ℕ := (n + 1) * (n * n + 1)

def secondary (p : Part n) : ℕ := (n - Graph.count p) * (n * n + 1) + labelSum p

theorem secondary_lt (p : Part n) : secondary p < width n := by
  have h := Nat.mul_le_mul_right (n * n + 1) (Nat.sub_le n (Graph.count p))
  have hsum := labelSum_le p
  unfold secondary width
  rw [Nat.add_mul, one_mul]
  omega

theorem secondary_drops_count {p q : Part n} (h : Graph.count p < Graph.count q) :
    secondary q < secondary p := by
  have hq : Graph.count q ≤ n := by simpa [Graph.count] using (card_image_le (s := (univ : Finset (Fin n))) (f := q))
  have hmul := Nat.mul_le_mul_right (n * n + 1)
    (show n - Graph.count q + 1 ≤ n - Graph.count p by omega)
  rw [Nat.add_mul, one_mul] at hmul
  have hsum := labelSum_le q
  unfold secondary
  omega

theorem secondary_drops_label {p q : Part n} (hc : Graph.count p = Graph.count q)
    (hl : labelSum q < labelSum p) : secondary q < secondary p := by
  unfold secondary
  rw [hc]
  omega

noncomputable def rank (G : Graph n) (r : ℝ) (p : Part n) : ℕ :=
  G.rank r p * width n + secondary p

theorem rank_lt (G : Graph n) (r : ℝ) (p : Part n) :
    rank G r p < (G.budget + 1) * width n := by
  have h : G.rank r p ≤ G.budget := by
    rw [G.budget_eq]
    exact (card_filter_le _ _).trans_eq card_univ
  have hm := Nat.mul_le_mul_right (width n) h
  have hs := secondary_lt p
  unfold rank
  rw [Nat.add_mul, one_mul]
  omega

theorem rank_drops_score (G : Graph n) (r : ℝ) {p q : Part n}
    (hq : G.score r p < G.score r q) : rank G r q < rank G r p := by
  have h := G.rank_drops hq
  have hm := Nat.mul_le_mul_right (width n) (show G.rank r q + 1 ≤ G.rank r p by omega)
  rw [Nat.add_mul, one_mul] at hm
  have hs := secondary_lt q
  unfold rank
  omega

theorem rank_drops_secondary (G : Graph n) (r : ℝ) {p q : Part n}
    (hq : G.score r q = G.score r p) (hs : secondary q < secondary p) :
    rank G r q < rank G r p := by
  unfold rank
  have h : G.rank r q = G.rank r p := by simp [Graph.rank, hq]
  rw [h]
  omega

theorem visit_respects (G : Graph n) (u p : Part n) (a e : Fin n)
    (hp : Graph.respects u p) (choose : Menu G.Code → ℕ) :
    Graph.respects u ((visit G u p a e).run choose) := by
  intro x y hxy
  simp only [visit, Plan.run, Graph.assign, hxy, hp x y hxy]

/-- The LIFO stack supplies a free label and reuses the source if removal newly frees it.
With these two invariants, every changed Seurat move strictly decreases the bounded rank. -/
theorem visit_drops (G : Graph n) (u p : Part n) (a e : Fin n) (r : ℝ)
    (hr : 0 ≤ r) (hp : Graph.respects u p) (he : e ∉ remaining u p a)
    (hlifo : p a ∉ remaining u p a → e = p a) :
    let q := (visit G u p a e).run (G.atReal r)
    q = p ∨ rank G r q < rank G r p := by
  classical
  let m := menu G u p a e
  let w := point G.form m r
  let t := labelAt e w
  let q := Graph.assign u p (u a) t
  change q = p ∨ rank G r q < rank G r p
  have hw : w ∈ maxima G.form m r := min'_mem _ _
  have hwopt := (mem_filter.mp hw).1
  have hmax := (mem_filter.mp hw).2
  have hzero : 0 ∈ m.options := by simp [m, menu]
  have hlocal (j : ℕ) (hj : j ∈ m.options) :
      (G.localLine u p (u a) (labelAt e j)).v r ≤ (G.localLine u p (u a) t).v r := by
    have h := hmax j hj
    change G.score r (Graph.assign u p (u a) (labelAt e j)) ≤ G.score r q at h
    rw [score_assign] at h
    dsimp [q] at h
    rw [score_assign] at h
    linarith
  have hnonneg : 0 ≤ (G.localLine u p (u a) t).v r := by
    simpa [local_empty G u p a e r he] using hlocal 0 hzero
  have hsource : (G.localLine u p (u a) (p a)).v r ≤ (G.localLine u p (u a) t).v r := by
    by_cases hs : p a ∈ targets G u p a
    · have hopt : (p a).val + 1 ∈ m.options := by
        exact mem_insert_of_mem (mem_image_of_mem _ hs)
      simpa only [labelAt_succ] using hlocal ((p a).val + 1) hopt
    · exact (local_nonadjacent G u p a (p a) r hr hs).trans hnonneg
  have hqual : G.score r p ≤ G.score r q := by
    rw [← assign_source u p a hp, score_assign]
    have hq := score_assign G u p a t r
    change G.score r q = _ at hq
    rw [hq]
    linarith
  rcases hqual.eq_or_lt with htie | himprove
  · by_cases hwzero : w = 0
    · have hte : t = e := by simp [t, hwzero]
      by_cases hs : p a ∈ remaining u p a
      · right
        apply rank_drops_secondary G r htie.symm
        apply secondary_drops_count
        unfold Graph.count
        have hprior := occupied_after u p a (p a)
        rw [assign_source u p a hp, insert_eq_of_mem hs] at hprior
        rw [hprior]
        change _ < (univ.image (Graph.assign u p (u a) t)).card
        rw [occupied_after, hte, card_insert_of_not_mem he]
        omega
      · left
        dsimp [q]
        rw [hte, hlifo hs, assign_source u p a hp]
    · have htmem : ∃ c ∈ targets G u p a, c.val + 1 = w := by
        exact mem_image.mp ((mem_insert.mp hwopt).resolve_left hwzero)
      obtain ⟨c, hc, hcw⟩ := htmem
      have htc : t = c := by simp [t, ← hcw]
      have hpos : 0 < (G.localLine u p (u a) t).v r := by
        by_contra hn
        have hz := le_antisymm (le_of_not_gt hn) hnonneg
        have hsame : (line G.form m 0).v r = (line G.form m w).v r := by
          change G.score r (Graph.assign u p (u a) (labelAt e 0)) = G.score r q
          rw [score_assign, labelAt_zero, local_empty G u p a e r he]
          change _ = G.score r (Graph.assign u p (u a) t)
          rw [score_assign, hz]
        have h0max : 0 ∈ maxima G.form m r := mem_filter.mpr ⟨hzero, fun j hj =>
          (hmax j hj).trans hsame.ge⟩
        exact hwzero (Nat.eq_zero_of_le_zero (min'_le _ _ h0max))
      have heq : (G.localLine u p (u a) (p a)).v r = (G.localLine u p (u a) t).v r := by
        have h1 := score_assign G u p a (p a) r
        rw [assign_source u p a hp, htie] at h1
        have h2 := score_assign G u p a t r
        change G.score r q = _ at h2
        linarith
      have hs : p a ∈ targets G u p a := by
        by_contra hs
        have hn := local_nonadjacent G u p a (p a) r hr hs
        rw [heq] at hn
        linarith
      have hsopt : (p a).val + 1 ∈ m.options := mem_insert_of_mem (mem_image_of_mem _ hs)
      have hsame : (line G.form m ((p a).val + 1)).v r = (line G.form m w).v r := by
        change G.score r (Graph.assign u p (u a) (labelAt e ((p a).val + 1))) = G.score r q
        simpa [assign_source u p a hp] using htie
      have hsmax : (p a).val + 1 ∈ maxima G.form m r := mem_filter.mpr ⟨hsopt,
        fun j hj => (hmax j hj).trans hsame.ge⟩
      have hle : t ≤ p a := by
        have hidx : w ≤ (p a).val + 1 := min'_le _ _ hsmax
        rw [htc]
        rw [← hcw] at hidx
        exact Fin.le_iff_val_le_val.mpr (by omega)
      rcases hle.eq_or_lt with ht | ht
      · left
        exact (congrArg (Graph.assign u p (u a)) ht).trans (assign_source u p a hp)
      · right
        apply rank_drops_secondary G r htie.symm
        apply secondary_drops_label
        · unfold Graph.count
          have hprior := occupied_after u p a (p a)
          rw [assign_source u p a hp, insert_eq_of_mem (target_occupied G u p a (p a) hs)] at hprior
          rw [hprior]
          change _ = (univ.image (Graph.assign u p (u a) t)).card
          rw [occupied_after, htc, insert_eq_of_mem (target_occupied G u p a c hc)]
        · exact labelSum_drops u p a t hp ht
  · exact Or.inr (rank_drops_score G r himprove)

/-- A stack's order is operational state, while validity checks its content. -/
structure ValidStack (m : ℕ) (occupied : Finset (Fin n)) (free : List (Fin n)) : Prop where
  occupied_lt : ∀ t ∈ occupied, t.val < m
  nodup : free.Nodup
  mem_iff : ∀ t, t ∈ free ↔ t.val < m ∧ t ∉ occupied

def initialStack (m : ℕ) (p : Part n) : List (Fin n) :=
  ((List.finRange n).filter (fun t => t.val < m ∧ t ∉ univ.image p)).reverse

theorem initialStack_valid (m : ℕ) (p : Part n) (hp : ∀ x, (p x).val < m) :
    ValidStack m (univ.image p) (initialStack m p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, _, rfl⟩ := mem_image.mp ht
    exact hp x
  · exact List.nodup_reverse.mpr ((List.nodup_finRange n).filter _)
  · intro t
    simp [initialStack]

/-- Remove the unit and push its old label exactly when the label becomes empty. -/
def removeSource (u p : Part n) (a : Fin n) (free : List (Fin n)) : List (Fin n) :=
  if p a ∈ remaining u p a then free else p a :: free

theorem removeSource_valid (m : ℕ) (u p : Part n) (a : Fin n) (free : List (Fin n))
    (hrespect : Graph.respects u p) (hvalid : ValidStack m (univ.image p) free) :
    ValidStack m (remaining u p a) (removeSource u p a free) := by
  have hset := occupied_after u p a (p a)
  rw [assign_source u p a hrespect] at hset
  by_cases hs : p a ∈ remaining u p a
  · simpa [hset, removeSource, hs, insert_eq_of_mem hs] using hvalid
  · have hown : p a ∈ univ.image p := mem_image_of_mem _ (mem_univ _)
    have hfree : p a ∉ free := fun h => ((hvalid.mem_iff _).mp h).2 hown
    rw [removeSource, if_neg hs]
    refine ⟨?_, List.nodup_cons.mpr ⟨hfree, hvalid.nodup⟩, ?_⟩
    · intro t ht
      exact hvalid.occupied_lt t (hset ▸ mem_insert_of_mem ht)
    · intro t
      by_cases ht : t = p a
      · subst t
        simp [hs, hvalid.occupied_lt _ hown]
      · have hne : p a ≠ t := Ne.symm ht
        simp [List.mem_cons, ht, hne, hvalid.mem_iff t, hset]

/-- Removing a represented focal unit leaves fewer occupied labels than units. -/
theorem remaining_card_lt (u p : Part n) (a : Fin n) (hp : Graph.respects u p) :
    (remaining u p a).card < Graph.count u := by
  classical
  let unitLabels := (univ : Finset (Fin n)).image u
  let representative (label : Fin n) : Fin n :=
    if h : ∃ x, u x = label then h.choose else a
  have repr_eq (x : Fin n) : u (representative (u x)) = u x := by
    unfold representative
    split
    · rename_i h
      exact h.choose_spec
    · rename_i h
      exact (h ⟨x, rfl⟩).elim
  have hmap : remaining u p a = (unitLabels.erase (u a)).image (p ∘ representative) := by
    ext t
    simp only [remaining, mem_image, mem_filter, mem_univ, true_and, mem_erase,
      unitLabels, Function.comp_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨u x, ⟨hx, x, rfl⟩, hp _ _ (repr_eq x)⟩
    · rintro ⟨_, ⟨hx, x, rfl⟩, ht⟩
      exact ⟨x, hx, (hp _ _ (repr_eq x)).symm.trans ht⟩
  rw [hmap]
  refine card_image_le.trans_lt ?_
  exact card_lt_card (erase_ssubset (mem_image_of_mem _ (mem_univ _)))

theorem slots_card (m : ℕ) (hm : m ≤ n) :
    ((univ : Finset (Fin n)).filter fun t => t.val < m).card = m := by
  let inj : Fin m ↪ Fin n :=
    ⟨Fin.castLE hm, fun a b hab => Fin.ext (congrArg (fun t : Fin n => t.val) hab)⟩
  have hs : ((univ : Finset (Fin n)).filter fun t => t.val < m) = (univ : Finset (Fin m)).map inj := by
    ext t
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro ht
      exact mem_map.mpr ⟨⟨t.val, ht⟩, mem_univ _, Fin.ext rfl⟩
    · intro ha
      obtain ⟨a, _, rfl⟩ := mem_map.mp ha
      exact a.isLt
  simp [hs]

theorem removeSource_has_head (u p : Part n) (a : Fin n) (free : List (Fin n))
    (hrespect : Graph.respects u p)
    (hvalid : ValidStack (Graph.count u) (univ.image p) free) :
    ∃ e tail, removeSource u p a free = e :: tail := by
  have hrest := removeSource_valid _ u p a free hrespect hvalid
  have hm : Graph.count u ≤ n := by
    simpa [Graph.count] using (card_image_le (s := (univ : Finset (Fin n))) (f := u))
  have hc : (remaining u p a).card <
      ((univ : Finset (Fin n)).filter fun t => t.val < Graph.count u).card := by
    rw [slots_card _ hm]
    exact remaining_card_lt u p a hrespect
  obtain ⟨e, he, hnot⟩ := exists_mem_not_mem_of_card_lt_card hc
  have heIn := (hrest.mem_iff e).mpr ⟨(mem_filter.mp he).2, hnot⟩
  cases heq : removeSource u p a free with
  | nil => simp [heq] at heIn
  | cons head tail => exact ⟨head, tail, rfl⟩

theorem removeSource_head (m : ℕ) (u p : Part n) (a e : Fin n) (free tail : List (Fin n))
    (hrespect : Graph.respects u p) (hvalid : ValidStack m (univ.image p) free)
    (hhead : removeSource u p a free = e :: tail) :
    e ∉ remaining u p a ∧ (p a ∉ remaining u p a → e = p a) := by
  have hrest := removeSource_valid m u p a free hrespect hvalid
  rw [hhead] at hrest
  refine ⟨((hrest.mem_iff e).mp (by simp)).2, ?_⟩
  intro hnot
  have hcons : p a :: free = e :: tail := by simpa [removeSource, hnot] using hhead
  exact (List.cons.inj hcons).1.symm

theorem chosen_is_free_or_occupied (G : Graph n) (u p : Part n) (a e : Fin n)
    (r : ℝ) :
    let j := point G.form (menu G u p a e) r
    labelAt e j = e ∨ labelAt e j ∈ remaining u p a := by
  let menuNow := menu G u p a e
  let j := point G.form menuNow r
  change labelAt e j = e ∨ labelAt e j ∈ remaining u p a
  have hj : j ∈ maxima G.form menuNow r := min'_mem _ _
  rcases mem_insert.mp (mem_filter.mp hj).1 with jzero | jpositive
  · left
    simp [jzero]
  · right
    obtain ⟨c, hc, hjc⟩ := mem_image.mp jpositive
    simpa [← hjc] using target_occupied G u p a c hc

/-- Consume the top free label if selected. Occupied targets leave the stack intact. -/
theorem restoreStack_valid (m : ℕ) (occupied : Finset (Fin n)) (e t : Fin n)
    (tail : List (Fin n)) (hvalid : ValidStack m occupied (e :: tail))
    (ht : t = e ∨ t ∈ occupied) :
    ValidStack m (insert t occupied) (if t = e then tail else e :: tail) := by
  rcases ht with ht | ht
  · subst t
    rw [if_pos rfl]
    have he := (hvalid.mem_iff e).mp (by simp)
    have hn := List.nodup_cons.mp hvalid.nodup
    refine ⟨?_, hn.2, ?_⟩
    · intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact he.1
      · exact hvalid.occupied_lt t ht
    · intro t
      by_cases heq : t = e
      · subst t
        simp [hn.1]
      · simpa [List.mem_cons, heq, Ne.symm heq] using hvalid.mem_iff t
  · have he := (hvalid.mem_iff e).mp (by simp)
    have hne : t ≠ e := fun h => he.2 (h ▸ ht)
    simpa [hne, insert_eq_of_mem ht] using hvalid

theorem visit_stack_valid (G : Graph n) (m : ℕ) (u p : Part n) (a e : Fin n) (r : ℝ)
    (tail : List (Fin n)) (hvalid : ValidStack m (remaining u p a) (e :: tail)) :
    let q := (visit G u p a e).run (G.atReal r)
    ValidStack m (univ.image q) (if q a = e then tail else e :: tail) := by
  let t := labelAt e (point G.form (menu G u p a e) r)
  let q := Graph.assign u p (u a) t
  change ValidStack m (univ.image q) (if q a = e then tail else e :: tail)
  have hlabel : q a = t := by simp [q, Graph.assign]
  rw [hlabel]
  dsimp only [q]
  rw [occupied_after]
  exact restoreStack_valid m (remaining u p a) e t tail hvalid
    (chosen_is_free_or_occupied G u p a e r)

end Louvain.SeuratExact
