import LocalGain

namespace Louvain.SeuratExact

open Finset

def units {n : ℕ} (u : Part n) : Finset (Fin n) := univ.image u

private def orderedLabels {n : ℕ} (u : Part n) : List (Fin n) :=
  (List.finRange n).filter (fun label => label ∈ units u)

/-- Enumerate one representative per unit, in the order of the unit IDs. -/
def representatives {n : ℕ} (u : Part n) : List (Fin n) :=
  (orderedLabels u).filterMap fun label =>
    let members := univ.filter (fun vertex => u vertex = label)
    if h : members.Nonempty then some (members.min' h) else none

private theorem filterMap_map_of_total {α β : Type} (f : α → Option β) (g : β → α)
    (xs : List α) (total : ∀ a ∈ xs, ∃ b, f a = some b ∧ g b = a) :
    (xs.filterMap f).map g = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨b, hb, hba⟩ := total a (List.mem_cons_self)
    have tail : ∀ t ∈ xs, ∃ y, f t = some y ∧ g y = t :=
      fun t ht => total t (List.mem_cons_of_mem a ht)
    simp [hb, hba, ih tail]

theorem representative_labels {n : ℕ} (u : Part n) :
    (representatives u).map u = orderedLabels u := by
  unfold representatives
  apply filterMap_map_of_total
  intro label inOrder
  have present : label ∈ units u := of_decide_eq_true (List.mem_filter.mp inOrder).2
  obtain ⟨witness, _, hw⟩ := mem_image.mp present
  let members := univ.filter (fun vertex => u vertex = label)
  have nonempty : members.Nonempty := ⟨witness, by simp [members, hw]⟩
  refine ⟨members.min' nonempty, dif_pos nonempty, ?_⟩
  exact (mem_filter.mp (Finset.min'_mem members nonempty)).2

theorem representatives_length_eq {n : ℕ} (u : Part n) :
    (representatives u).length = Graph.count u := by
  have h := congrArg List.length (representative_labels u)
  simp only [List.length_map] at h
  have unique : (orderedLabels u).Nodup := (List.nodup_finRange n).filter _
  have hset : (orderedLabels u).toFinset = units u := by
    ext vertex
    simp [orderedLabels]
  change (representatives u).length = (units u).card
  rw [h, ← hset, List.toFinset_card_of_nodup unique]

theorem representatives_length_le {n : ℕ} (u : Part n) :
    (representatives u).length ≤ n := by
  rw [representatives_length_eq]
  simpa [Graph.count, units] using (Finset.card_le_univ (units u))

theorem exists_representative {n : ℕ} (u : Part n) (vertex : Fin n) :
    ∃ representative ∈ representatives u, u representative = u vertex := by
  apply List.mem_map.mp
  rw [representative_labels]
  simp [orderedLabels, units]

theorem count_le_of_respects {n : ℕ} {u p : Part n} (respects : Graph.respects u p) :
    Graph.count p ≤ Graph.count u := by
  have covered : units p ⊆ (representatives u).toFinset.image p := by
    intro label inUse
    obtain ⟨vertex, _, hv⟩ := mem_image.mp inUse
    obtain ⟨representative, inOrder, sameUnit⟩ := exists_representative u vertex
    exact mem_image.mpr ⟨representative, List.mem_toFinset.mpr inOrder,
      (respects _ _ sameUnit).trans hv⟩
  calc
    Graph.count p = (units p).card := rfl
    _ ≤ ((representatives u).toFinset.image p).card := card_le_card covered
    _ ≤ (representatives u).toFinset.card := card_image_le
    _ ≤ (representatives u).length := List.toFinset_card_le _
    _ = Graph.count u := representatives_length_eq u

/-- Removing a unit leaves fewer occupied cluster labels than available
unit slots, even if the removed unit's old cluster remains occupied. -/
theorem remaining_card_lt_count {n : ℕ} {u p : Part n} (a : Fin n)
    (respects : Graph.respects u p) :
    ((univ.filter fun x => u x ≠ u a).image p).card < Graph.count u := by
  let others := (representatives u).toFinset.filter (fun v => u v ≠ u a)
  have covered : (univ.filter fun x => u x ≠ u a).image p ⊆ others.image p := by
    intro label inUse
    obtain ⟨vertex, outside, hv⟩ := mem_image.mp inUse
    obtain ⟨representative, inOrder, sameUnit⟩ := exists_representative u vertex
    refine mem_image.mpr ⟨representative, mem_filter.mpr ⟨List.mem_toFinset.mpr inOrder, ?_⟩,
      (respects _ _ sameUnit).trans hv⟩
    rw [sameUnit]
    exact (mem_filter.mp outside).2
  have strict : others ⊂ (representatives u).toFinset := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro same
    obtain ⟨representative, inOrder, sameUnit⟩ := exists_representative u a
    have present : representative ∈ (representatives u).toFinset := List.mem_toFinset.mpr inOrder
    rw [← same] at present
    exact (mem_filter.mp present).2 sameUnit
  calc
    ((univ.filter fun x => u x ≠ u a).image p).card ≤ (others.image p).card := card_le_card covered
    _ ≤ others.card := card_image_le
    _ < (representatives u).toFinset.card := card_lt_card strict
    _ ≤ (representatives u).length := List.toFinset_card_le _
    _ = Graph.count u := representatives_length_eq u

private theorem smallerLabels_lt_card {n : ℕ} (p : Part n) {label : Fin n}
    (occupied : label ∈ units p) : ((units p).filter (· < label)).card < (units p).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  have cycle := occupied
  rw [← he] at cycle
  exact (lt_irrefl label) (Finset.mem_filter.mp cycle).2

private def compactLabel {n : ℕ} (p : Part n) (label : Fin n) (occupied : label ∈ units p) : Fin n :=
  ⟨((units p).filter (· < label)).card, by
    have bound : (units p).card ≤ n := by
      simpa using (Finset.card_le_univ (units p))
    exact (smallerLabels_lt_card p occupied).trans_le bound⟩

/-- Seurat compacts occupied community IDs in increasing order of their old IDs. -/
def compact {n : ℕ} (p : Part n) : Part n := fun v =>
  compactLabel p (p v) (by simp [units])

private theorem compactLabel_strict {n : ℕ} (p : Part n) {a b : Fin n}
    (ha : a ∈ units p) (hb : b ∈ units p) (ordered : a < b) :
    compactLabel p a ha < compactLabel p b hb := by
  change ((units p).filter (· < a)).card < ((units p).filter (· < b)).card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨member, less⟩ := Finset.mem_filter.mp hz
    exact mem_filter.mpr ⟨member, less.trans ordered⟩
  · intro equal
    have included : a ∈ (units p).filter (· < b) := mem_filter.mpr ⟨ha, ordered⟩
    rw [← equal] at included
    exact (lt_irrefl a) (mem_filter.mp included).2

private theorem compactLabel_injective {n : ℕ} (p : Part n) {a b : Fin n}
    (ha : a ∈ units p) (hb : b ∈ units p)
    (equal : compactLabel p a ha = compactLabel p b hb) : a = b := by
  rcases lt_trichotomy a b with less | same | greater
  · exact (ne_of_lt (compactLabel_strict p ha hb less) equal).elim
  · exact same
  · exact (ne_of_lt (compactLabel_strict p hb ha greater) equal.symm).elim

theorem compact_same {n : ℕ} (p : Part n) (a b : Fin n) :
    compact p a = compact p b ↔ p a = p b := by
  constructor
  · exact compactLabel_injective p _ _
  · intro same
    simp only [compact, same]

theorem compact_count {n : ℕ} (p : Part n) : Graph.count (compact p) = Graph.count p := by
  change (units (compact p)).card = (units p).card
  symm
  apply Finset.card_bij (compactLabel p)
  · intro label h
    obtain ⟨v, _, hv⟩ := mem_image.mp h
    subst label
    exact mem_image.mpr ⟨v, mem_univ _, rfl⟩
  · intro a ha b hb equal
    exact compactLabel_injective p ha hb equal
  · intro label h
    obtain ⟨v, _, hv⟩ := mem_image.mp h
    exact ⟨p v, by simp [units], hv⟩

theorem compact_label_lt_count {n : ℕ} (p : Part n) (vertex : Fin n) :
    (compact p vertex).val < Graph.count p :=
  smallerLabels_lt_card p (by simp [units])

/-- The live cluster labels after compaction are exactly `0, ..., count p - 1`. -/
theorem units_compact {n : ℕ} (p : Part n) :
    units (compact p) = univ.filter (fun label => label.val < Graph.count p) := by
  have bound : Graph.count p ≤ n := by
    rw [← representatives_length_eq]
    exact representatives_length_le p
  let embedding := Fin.castLEEmb bound
  have initialSegment : (univ : Finset (Fin (Graph.count p))).map embedding =
      (univ : Finset (Fin n)).filter (fun label => label.val < Graph.count p) := by
    ext label
    constructor
    · intro inside
      obtain ⟨source, _, hlabel⟩ := mem_map.mp inside
      subst label
      exact mem_filter.mpr ⟨mem_univ _, source.isLt⟩
    · intro inside
      have hlabel := (mem_filter.mp inside).2
      exact mem_map.mpr ⟨⟨label.val, hlabel⟩, mem_univ _, rfl⟩
  apply Finset.eq_of_subset_of_card_le
  · intro label occupied
    obtain ⟨vertex, _, hv⟩ := mem_image.mp occupied
    exact mem_filter.mpr ⟨mem_univ _, hv ▸ compact_label_lt_count p vertex⟩
  · rw [← initialSegment, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact (compact_count p).ge

theorem compact_respects {n : ℕ} {u p : Part n} (respects : Graph.respects u p) :
    Graph.respects u (compact p) :=
  fun _ _ equal => (compact_same _ _ _).2 (respects _ _ equal)

theorem respect_self {n : ℕ} (u : Part n) : Graph.respects u u := Graph.respects_self u

end Louvain.SeuratExact
