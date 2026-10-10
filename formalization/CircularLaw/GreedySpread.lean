import CircularLaw.LevelPartition
import Mathlib.Data.Prod.Lex

/-!
# The canonical spread-value selection

The source starts from the lexicographically greatest value which has a
separated partner, then takes admissible values in decreasing order. The
finite scan checks separation, maximality, and the required two-value
minimum. Starting from an arbitrary greatest value could produce a
singleton, which is why the separated-partner seed is used explicitly.
-/

noncomputable section

namespace CircularLaw

def complexLexOrder : LinearOrder ℂ :=
  LinearOrder.lift' (fun z : ℂ => toLex (z.re, z.im)) (by
    intro z w h
    have hPair : (z.re, z.im) = (w.re, w.im) := congrArg ofLex h
    exact Complex.ext (congrArg Prod.fst hPair) (congrArg Prod.snd hPair))

def greedyInsert {α : Type*} [PseudoMetricSpace α] (δ : ℝ) (s : Finset α) (x : α) : Finset α := by
  classical
  exact if ∀ y ∈ s, δ ≤ dist x y then insert x s else s

def greedyScan {α : Type*} [PseudoMetricSpace α] (δ : ℝ) (s : Finset α) : List α → Finset α
  | [] => s
  | x :: xs => greedyScan δ (greedyInsert δ s x) xs

theorem greedyInsert_subset {α : Type*} [PseudoMetricSpace α] (δ : ℝ) (s : Finset α) (x : α) :
    s ⊆ greedyInsert δ s x := by
  classical
  unfold greedyInsert
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem greedyInsert_subset_union {α : Type*} [PseudoMetricSpace α] [DecidableEq α]
    (δ : ℝ) (s : Finset α) (x : α) :
    greedyInsert δ s x ⊆ insert x s := by
  classical
  unfold greedyInsert
  split
  · intro y hy
    simpa only [Finset.mem_insert] using hy
  · exact Finset.subset_insert _ _

theorem greedyScan_subset {α : Type*} [PseudoMetricSpace α] (δ : ℝ) (s : Finset α) (xs : List α) :
    s ⊆ greedyScan δ s xs := by
  induction xs generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons x xs ih => exact (greedyInsert_subset δ s x).trans (ih _)

theorem greedyScan_subset_union {α : Type*} [PseudoMetricSpace α] [DecidableEq α]
    (δ : ℝ) (s : Finset α) (xs : List α) :
    greedyScan δ s xs ⊆ s ∪ xs.toFinset := by
  classical
  induction xs generalizing s with
  | nil => simp only [greedyScan, List.toFinset_nil, Finset.union_empty, Finset.Subset.refl]
  | cons x xs ih =>
    intro y hy
    have h := ih (greedyInsert δ s x) hy
    rcases Finset.mem_union.mp h with h | h
    · have h' := greedyInsert_subset_union δ s x h
      rcases Finset.mem_insert.mp h' with h' | h'
      · subst y
        exact Finset.mem_union_right _ (by simp only [List.toFinset_cons, Finset.mem_insert_self])
      · exact Finset.mem_union_left _ h'
    · exact Finset.mem_union_right _ (by rw [List.toFinset_cons]; exact Finset.mem_insert_of_mem h)

theorem greedyInsert_separated {α : Type*} [PseudoMetricSpace α] (δ : ℝ) (s : Finset α) (x : α)
    (hs : (s : Set α).Pairwise (fun a b => δ ≤ dist a b)) :
    (greedyInsert δ s x : Set α).Pairwise (fun a b => δ ≤ dist a b) := by
  classical
  unfold greedyInsert
  split_ifs with h
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with ha | ha
    · rcases Finset.mem_insert.mp hb with hb | hb
      · exact (hab (ha.trans hb.symm)).elim
      · rw [ha]
        exact h b hb
    · rcases Finset.mem_insert.mp hb with hb | hb
      · rw [hb, dist_comm]
        exact h a ha
      · exact hs ha hb hab
  · exact hs

theorem greedyScan_separated {α : Type*} [PseudoMetricSpace α]
    (δ : ℝ) (s : Finset α) (xs : List α)
    (hs : (s : Set α).Pairwise (fun a b => δ ≤ dist a b)) :
    (greedyScan δ s xs : Set α).Pairwise (fun a b => δ ≤ dist a b) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih => exact ih _ (greedyInsert_separated δ s x hs)

theorem greedyScan_covers {α : Type*} [PseudoMetricSpace α]
    (δ : ℝ) (s : Finset α) (xs : List α) :
    ∀ x ∈ xs, x ∉ greedyScan δ s xs → ∃ y ∈ greedyScan δ s xs, dist x y < δ := by
  classical
  induction xs generalizing s with
  | nil => intro x hx; exact (List.not_mem_nil hx).elim
  | cons a xs ih =>
    intro x hx hxOut
    rcases List.mem_cons.mp hx with hx | hx
    · rw [hx] at hxOut ⊢
      by_cases hAdmissible : ∀ y ∈ s, δ ≤ dist a y
      · have hIn : a ∈ greedyInsert δ s a := by
          simp only [greedyInsert, if_pos hAdmissible, Finset.mem_insert_self]
        exact (hxOut (greedyScan_subset δ _ xs hIn)).elim
      · obtain ⟨y, hDist⟩ := not_forall.mp hAdmissible
        obtain ⟨hy, hDist⟩ := Classical.not_imp.mp hDist
        exact ⟨y, greedyScan_subset δ s (a :: xs) hy, lt_of_not_ge hDist⟩
    · exact ih (greedyInsert δ s a) x hx hxOut

def pairCapable {α : Type*} [PseudoMetricSpace α] (δ : ℝ) (Λ : Finset α) : Finset α := by
  classical
  exact Λ.filter (fun x => ∃ y ∈ Λ, δ ≤ dist x y)

def spreadSelection {α : Type*} [PseudoMetricSpace α] [LinearOrder α]
    (δ : ℝ) (Λ : Finset α) : Finset α := by
  classical
  exact if h : (pairCapable δ Λ).Nonempty then
    greedyScan δ {(pairCapable δ Λ).max' h} Λ.sort.reverse else ∅

theorem spreadSelection_subset {α : Type*} [PseudoMetricSpace α] [LinearOrder α]
    (δ : ℝ) (Λ : Finset α) : spreadSelection δ Λ ⊆ Λ := by
  classical
  unfold spreadSelection
  split_ifs with h
  · have hSeed := (Finset.mem_filter.mp (Finset.max'_mem (pairCapable δ Λ) h)).1
    intro x hx
    have h' := greedyScan_subset_union δ {(pairCapable δ Λ).max' h} Λ.sort.reverse hx
    rcases Finset.mem_union.mp h' with h' | h'
    · rw [Finset.mem_singleton.mp h']
      exact hSeed
    · simpa only [List.mem_toFinset, List.mem_reverse, Finset.mem_sort] using h'
  · exact Finset.empty_subset _

theorem spreadSelection_separated {α : Type*} [PseudoMetricSpace α] [LinearOrder α]
    (δ : ℝ) (Λ : Finset α) :
    (spreadSelection δ Λ : Set α).Pairwise (fun a b => δ ≤ dist a b) := by
  classical
  unfold spreadSelection
  split_ifs
  · apply greedyScan_separated
    simpa only [Finset.coe_singleton] using Set.pairwise_singleton _ (fun a b => δ ≤ dist a b)
  · simpa only [Finset.coe_empty] using Set.pairwise_empty (fun a b => δ ≤ dist a b)

theorem spreadSelection_covers {α : Type*} [PseudoMetricSpace α] [LinearOrder α]
    (δ : ℝ) (Λ : Finset α) (h : (pairCapable δ Λ).Nonempty) :
    ∀ x ∈ Λ, x ∉ spreadSelection δ Λ → ∃ y ∈ spreadSelection δ Λ, dist x y < δ := by
  classical
  rw [spreadSelection, dif_pos h]
  intro x hx hxOut
  exact greedyScan_covers δ _ (Λ.sort (· ≤ ·)).reverse x
    (by simpa only [List.mem_reverse, Finset.mem_sort] using hx) hxOut

theorem spreadSelection_card_lower {α : Type*} [PseudoMetricSpace α] [LinearOrder α]
    {δ : ℝ} (hδ : 0 < δ) (Λ : Finset α) (h : (pairCapable δ Λ).Nonempty) :
    2 ≤ (spreadSelection δ Λ).card := by
  classical
  let a := (pairCapable δ Λ).max' h
  have hA : a ∈ spreadSelection δ Λ := by
    rw [spreadSelection, dif_pos h]
    exact greedyScan_subset δ _ _ (Finset.mem_singleton_self a)
  obtain ⟨b, hb, hab⟩ := (Finset.mem_filter.mp (Finset.max'_mem (pairCapable δ Λ) h)).2
  by_cases hB : b ∈ spreadSelection δ Λ
  · have hne : a ≠ b := by intro heq; rw [← heq, dist_self] at hab; linarith
    exact Finset.one_lt_card.mpr ⟨a, hA, b, hB, hne⟩
  · obtain ⟨c, hc, hbc⟩ := spreadSelection_covers δ Λ h b hb hB
    have hne : a ≠ c := by
      intro heq
      rw [← heq, dist_comm] at hbc
      exact (not_lt_of_ge hab) hbc
    exact Finset.one_lt_card.mpr ⟨a, hA, c, hc, hne⟩

theorem pairCapable_empty_iff {α : Type*} [PseudoMetricSpace α]
    (δ : ℝ) (Λ : Finset α) :
    pairCapable δ Λ = ∅ ↔ ∀ a ∈ Λ, ∀ b ∈ Λ, dist a b < δ := by
  classical
  rw [← Finset.not_nonempty_iff_eq_empty]
  constructor
  · intro h a ha b hb
    apply lt_of_not_ge
    intro hDist
    exact h ⟨a, Finset.mem_filter.mpr ⟨ha, b, hb, hDist⟩⟩
  · intro h hPair
    obtain ⟨a, ha⟩ := hPair
    obtain ⟨ha, b, hb, hDist⟩ := Finset.mem_filter.mp ha
    exact (not_le_of_gt (h a ha b hb)) hDist

theorem spreadSelection_empty_iff {α : Type*} [PseudoMetricSpace α] [LinearOrder α]
    (δ : ℝ) (Λ : Finset α) : spreadSelection δ Λ = ∅ ↔ pairCapable δ Λ = ∅ := by
  classical
  constructor
  · intro hEmpty
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro h
    have hSeed : (pairCapable δ Λ).max' h ∈ spreadSelection δ Λ := by
      rw [spreadSelection, dif_pos h]
      exact greedyScan_subset δ _ _ (Finset.mem_singleton_self _)
    rw [hEmpty] at hSeed
    simp only [Finset.notMem_empty] at hSeed
  · intro h
    have hNo : ¬(pairCapable δ Λ).Nonempty := by rw [h]; exact Finset.not_nonempty_empty
    rw [spreadSelection, dif_neg hNo]

end CircularLaw
