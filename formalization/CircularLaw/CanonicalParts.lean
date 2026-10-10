import CircularLaw.GreedySpread
import CircularLaw.Discretization
import CircularLaw.RegularBlock

/-!
# Spread and regular parts of the actual level construction

These are the source's unions of selected levels. Both inherit the
size-height bounds; spread values are separated; regular values retain
the lattice separation. An explicit fiber equivalence gives the
factor-four level balance for uniform samples of a constructed part.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CircularLaw

def spreadValueSet {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ) : Finset ℂ := by
  letI := complexLexOrder
  exact spreadSelection δ (representedValues y j)

def regularValueSet {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ) : Finset ℂ :=
  representedValues y j \ spreadValueSet y j δ

def spreadPart {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ) : Finset (Fin n) :=
  levelPart y j (spreadValueSet y j δ)

def regularPart {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ) : Finset (Fin n) :=
  levelPart y j (regularValueSet y j δ)

theorem spreadValueSet_subset {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ) :
    spreadValueSet y j δ ⊆ representedValues y j := by
  letI := complexLexOrder
  exact spreadSelection_subset δ _

theorem regularValueSet_subset {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ) :
    regularValueSet y j δ ⊆ representedValues y j := Finset.sdiff_subset

theorem source_parts_size_height {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ) :
    (2 ^ (j - 1) * (spreadValueSet y j δ).card ≤ (spreadPart y j δ).card ∧
      (spreadPart y j δ).card ≤ 2 ^ (j + 1) * (spreadValueSet y j δ).card) ∧
    (2 ^ (j - 1) * (regularValueSet y j δ).card ≤ (regularPart y j δ).card ∧
      (regularPart y j δ).card ≤ 2 ^ (j + 1) * (regularValueSet y j δ).card) :=
  ⟨levelPart_size_height y j _ (spreadValueSet_subset y j δ),
    levelPart_size_height y j _ (regularValueSet_subset y j δ)⟩

theorem spreadPart_values_separated {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ)
    {i l : Fin n} (hi : i ∈ spreadPart y j δ) (hl : l ∈ spreadPart y j δ) (hil : y i ≠ y l) :
    δ ≤ dist (y i) (y l) := by
  letI := complexLexOrder
  obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨b, hb, hlb⟩ := Finset.mem_biUnion.mp hl
  have hyi := selectedLevelAt_value y j a hia
  have hyl := selectedLevelAt_value y j b hlb
  rw [hyi, hyl] at hil ⊢
  exact spreadSelection_separated δ _ ha hb hil

theorem spreadPart_height_ge_two {n : ℕ} (y : Fin n → ℂ) (j : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hPart : (spreadPart y j δ).Nonempty) :
    2 ≤ (spreadValueSet y j δ).card := by
  letI := complexLexOrder
  have hValues := (levelPart_nonempty_iff y j _ (spreadValueSet_subset y j δ)).mp hPart
  have hPair : (pairCapable δ (representedValues y j)).Nonempty := by
    by_contra hNo
    have hEmpty : spreadValueSet y j δ = ∅ := by
      simp only [spreadValueSet, spreadSelection, dif_neg hNo]
    rw [hEmpty] at hValues
    exact Finset.not_nonempty_empty hValues
  exact spreadSelection_card_lower hδ _ hPair

theorem source_regular_value_geometry {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ) :
    ((spreadValueSet y j δ = ∅) → ∀ a ∈ regularValueSet y j δ,
      ∀ b ∈ regularValueSet y j δ, dist a b < δ) ∧
    ((spreadValueSet y j δ).Nonempty → ∀ a ∈ regularValueSet y j δ,
      ∃ b ∈ spreadValueSet y j δ, dist a b < δ) := by
  letI := complexLexOrder
  constructor
  · intro hEmpty a ha b hb
    have hPair := (spreadSelection_empty_iff δ (representedValues y j)).mp hEmpty
    exact (pairCapable_empty_iff δ _).mp hPair a (regularValueSet_subset y j δ ha)
      b (regularValueSet_subset y j δ hb)
  · intro hNonempty a ha
    have hPair : (pairCapable δ (representedValues y j)).Nonempty := by
      by_contra h
      have hEmpty : spreadValueSet y j δ = ∅ := by
        simp only [spreadValueSet, spreadSelection, dif_neg h]
      rw [hEmpty] at hNonempty
      exact Finset.not_nonempty_empty hNonempty
    exact spreadSelection_covers δ _ hPair a (Finset.mem_sdiff.mp ha).1
      (Finset.mem_sdiff.mp ha).2

theorem levelPart_value_mem {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (A : Finset ℂ)
    {i : Fin n} (hi : i ∈ levelPart y j A) : y i ∈ A := by
  obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp hi
  rw [selectedLevelAt_value y j z hiz]
  exact hz

def partLevel {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (A : Finset ℂ) :
    {i : Fin n // i ∈ levelPart y j A} → {z : ℂ // z ∈ A} :=
  fun i => ⟨y i.val, levelPart_value_mem y j A i.property⟩

def partLevelFiberEquiv {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (A : Finset ℂ) (z : {z : ℂ // z ∈ A}) :
    {i : {i : Fin n // i ∈ levelPart y j A} // partLevel y j A i = z} ≃
      {i : Fin n // i ∈ selectedLevelAt y j z.val} where
  toFun i := ⟨i.val.val, by
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp i.val.property
    have hEq : w = z.val := (selectedLevelAt_value y j w hiw).symm.trans
      (congrArg Subtype.val i.property)
    rw [hEq] at hiw
    exact hiw⟩
  invFun i := ⟨⟨i.val, Finset.mem_biUnion.mpr ⟨z.val, z.property, i.property⟩⟩,
    Subtype.ext (selectedLevelAt_value y j z.val i.property)⟩
  left_inv i := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

theorem partLevel_fiber_card {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (A : Finset ℂ)
    (z : {z : ℂ // z ∈ A}) :
    Nat.card {i : {i : Fin n // i ∈ levelPart y j A} // partLevel y j A i = z} =
      (selectedLevelAt y j z.val).card := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_congr (partLevelFiberEquiv y j A z)

theorem partLevel_balanced {n : ℕ} (y : Fin n → ℂ) (j : ℕ)
    (A : Finset ℂ) (hA : A ⊆ representedValues y j) :
    ∀ a b : {z : ℂ // z ∈ A},
      Nat.card {i : {i : Fin n // i ∈ levelPart y j A} // partLevel y j A i = a} ≤
        4 * Nat.card {i : {i : Fin n // i ∈ levelPart y j A} // partLevel y j A i = b} := by
  intro a b
  rw [partLevel_fiber_card, partLevel_fiber_card]
  exact selectedLevels_factor_four _ _ j
    ((selectedLevelAt_nonempty_mem y j a.val).mpr (hA a.property))
    ((selectedLevelAt_nonempty_mem y j b.val).mpr (hA b.property))

/-- The regular branch for the actual canonical part. Lattice geometry
and balanced fibers are derived, rather than assumed concentration inputs. -/
theorem canonical_regular_part_small_ball {n k m d : ℕ} (hk : 0 < k)
    (hm : 1 ≤ m) (hmd : m ≤ d) (y : Fin n → ℂ) (hy : IsKVector k y) (j : ℕ)
    {τ : ℝ} (hτ : 1 ≤ τ) (hPart : (regularPart y j ((d : ℝ) / (k : ℝ))).Nonempty) (z : ℂ) :
    uniformProbability (fun x : Fin m → {i : Fin n // i ∈ regularPart y j ((d : ℝ) / (k : ℝ))} =>
      ‖(∑ a, y (x a).val) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) ≤
      40000 * τ ^ 2 * (((regularValueSet y j ((d : ℝ) / (k : ℝ))).card : ℝ) *
        ((m : ℝ) / (d : ℝ)))⁻¹ := by
  let A := regularValueSet y j ((d : ℝ) / (k : ℝ))
  let α := {i : Fin n // i ∈ levelPart y j A}
  let β := {z : ℂ // z ∈ A}
  haveI : Nonempty α := hPart.to_subtype
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSingletonClass α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hValues (a : β) : a.val ∈ Set.range y := by
    have hRep := regularValueSet_subset y j ((d : ℝ) / (k : ℝ)) a.property
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hRep).1
    exact ⟨i, hi⟩
  have hSep : ∀ a b : β, a ≠ b → 1 / (k : ℝ) ≤ dist a.val b.val := by
    intro a b hab
    exact kVector_values_separated hk hy (hValues a) (hValues b)
      (fun h => hab (Subtype.ext h))
  have h := regular_balanced_block_small_ball (partLevel y j A) (fun a : β => a.val) hm hmd
    hτ (by exact_mod_cast hk : (0 : ℝ) < k) hSep
    (partLevel_balanced y j A (regularValueSet_subset y j ((d : ℝ) / (k : ℝ)))) z
  simpa only [Fintype.card_coe, partLevel] using h

end CircularLaw
