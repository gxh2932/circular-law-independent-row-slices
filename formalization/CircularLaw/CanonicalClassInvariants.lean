import CircularLaw.CoordinateMultiset
import CircularLaw.CanonicalBinCompression

/-!
# Canonical part data on a coordinate-multiset class

Part labels retain the spread/regular kind and creation order. The actual
values and sizes of these parts are invariant under coordinate permutation,
so each class member has an assignment to the reference vector's labels
with exactly the prescribed part sizes.
-/

noncomputable section
open Classical

-- Keep the coordinate-label choice abstract while comparing its part data.
attribute [local irreducible] CircularLaw.canonicalCoordinateLabel

namespace CircularLaw

theorem taggedValues_perm {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (σ : Equiv.Perm (Fin n)) (q : Bool × Fin (n + 2)) :
    taggedValues (y ∘ σ) δ q = taggedValues y δ q := by
  unfold taggedValues
  split_ifs
  · exact spreadValueSet_perm y σ q.2.val δ
  · exact regularValueSet_perm y σ q.2.val δ

theorem taggedPart_card_perm {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (σ : Equiv.Perm (Fin n)) (q : Bool × Fin (n + 2)) :
    (taggedPart (y ∘ σ) δ q).card = (taggedPart y δ q).card := by
  unfold taggedPart
  rw [taggedValues_perm]
  exact levelPart_card_perm y σ q.2.val (taggedValues y δ q)

theorem taggedValues_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (δ : ℝ) (q : Bool × Fin (n + 2)) :
    taggedValues z δ q = taggedValues y δ q := by
  obtain ⟨σ, rfl⟩ := (coordinateMultiset_eq_iff_perm y z).mp h
  exact taggedValues_perm y δ σ q

theorem taggedPart_card_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (δ : ℝ) (q : Bool × Fin (n + 2)) :
    (taggedPart z δ q).card = (taggedPart y δ q).card := by
  obtain ⟨σ, rfl⟩ := (coordinateMultiset_eq_iff_perm y z).mp h
  exact taggedPart_card_perm y δ σ q

theorem taggedPart_nonempty_multiset_iff {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (δ : ℝ) (q : Bool × Fin (n + 2)) :
    (taggedPart z δ q).Nonempty ↔ (taggedPart y δ q).Nonempty := by
  rw [← Finset.card_pos, ← Finset.card_pos, taggedPart_card_multiset_eq y z h δ q]

def canonicalClassPart {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (z : CoordinatePermutationClass y) (i : Fin n) : CanonicalLabel y δ :=
  ⟨(canonicalCoordinateLabel z.val δ i).val,
    (taggedPart_nonempty_multiset_iff y z.val z.property δ
      (canonicalCoordinateLabel z.val δ i).val).mp (canonicalCoordinateLabel z.val δ i).property⟩

theorem canonicalClassPart_val {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (z : CoordinatePermutationClass y) (i : Fin n) :
    @Subtype.val (Bool × Fin (n + 2)) (fun q => (taggedPart y δ q).Nonempty)
      (canonicalClassPart y δ z i) =
    @Subtype.val (Bool × Fin (n + 2)) (fun q => (taggedPart z.val δ q).Nonempty)
      (canonicalCoordinateLabel z.val δ i) := by
  unfold canonicalClassPart
  rfl

theorem canonicalClassPart_counts {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (z : CoordinatePermutationClass y) (q : CanonicalLabel y δ) :
    Nat.card {i : Fin n // canonicalClassPart y δ z i = q} =
      assignmentPartSize (canonicalCoordinateLabel y δ) q := by
  let qz : CanonicalLabel z.val δ :=
    ⟨q.val, (taggedPart_nonempty_multiset_iff y z.val z.property δ q.val).mpr q.property⟩
  let eFiber : {i : Fin n // canonicalClassPart y δ z i = q} ≃
      {i : Fin n // canonicalCoordinateLabel z.val δ i = qz} :=
    Equiv.subtypeEquivRight (fun i => by
      constructor
      · intro hi
        apply Subtype.ext
        have hValues :
            @Subtype.val (Bool × Fin (n + 2)) (fun q => (taggedPart y δ q).Nonempty)
              (canonicalClassPart y δ z i) =
            @Subtype.val (Bool × Fin (n + 2)) (fun q => (taggedPart y δ q).Nonempty) q :=
          congrArg (@Subtype.val (Bool × Fin (n + 2))
            (fun q => (taggedPart y δ q).Nonempty)) hi
        rw [canonicalClassPart_val] at hValues
        exact hValues
      · intro hi
        apply Subtype.ext
        rw [canonicalClassPart_val]
        have hValues :
            @Subtype.val (Bool × Fin (n + 2)) (fun q => (taggedPart z.val δ q).Nonempty)
              (canonicalCoordinateLabel z.val δ i) =
            @Subtype.val (Bool × Fin (n + 2)) (fun q => (taggedPart z.val δ q).Nonempty) qz :=
          congrArg (@Subtype.val (Bool × Fin (n + 2))
            (fun q => (taggedPart z.val δ q).Nonempty)) hi
        exact hValues)
  calc
    _ = Nat.card {i : Fin n // canonicalCoordinateLabel z.val δ i = qz} :=
      Nat.card_congr eFiber
    _ = (taggedPart z.val δ qz.val).card := canonicalPart_card z.val δ qz
    _ = (taggedPart y δ q.val).card := by
      have hVal : qz.val = q.val := rfl
      rw [hVal]
      exact taggedPart_card_multiset_eq y z.val z.property δ q.val
    _ = _ := (canonicalPart_card y δ q).symm

def canonicalClassAssignment {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (z : CoordinatePermutationClass y) : FixedPartAssignments (canonicalCoordinateLabel y δ) :=
  ⟨canonicalClassPart y δ z, canonicalClassPart_counts y δ z⟩

theorem canonicalClass_value_mem {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (z : CoordinatePermutationClass y) (i : Fin n) :
    z.val i ∈ taggedValues y δ (canonicalClassPart y δ z i).val := by
  rw [canonicalClassPart_val]
  rw [← taggedValues_multiset_eq y z.val z.property δ (canonicalCoordinateLabel z.val δ i).val]
  exact levelPart_value_mem z.val _ _ (canonicalCoordinateLabel_mem z.val δ i)

theorem canonical_assignmentPartSize_eq {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (q : CanonicalLabel y δ) :
    assignmentPartSize (canonicalCoordinateLabel y δ) q =
      profilePartSize (canonicalRowProfile y δ) q := rfl

end CircularLaw
