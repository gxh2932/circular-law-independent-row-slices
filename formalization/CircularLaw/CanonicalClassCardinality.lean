import CircularLaw.CanonicalClassInvariants
import CircularLaw.PartLevelCounting
import CircularLaw.CoordinateClassRestriction

/-!
# The source LLTTY equivalence-class cardinality bound

Every vector with the reference coordinate multiset is encoded by its
actual canonical assignment and its coordinate values in the corresponding
parts. The encoding is injective. The exact count of these codes gives
`n! / ∏ s_q! * ∏ h_q^s_q`, also for restricted approximation classes.
-/

noncomputable section
open Classical
open scoped BigOperators Nat

namespace CircularLaw

def canonicalClassCode {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (z : CoordinatePermutationClass y) :
    PartLevelAssignments (canonicalCoordinateLabel y δ) (fun q => taggedValues y δ q.val) :=
  ⟨canonicalClassAssignment y δ z, fun i => ⟨z.val i, canonicalClass_value_mem y δ z i⟩⟩

theorem canonicalClassCode_injective {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    Function.Injective (canonicalClassCode y δ) := by
  intro z w h
  apply Subtype.ext
  have hValues := congrArg
    (fun c : PartLevelAssignments (canonicalCoordinateLabel y δ)
        (fun q => taggedValues y δ q.val) => fun i => (c.2 i).val) h
  exact hValues

theorem canonicalClassCode_card_le {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    Nat.card (CoordinatePermutationClass y) ≤ Nat.card
      (PartLevelAssignments (canonicalCoordinateLabel y δ) (fun q => taggedValues y δ q.val)) :=
  Nat.card_le_card_of_injective (canonicalClassCode y δ) (canonicalClassCode_injective y δ)

theorem canonicalClass_cardinality {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    (Nat.card (CoordinatePermutationClass y) : ℝ) ≤
      ((n)! : ℝ) / (∏ q, ((profilePartSize (canonicalRowProfile y δ) q)! : ℝ)) *
        (∏ q, ((canonicalRowProfile y δ).height q : ℝ) ^
          profilePartSize (canonicalRowProfile y δ) q) := by
  have hCount : (Nat.card (CoordinatePermutationClass y) : ℝ) ≤ Nat.card
      (PartLevelAssignments (canonicalCoordinateLabel y δ) (fun q => taggedValues y δ q.val)) := by
    exact_mod_cast canonicalClassCode_card_le y δ
  have h := hCount.trans_eq (partLevelAssignments_card_real
    (canonicalCoordinateLabel y δ) (fun q => taggedValues y δ q.val))
  simpa only [Fintype.card_fin, canonical_assignmentPartSize_eq] using h

theorem canonicalClassIn_cardinality {n : ℕ} (A : Set (Fin n → ℂ))
    (y : Fin n → ℂ) (δ : ℝ) :
    (Nat.card (CoordinateMultisetClassIn A y) : ℝ) ≤
      ((n)! : ℝ) / (∏ q, ((profilePartSize (canonicalRowProfile y δ) q)! : ℝ)) *
        (∏ q, ((canonicalRowProfile y δ).height q : ℝ) ^
          profilePartSize (canonicalRowProfile y δ) q) := by
  have hCount : (Nat.card (CoordinateMultisetClassIn A y) : ℝ) ≤
      Nat.card (CoordinatePermutationClass y) := by
    exact_mod_cast coordinateMultisetClassIn_card_le A y
  exact hCount.trans (canonicalClass_cardinality y δ)

theorem orderedCanonicalClassIn_cardinality {n : ℕ} (A : Set (Fin n → ℂ))
    (y : Fin n → ℂ) (δ : ℝ) :
    (Nat.card (CoordinateMultisetClassIn A y) : ℝ) ≤
      ((n)! : ℝ) / (∏ q, ((profilePartSize (orderedCanonicalRowProfile y δ) q)! : ℝ)) *
        (∏ q, ((orderedCanonicalRowProfile y δ).height q : ℝ) ^
          profilePartSize (orderedCanonicalRowProfile y δ) q) := by
  have hFactorials :
      (∏ q, ((profilePartSize (orderedCanonicalRowProfile y δ) q)! : ℝ)) =
        ∏ q, ((profilePartSize (canonicalRowProfile y δ) q)! : ℝ) := by
    simp only [orderedCanonical_profilePartSize_eq]
    exact (canonicalEnumeration y δ).prod_comp (fun q =>
      ((profilePartSize (canonicalRowProfile y δ) q)! : ℝ))
  have hHeights :
      (∏ q, ((orderedCanonicalRowProfile y δ).height q : ℝ) ^
        profilePartSize (orderedCanonicalRowProfile y δ) q) =
      ∏ q, ((canonicalRowProfile y δ).height q : ℝ) ^
        profilePartSize (canonicalRowProfile y δ) q := by
    simp only [orderedCanonical_profilePartSize_eq]
    exact (canonicalEnumeration y δ).prod_comp (fun q =>
      ((canonicalRowProfile y δ).height q : ℝ) ^ profilePartSize (canonicalRowProfile y δ) q)
  rw [hFactorials, hHeights]
  exact canonicalClassIn_cardinality A y δ

def canonicalApproxFamily {n : ℕ} (k : ℕ) (X : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  (fun x : Fin n → ℂ => fun i => canonicalApprox k (x i)) '' X

theorem canonicalApproxFamily_isKVector {n : ℕ} (k : ℕ) (X : Set (Fin n → ℂ))
    {y : Fin n → ℂ} (hy : y ∈ canonicalApproxFamily k X) : IsKVector k y := by
  obtain ⟨x, _, rfl⟩ := hy
  exact canonicalApprox_isKVector k x

theorem canonicalApproxFamily_mono {n : ℕ} (k : ℕ) {X Y : Set (Fin n → ℂ)}
    (h : X ⊆ Y) : canonicalApproxFamily k X ⊆ canonicalApproxFamily k Y :=
  Set.image_mono h

theorem canonicalApproxClasses_card_le {n : ℕ} (k : ℕ)
    {X Y : Set (Fin n → ℂ)} (h : X ⊆ Y)
    (hY : (coordinateMultisetClasses (canonicalApproxFamily k Y)).Finite) :
    Nat.card {m : Multiset ℂ // m ∈ coordinateMultisetClasses (canonicalApproxFamily k X)} ≤
      Nat.card {m : Multiset ℂ // m ∈ coordinateMultisetClasses (canonicalApproxFamily k Y)} :=
  coordinateMultisetClasses_card_le (canonicalApproxFamily_mono k h) hY

theorem canonicalApprox_class_cardinality {n : ℕ} (k : ℕ) (X : Set (Fin n → ℂ))
    (y : Fin n → ℂ) (δ : ℝ) :
    (Nat.card (CoordinateMultisetClassIn (canonicalApproxFamily k X) y) : ℝ) ≤
      ((n)! : ℝ) / (∏ q, ((profilePartSize (orderedCanonicalRowProfile y δ) q)! : ℝ)) *
        (∏ q, ((orderedCanonicalRowProfile y δ).height q : ℝ) ^
          profilePartSize (orderedCanonicalRowProfile y δ) q) :=
  orderedCanonicalClassIn_cardinality (canonicalApproxFamily k X) y δ

end CircularLaw
