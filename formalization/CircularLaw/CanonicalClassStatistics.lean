import CircularLaw.CanonicalClassInvariants
import CircularLaw.CanonicalProfileStatistics
import CircularLaw.FixedNetSlice

/-!
# Canonical statistics are constant on coordinate-multiset classes

The canonical procedure chooses leftmost occurrences, so an input
permutation need not transport its coordinate labels pointwise. The
comparison instead uses the creation-order labels, their equal masses,
and their equal heights and kinds. This proves equality of the actual
geometric mean, dispersion and fixed-vector probability estimate.
-/

noncomputable section
open Classical
open scoped BigOperators

attribute [local irreducible] CircularLaw.canonicalCoordinateLabel
attribute [local irreducible] CircularLaw.taggedPart CircularLaw.taggedValues

namespace CircularLaw

def canonicalLabelMultisetEquiv {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) :
    CanonicalLabel y η ≃ CanonicalLabel z η :=
  Equiv.subtypeEquivRight (fun q => (taggedPart_nonempty_multiset_iff y z h η q).symm)

theorem canonicalLabelMultisetEquiv_val {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) (q : CanonicalLabel y η) :
    @Subtype.val (Bool × Fin (n + 2)) (fun p => (taggedPart z η p).Nonempty)
      (canonicalLabelMultisetEquiv y z h η q) =
    @Subtype.val (Bool × Fin (n + 2)) (fun p => (taggedPart y η p).Nonempty) q := by
  exact congrArg (@Subtype.val (Bool × Fin (n + 2)) (fun p => (taggedPart z η p).Nonempty))
    (Equiv.subtypeEquivRight_apply (fun p => (taggedPart_nonempty_multiset_iff y z h η p).symm) q)

theorem canonical_profile_size_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) (q : CanonicalLabel y η) :
    profilePartSize (canonicalRowProfile z η) (canonicalLabelMultisetEquiv y z h η q) =
      profilePartSize (canonicalRowProfile y η) q := by
  change Nat.card {i : Fin n // (canonicalRowProfile z η).part i =
    canonicalLabelMultisetEquiv y z h η q} =
      Nat.card {i : Fin n // (canonicalRowProfile y η).part i = q}
  rw [canonicalPart_card, canonicalPart_card, canonicalLabelMultisetEquiv_val]
  exact taggedPart_card_multiset_eq y z h η q.val

theorem canonical_profile_mass_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) (q : CanonicalLabel y η) :
    partMass (canonicalRowProfile z η).part (canonicalLabelMultisetEquiv y z h η q) =
      partMass (canonicalRowProfile y η).part q := by
  rw [partMass_eq_profile_size, partMass_eq_profile_size,
    canonical_profile_size_multiset_eq y z h η q]

theorem canonical_profile_height_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) (q : CanonicalLabel y η) :
    (canonicalRowProfile z η).height (canonicalLabelMultisetEquiv y z h η q) =
      (canonicalRowProfile y η).height q := by
  change (taggedValues z η (canonicalLabelMultisetEquiv y z h η q).val).card =
    (taggedValues y η q.val).card
  rw [canonicalLabelMultisetEquiv_val, taggedValues_multiset_eq y z h η q.val]

theorem canonical_profile_spread_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) (q : CanonicalLabel y η) :
    (canonicalRowProfile z η).spread (canonicalLabelMultisetEquiv y z h η q) =
      (canonicalRowProfile y η).spread q := by
  exact congrArg (fun p : Bool × Fin (n + 2) => p.1)
    (canonicalLabelMultisetEquiv_val y z h η q)

theorem canonical_profile_weight_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) (d : ℕ) (q : CanonicalLabel y η) :
    truncatedProfileWeight (canonicalRowProfile z η) d (canonicalLabelMultisetEquiv y z h η q) =
      truncatedProfileWeight (canonicalRowProfile y η) d q := by
  unfold truncatedProfileWeight
  rw [canonical_profile_mass_multiset_eq y z h η q,
    canonical_profile_height_multiset_eq y z h η q,
    canonical_profile_spread_multiset_eq y z h η q]

theorem canonical_profile_mean_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) (d : ℕ) :
    profileGeometricMean (canonicalRowProfile z η).part
      (truncatedProfileWeight (canonicalRowProfile z η) d) =
    profileGeometricMean (canonicalRowProfile y η).part
      (truncatedProfileWeight (canonicalRowProfile y η) d) := by
  unfold profileGeometricMean
  rw [← (canonicalLabelMultisetEquiv y z h η).prod_comp
    (fun q => Real.rpow (truncatedProfileWeight (canonicalRowProfile z η) d q)
      (-partMass (canonicalRowProfile z η).part q))]
  apply Finset.prod_congr rfl
  intro q _
  rw [canonical_profile_weight_multiset_eq y z h η d q,
    canonical_profile_mass_multiset_eq y z h η q]

theorem pairDispersion_part_formula {α ι : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (B : ι → ℝ) :
    pairDispersion (fun a => B (part a)) =
      ∑ q, partMass part q * ∑ r, partMass part r * |B q - B r| := by
  rw [pairDispersion, finiteMean_prod_fubini]
  change finiteMean (fun b => finiteMean (fun a => |B (part a) - B (part b)|)) = _
  have hInner (b : α) : finiteMean (fun a => |B (part a) - B (part b)|) =
      ∑ q, partMass part q * |B q - B (part b)| :=
    finiteMean_part_function part (fun q => |B q - B (part b)|)
  have hOuter (q : ι) : finiteMean (fun b => |B q - B (part b)|) =
      ∑ r, partMass part r * |B q - B r| :=
    finiteMean_part_function part (fun r => |B q - B r|)
  simp_rw [hInner]
  rw [finiteMean_finset_sum]
  simp_rw [finiteMean_const_mul, hOuter]

theorem canonical_profile_dispersion_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) (d : ℕ) :
    profileCoordinateDispersion (canonicalRowProfile z η) d =
      profileCoordinateDispersion (canonicalRowProfile y η) d := by
  unfold profileCoordinateDispersion
  rw [pairDispersion_part_formula (canonicalRowProfile z η).part
    (fun q => dyadicWeight (truncatedProfileWeight (canonicalRowProfile z η) d q)),
    pairDispersion_part_formula (canonicalRowProfile y η).part
      (fun q => dyadicWeight (truncatedProfileWeight (canonicalRowProfile y η) d q))]
  rw [← (canonicalLabelMultisetEquiv y z h η).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  rw [canonical_profile_mass_multiset_eq y z h η q,
    ← (canonicalLabelMultisetEquiv y z h η).sum_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [canonical_profile_mass_multiset_eq y z h η r,
    canonical_profile_weight_multiset_eq y z h η d q,
    canonical_profile_weight_multiset_eq y z h η d r]

theorem orderedCanonical_profile_mean_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) {d : ℕ} (hd : 0 < d) :
    profileGeometricMean (orderedCanonicalRowProfile z η).part
      (truncatedProfileWeight (orderedCanonicalRowProfile z η) d) =
    profileGeometricMean (orderedCanonicalRowProfile y η).part
      (truncatedProfileWeight (orderedCanonicalRowProfile y η) d) := by
  rw [orderedCanonical_profile_mean_eq z η hd, orderedCanonical_profile_mean_eq y η hd]
  exact canonical_profile_mean_multiset_eq y z h η d

theorem orderedCanonical_profile_dispersion_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (η : ℝ) (d : ℕ) :
    profileCoordinateDispersion (orderedCanonicalRowProfile z η) d =
      profileCoordinateDispersion (orderedCanonicalRowProfile y η) d := by
  rw [orderedCanonical_profile_dispersion_eq, orderedCanonical_profile_dispersion_eq]
  exact canonical_profile_dispersion_multiset_eq y z h η d

theorem fixedNetSliceEstimate_multiset_eq {n : ℕ} (y z : Fin n → ℂ)
    (h : coordinateMultiset z = coordinateMultiset y) (k K : ℕ) {d : ℕ} (hd : 0 < d) (R : ℝ) :
    fixedNetSliceEstimate k d K z R = fixedNetSliceEstimate k d K y R := by
  dsimp only [fixedNetSliceEstimate]
  rw [orderedCanonical_profile_dispersion_multiset_eq y z h ((d : ℝ) / k) d,
    orderedCanonical_profile_mean_multiset_eq y z h ((d : ℝ) / k) hd]

end CircularLaw
