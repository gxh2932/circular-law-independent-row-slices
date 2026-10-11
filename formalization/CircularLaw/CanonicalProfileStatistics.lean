import CircularLaw.ProfileMeanPowers
import CircularLaw.SourceProfileDispersion

/-!
# Coordinate statistics agree in the two canonical enumerations

The actual coordinate weight is unchanged when canonical labels are
enumerated spread-first. Thus the dyadic dispersion and geometric mean
in the row-local estimates are the same statistics as in the structural
class estimates.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem orderedCanonical_coordinate_weight_eq {n : ℕ} (y : Fin n → ℂ) (η : ℝ)
    (d : ℕ) (i : Fin n) :
    truncatedProfileWeight (orderedCanonicalRowProfile y η) d
      ((orderedCanonicalRowProfile y η).part i) =
    truncatedProfileWeight (canonicalRowProfile y η) d ((canonicalRowProfile y η).part i) := by
  rw [orderedCanonical_truncatedProfileWeight_eq]
  change truncatedProfileWeight (canonicalRowProfile y η) d
    (canonicalEnumeration y η ((canonicalEnumeration y η).symm (canonicalCoordinateLabel y η i))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem orderedCanonical_profile_dispersion_eq {n : ℕ} (y : Fin n → ℂ) (η : ℝ) (d : ℕ) :
    profileCoordinateDispersion (orderedCanonicalRowProfile y η) d =
      profileCoordinateDispersion (canonicalRowProfile y η) d := by
  unfold profileCoordinateDispersion
  simp_rw [orderedCanonical_coordinate_weight_eq]

theorem orderedCanonical_profile_mean_eq {n : ℕ} (y : Fin n → ℂ) (η : ℝ)
    {d : ℕ} (hd : 0 < d) :
    profileGeometricMean (orderedCanonicalRowProfile y η).part
      (truncatedProfileWeight (orderedCanonicalRowProfile y η) d) =
    profileGeometricMean (canonicalRowProfile y η).part
      (truncatedProfileWeight (canonicalRowProfile y η) d) := by
  rw [profileGeometricMean_eq_exp _ _ (truncatedProfileWeight_pos _ hd),
    profileGeometricMean_eq_exp _ _ (truncatedProfileWeight_pos _ hd)]
  simp_rw [orderedCanonical_coordinate_weight_eq]

end CircularLaw
