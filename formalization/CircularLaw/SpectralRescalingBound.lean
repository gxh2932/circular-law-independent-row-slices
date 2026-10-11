import CircularLaw.EmpiricalSpectralIntegrals
import CircularLaw.EigenvalueFirstMoment

/-!
# Bounded-Lipschitz distances under actual matrix rescaling

Exact transport of characteristic roots and the first eigenvalue moment
bound control the full bounded-Lipschitz supremum. The bound applies to
every complex matrix, with no normality or diagonalizability assumption.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace CircularLaw

theorem boundedLipschitzDistance_triangle (μ ν ξ : Measure ℂ) :
    boundedLipschitzDistance μ ξ ≤ boundedLipschitzDistance μ ν + boundedLipschitzDistance ν ξ := by
  apply iSup_le
  intro f
  calc
    ENNReal.ofReal |(∫ z, f.val z ∂μ) - ∫ z, f.val z ∂ξ| ≤
        ENNReal.ofReal (|(∫ z, f.val z ∂μ) - ∫ z, f.val z ∂ν| +
          |(∫ z, f.val z ∂ν) - ∫ z, f.val z ∂ξ|) :=
      ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ ≤ _ + _ := ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add
      (le_iSup (fun g : BLTest => ENNReal.ofReal |(∫ z, g.val z ∂μ) - ∫ z, g.val z ∂ν|) f)
      (le_iSup (fun g : BLTest => ENNReal.ofReal |(∫ z, g.val z ∂ν) - ∫ z, g.val z ∂ξ|) f)

theorem boundedLipschitzDistance_symm (μ ν : Measure ℂ) :
    boundedLipschitzDistance μ ν = boundedLipschitzDistance ν μ := by
  simp only [boundedLipschitzDistance, abs_sub_comm]

theorem bl_test_rescaling_pointwise (f : BLTest) (c z : ℂ) :
    |f.val (c * z) - f.val z| ≤ ‖c - 1‖ * ‖z‖ := by
  have h := f.property.2.dist_le_mul (c * z) z
  simp only [dist_eq_norm, NNReal.coe_one, one_mul] at h
  have hEq : c * z - z = (c - 1) * z := by ring
  rw [hEq, norm_mul] at h
  exact h

theorem bl_test_empirical_rescaling_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (f : BLTest) :
    |(∫ z, f.val z ∂empiricalSpectralMeasure (c • A)) -
      ∫ z, f.val z ∂empiricalSpectralMeasure A| ≤ ‖c - 1‖ * squareEigenvalueFirstMoment A := by
  have hAbs : |(n : ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg n)
  rw [empiricalSpectralMeasure_integral_smul, empiricalSpectralMeasure_integral,
    multiset_map_sum_eq_fin_sum, multiset_map_sum_eq_fin_sum,
    ← sub_div, abs_div, hAbs, ← Finset.sum_sub_distrib]
  calc
    _ ≤ (∑ i : Fin A.charpoly.roots.toList.length,
        |f.val (c * A.charpoly.roots.toList.get i) - f.val (A.charpoly.roots.toList.get i)|) / n :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg n)
    _ ≤ (∑ i : Fin A.charpoly.roots.toList.length, ‖c - 1‖ * ‖A.charpoly.roots.toList.get i‖) / n :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum (fun _ _ => bl_test_rescaling_pointwise f c _)) (Nat.cast_nonneg n)
    _ = _ := by
      rw [← Finset.mul_sum, ← multiset_map_sum_eq_fin_sum]
      unfold squareEigenvalueFirstMoment
      ring

theorem empirical_spectral_rescaling_distance_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    boundedLipschitzDistance (empiricalSpectralMeasure (c • A)) (empiricalSpectralMeasure A) ≤
      ENNReal.ofReal (‖c - 1‖ * Real.sqrt (squareMatrixEnergy A / n)) := by
  apply iSup_le
  intro f
  apply ENNReal.ofReal_le_ofReal
  exact (bl_test_empirical_rescaling_bound A c f).trans
    (mul_le_mul_of_nonneg_left (square_eigenvalue_first_moment_bound A) (norm_nonneg _))

end CircularLaw
