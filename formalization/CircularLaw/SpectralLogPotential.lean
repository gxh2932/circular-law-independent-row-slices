import CircularLaw.CharacteristicRootShift
import CircularLaw.SquareSingularDeterminant
import CircularLaw.ExtendedEmpiricalLog
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
# The actual ESD logarithmic potential and shifted determinant

Off the finite eigenvalue set the integral equals the normalized shifted
logarithmic determinant. The extended values agree at every shift: both
are minus infinity when the shifted matrix is singular. The same value
is the empirical extended logarithm of its actual singular values.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def spectralLogPotential {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : ℝ :=
  ∫ w, Real.log ‖z - w‖ ∂empiricalSpectralMeasure A

/-- The extended logarithmic integral of a finite atomic ESD. A positive
atom at the evaluation point contributes minus infinity. -/
def extendedSpectralLogPotential {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : EReal :=
  if z ∈ A.charpoly.roots then ⊥ else (spectralLogPotential A z : EReal)

def normalizedLogDeterminant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : ℝ :=
  Real.log ‖(A - z • 1).det‖ / n

def normalizedExtendedLogDeterminant {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : EReal :=
  if (A - z • 1).det = 0 then ⊥ else (normalizedLogDeterminant A z : EReal)

theorem extended_spectral_log_potential_eq_atom_formula {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    extendedSpectralLogPotential A z =
      if empiricalSpectralMeasure A {z} ≠ 0 then ⊥ else (spectralLogPotential A z : EReal) := by
  simp only [extendedSpectralLogPotential, empiricalSpectralMeasure_atom_iff_characteristic_root]

theorem shifted_norm_det_eq_characteristic_product {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    ‖(A - z • 1).det‖ = (A.charpoly.roots.map (fun w => ‖z - w‖)).prod := by
  have hNorm (s : Multiset ℂ) : ‖s.prod‖ = (s.map (fun w => ‖w‖)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons w s ih => simp [ih]
  have hNeg : z • (1 : Matrix (Fin n) (Fin n) ℂ) - A = -(A - z • 1) := by abel
  have hEval : ‖A.charpoly.eval z‖ = ‖(A - z • 1).det‖ := by
    rw [Matrix.eval_charpoly, matrix_scalar_eq_smul_one, hNeg, Matrix.det_neg,
      norm_mul, norm_pow]
    simp
  rw [← hEval, (IsAlgClosed.splits A.charpoly).eval_eq_prod_roots_of_monic
    A.charpoly_monic, hNorm, Multiset.map_map]
  rfl

theorem spectral_log_potential_eq_log_determinant {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (hDet : (A - z • 1).det ≠ 0) :
    spectralLogPotential A z = normalizedLogDeterminant A z := by
  have hz : z ∉ A.charpoly.roots :=
    (shifted_det_zero_iff_characteristic_root A z).not.mp hDet
  have hNonzero : ∀ t ∈ A.charpoly.roots.map (fun w => ‖z - w‖), t ≠ 0 := by
    intro t ht
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp ht
    apply norm_ne_zero_iff.mpr
    apply sub_ne_zero.mpr
    intro h
    exact hz (h.symm ▸ hw)
  rw [spectralLogPotential, empiricalSpectralMeasure_integral,
    normalizedLogDeterminant, shifted_norm_det_eq_characteristic_product,
    Real.log_multiset_prod hNonzero, Multiset.map_map]
  rfl

theorem extended_spectral_log_potential_eq_log_determinant {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    extendedSpectralLogPotential A z = normalizedExtendedLogDeterminant A z := by
  unfold extendedSpectralLogPotential normalizedExtendedLogDeterminant
  by_cases hDet : (A - z • 1).det = 0
  · have hz := (shifted_det_zero_iff_characteristic_root A z).mp hDet
    simp only [hDet, hz, if_true]
  · have hz := (shifted_det_zero_iff_characteristic_root A z).not.mp hDet
    simp only [hDet, hz, if_false, spectral_log_potential_eq_log_determinant A z hDet]

theorem shifted_singular_empirical_mean_eq_log_determinant {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (hDet : (A - z • 1).det ≠ 0) :
    empiricalNonnegativeMean (squareSingularValuesNNReal (A - z • 1))
      (fun t => Real.log (t : ℝ)) = normalizedLogDeterminant A z := by
  unfold empiricalNonnegativeMean finiteMean normalizedLogDeterminant
  simp only [Fintype.card_fin]
  rw [square_log_norm_det_eq_singular_log_sum _ hDet]
  rfl

theorem shifted_singular_extended_log_eq_spectral_potential {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    empiricalExtendedLogIntegral (squareSingularValuesNNReal (A - z • 1)) =
      extendedSpectralLogPotential A z := by
  rw [extended_spectral_log_potential_eq_log_determinant]
  unfold empiricalExtendedLogIntegral normalizedExtendedLogDeterminant
  simp only [square_singular_has_zero_iff_det_zero]
  by_cases hDet : (A - z • 1).det = 0
  · simp only [hDet, if_true]
  · simp only [hDet, if_false, shifted_singular_empirical_mean_eq_log_determinant A z hDet]

theorem shifted_singular_set_finite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    {z : ℂ | (A - z • 1).det = 0}.Finite := by
  have hSet : {z : ℂ | (A - z • 1).det = 0} = ↑A.charpoly.roots.toFinset := by
    ext z
    simp [shifted_det_zero_iff_characteristic_root]
  rw [hSet]
  exact Finset.finite_toSet _

theorem shifted_singular_set_volume_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    volume {z : ℂ | (A - z • 1).det = 0} = 0 :=
  (shifted_singular_set_finite A).measure_zero volume

theorem spectral_log_potential_eq_log_determinant_ae {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralLogPotential A =ᵐ[volume] normalizedLogDeterminant A := by
  have hNonzero : ∀ᵐ z : ℂ ∂volume, (A - z • 1).det ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using shifted_singular_set_volume_zero A
  filter_upwards [hNonzero] with z hz
  exact spectral_log_potential_eq_log_determinant A z hz

end CircularLaw
