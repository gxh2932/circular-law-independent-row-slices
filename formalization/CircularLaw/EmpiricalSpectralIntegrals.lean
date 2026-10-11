import CircularLaw.Statement
import CircularLaw.CharacteristicRootScaling

/-!
# Literal empirical spectral integrals and scalar root transport

Every characteristic root is counted with algebraic multiplicity. The
finite Dirac sum is integrable for every real-valued test function.
-/

noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace CircularLaw

theorem integrable_multiset_dirac_sum (s : Multiset ℂ) (f : ℂ → ℝ) :
    Integrable f ((s.map fun z => Measure.dirac z).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (integrable_dirac (by finiteness : ‖f z‖ₑ < ∞)).add_measure ih

theorem integral_multiset_dirac_sum (s : Multiset ℂ) (f : ℂ → ℝ) :
    (∫ z, f z ∂(s.map fun z => Measure.dirac z).sum) = (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [integral_add_measure (integrable_dirac (by finiteness : ‖f z‖ₑ < ∞))
      (integrable_multiset_dirac_sum s f), integral_dirac, ih]

theorem empiricalSpectralMeasure_integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (f : ℂ → ℝ) :
    (∫ z, f z ∂empiricalSpectralMeasure A) = (A.charpoly.roots.map f).sum / n := by
  rw [empiricalSpectralMeasure, integral_smul_measure, integral_multiset_dirac_sum]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, inv_mul_eq_div]

theorem empiricalSpectralMeasure_integral_smul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (f : ℂ → ℝ) :
    (∫ z, f z ∂empiricalSpectralMeasure (c • A)) =
      (A.charpoly.roots.map (fun z => f (c * z))).sum / n := by
  rw [empiricalSpectralMeasure_integral, matrix_charpoly_roots_smul, Multiset.map_map]
  rfl

end CircularLaw
