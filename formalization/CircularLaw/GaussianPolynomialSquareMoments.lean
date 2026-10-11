import CircularLaw.GaussianPolynomialMoments
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Gaussian polynomial conjugation and exact square expectations

Conjugation conjugates coefficients and exchanges the two entry tags.
The resulting polynomial evaluates to the actual complex conjugate.
All norm powers are integrable, and mean-square norms are given by the
same checked finite polynomial expectation functional.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def gaussianPolynomialStarHom {ι : Type*} : GaussianPolynomial ι →+* GaussianPolynomial ι :=
  (MvPolynomial.rename (fun bi : Bool × ι => (!bi.1, bi.2))).toRingHom.comp
    (MvPolynomial.map (starRingEnd ℂ))

theorem gaussian_polynomial_star_evaluation_hom {ι : Type*} (x : ι → ℂ) :
    (MvPolynomial.eval (gaussianPolynomialVariables x)).comp gaussianPolynomialStarHom =
      (starRingEnd ℂ).comp (MvPolynomial.eval (gaussianPolynomialVariables x)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gaussianPolynomialStarHom]
  · rintro ⟨b, i⟩
    cases b <;> simp [gaussianPolynomialStarHom, gaussianPolynomialVariables]

theorem gaussian_polynomial_star_evaluation {ι : Type*} (p : GaussianPolynomial ι)
    (x : ι → ℂ) :
    gaussianPolynomialEvaluation (gaussianPolynomialStarHom p) x =
      star (gaussianPolynomialEvaluation p x) :=
  RingHom.congr_fun (gaussian_polynomial_star_evaluation_hom x) p

theorem gaussian_polynomial_norm_square_real {ι : Type*} (p : GaussianPolynomial ι)
    (x : ι → ℂ) :
    ‖gaussianPolynomialEvaluation p x‖ ^ 2 =
      (gaussianPolynomialEvaluation (p * gaussianPolynomialStarHom p) x).re := by
  rw [gaussian_polynomial_evaluation_mul, gaussian_polynomial_star_evaluation]
  have h : gaussianPolynomialEvaluation p x * star (gaussianPolynomialEvaluation p x) =
      ((‖gaussianPolynomialEvaluation p x‖ ^ 2 : ℝ) : ℂ) := by
    simpa using complex_balanced_power_eq_norm_power (gaussianPolynomialEvaluation p x) 1
  rw [h, Complex.ofReal_re]

theorem gaussian_polynomial_norm_power_integrable {ι : Type*} [Fintype ι]
    (p : GaussianPolynomial ι) (k : ℕ) :
    Integrable (fun x => ‖gaussianPolynomialEvaluation p x‖ ^ k)
      (standardComplexGaussianProductLaw ι) := by
  have hNorm := (gaussian_polynomial_evaluation_integrable (p ^ k)).norm
  have hEq : (fun x => ‖gaussianPolynomialEvaluation (p ^ k) x‖) =
      fun x => ‖gaussianPolynomialEvaluation p x‖ ^ k := by
    funext x
    rw [gaussian_polynomial_evaluation_pow, norm_pow]
  rw [hEq] at hNorm
  exact hNorm

theorem gaussian_polynomial_norm_square_integral {ι : Type*} [Fintype ι]
    (p : GaussianPolynomial ι) :
    (∫ x, ‖gaussianPolynomialEvaluation p x‖ ^ 2 ∂standardComplexGaussianProductLaw ι) =
      (gaussianPolynomialMean (p * gaussianPolynomialStarHom p)).re := by
  simp only [gaussian_polynomial_norm_square_real]
  change (∫ x, RCLike.re (gaussianPolynomialEvaluation (p * gaussianPolynomialStarHom p) x)
    ∂standardComplexGaussianProductLaw ι) = _
  rw [integral_re (gaussian_polynomial_evaluation_integrable _), gaussian_polynomial_evaluation_integral]
  rfl

theorem gaussian_polynomial_mean_square_nonneg {ι : Type*} [Fintype ι]
    (p : GaussianPolynomial ι) :
    0 ≤ (gaussianPolynomialMean (p * gaussianPolynomialStarHom p)).re := by
  rw [← gaussian_polynomial_norm_square_integral]
  exact integral_nonneg (fun _ => sq_nonneg _)

end CircularLaw
