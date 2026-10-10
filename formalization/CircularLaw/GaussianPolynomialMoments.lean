import CircularLaw.GaussianEntryProducts
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.BigOperators

/-!
# Every Gaussian entry polynomial has a checked finite expectation

Variables record both the actual entries and their complex conjugates.
Evaluation is expanded over the polynomial's actual finite support.
The exact independent-entry moment formula applies to every exponent,
retaining arbitrary repeated indices and coefficients.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

abbrev GaussianPolynomial (ι : Type*) := MvPolynomial (Bool × ι) ℂ

def gaussianPolynomialVariables {ι : Type*} (x : ι → ℂ) (bi : Bool × ι) : ℂ :=
  if bi.1 then star (x bi.2) else x bi.2

def gaussianPolynomialEvaluation {ι : Type*} (p : GaussianPolynomial ι) (x : ι → ℂ) : ℂ :=
  MvPolynomial.eval (gaussianPolynomialVariables x) p

def gaussianPolynomialMean {ι : Type*} [Fintype ι] (p : GaussianPolynomial ι) : ℂ :=
  p.sum fun s c => c *
    (if ∀ i, s (false, i) = s (true, i) then (∏ i, (s (false, i)).factorial : ℂ) else 0)

theorem gaussian_polynomial_variable_product {ι : Type*} [Fintype ι]
    (s : (Bool × ι) →₀ ℕ) (x : ι → ℂ) :
    (∏ bi : Bool × ι, gaussianPolynomialVariables x bi ^ s bi) =
      ∏ i, x i ^ s (false, i) * star (x i) ^ s (true, i) := by
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  change (∏ i, star (x i) ^ s (true, i)) * (∏ i, x i ^ s (false, i)) = _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem gaussian_polynomial_evaluation_expansion {ι : Type*} [Fintype ι]
    (p : GaussianPolynomial ι) (x : ι → ℂ) :
    gaussianPolynomialEvaluation p x =
      ∑ s ∈ p.support, p.coeff s * (∏ i, x i ^ s (false, i) * star (x i) ^ s (true, i)) := by
  simp only [gaussianPolynomialEvaluation, MvPolynomial.eval_eq', gaussian_polynomial_variable_product]

theorem gaussian_polynomial_evaluation_integrable {ι : Type*} [Fintype ι]
    (p : GaussianPolynomial ι) :
    Integrable (gaussianPolynomialEvaluation p) (standardComplexGaussianProductLaw ι) := by
  have hEq : gaussianPolynomialEvaluation p =
      fun x => ∑ s ∈ p.support, p.coeff s *
        (∏ i, x i ^ s (false, i) * star (x i) ^ s (true, i)) :=
    funext (gaussian_polynomial_evaluation_expansion p)
  rw [hEq]
  apply integrable_finset_sum
  intro s _
  exact (gaussian_entry_monomial_integrable (fun i => s (false, i))
    (fun i => s (true, i))).const_mul _

theorem gaussian_polynomial_evaluation_integral {ι : Type*} [Fintype ι]
    (p : GaussianPolynomial ι) :
    (∫ x, gaussianPolynomialEvaluation p x ∂standardComplexGaussianProductLaw ι) =
      gaussianPolynomialMean p := by
  simp only [gaussian_polynomial_evaluation_expansion]
  rw [integral_finset_sum _ (fun s _ =>
    (gaussian_entry_monomial_integrable (fun i => s (false, i))
      (fun i => s (true, i))).const_mul (p.coeff s))]
  simp only [integral_const_mul, gaussian_entry_monomial_integral,
    gaussianPolynomialMean, MvPolynomial.sum_def]

theorem gaussian_polynomial_evaluation_add {ι : Type*} (p q : GaussianPolynomial ι)
    (x : ι → ℂ) :
    gaussianPolynomialEvaluation (p + q) x =
      gaussianPolynomialEvaluation p x + gaussianPolynomialEvaluation q x :=
  map_add _ _ _

theorem gaussian_polynomial_evaluation_mul {ι : Type*} (p q : GaussianPolynomial ι)
    (x : ι → ℂ) :
    gaussianPolynomialEvaluation (p * q) x =
      gaussianPolynomialEvaluation p x * gaussianPolynomialEvaluation q x :=
  map_mul _ _ _

theorem gaussian_polynomial_evaluation_pow {ι : Type*} (p : GaussianPolynomial ι)
    (k : ℕ) (x : ι → ℂ) :
    gaussianPolynomialEvaluation (p ^ k) x = gaussianPolynomialEvaluation p x ^ k :=
  map_pow _ _ _

end CircularLaw
