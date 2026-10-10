import CircularLaw.GaussianPolynomialMoments
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Unbalanced Gaussian polynomials have zero expectation

Direct variables have integer weight one and conjugate variables weight
minus one. Every balanced entry monomial has weight zero. Thus any
polynomial homogeneous at nonzero imbalance has actual expectation zero.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def gaussianImbalanceWeight {ι : Type*} (bi : Bool × ι) : ℤ := if bi.1 then -1 else 1

theorem gaussian_balanced_exponent_weight {ι : Type*} [Fintype ι]
    (s : (Bool × ι) →₀ ℕ) (h : ∀ i, s (false, i) = s (true, i)) :
    Finsupp.weight gaussianImbalanceWeight s = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype s
      (fun i (c : ℕ) => c • gaussianImbalanceWeight i) (fun i => zero_smul ℕ _),
    Fintype.sum_prod_type, Fintype.sum_bool]
  change (∑ i, s (true, i) • (-1 : ℤ)) + (∑ i, s (false, i) • (1 : ℤ)) = 0
  simp only [h, nsmul_eq_mul, mul_neg, mul_one, Finset.sum_neg_distrib, neg_add_cancel]

theorem gaussian_homogeneous_polynomial_mean_zero {ι : Type*} [Fintype ι]
    (p : GaussianPolynomial ι) {m : ℤ}
    (hp : p.IsWeightedHomogeneous gaussianImbalanceWeight m) (hm : m ≠ 0) :
    gaussianPolynomialMean p = 0 := by
  rw [gaussianPolynomialMean, MvPolynomial.sum_def]
  apply Finset.sum_eq_zero
  intro s hs
  have hWeight := hp (MvPolynomial.mem_support_iff.mp hs)
  have hNotBalanced : ¬∀ i, s (false, i) = s (true, i) := by
    intro h
    exact hm (hWeight.symm.trans (gaussian_balanced_exponent_weight s h))
  rw [if_neg hNotBalanced, mul_zero]

theorem gaussian_homogeneous_polynomial_integral_zero {ι : Type*} [Fintype ι]
    (p : GaussianPolynomial ι) {m : ℤ}
    (hp : p.IsWeightedHomogeneous gaussianImbalanceWeight m) (hm : m ≠ 0) :
    (∫ x, gaussianPolynomialEvaluation p x ∂standardComplexGaussianProductLaw ι) = 0 := by
  rw [gaussian_polynomial_evaluation_integral,
    gaussian_homogeneous_polynomial_mean_zero p hp hm]

end CircularLaw
