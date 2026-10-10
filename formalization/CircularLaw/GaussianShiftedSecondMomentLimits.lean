import CircularLaw.GaussianNormalizedWordCovariance
import CircularLaw.GaussianShiftedMomentMeanLimits
import CircularLaw.FiniteListSecondMoments

/-!
# Actual shifted Gaussian trace second-moment limits

The checked covariance limit gives the product-mean limit for every pair
of finite words. The scalar-shift expansion then passes the actual
second moment through the finite list of all ordered word pairs. No
independence between word traces or limiting law is assumed.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem gaussian_normalized_word_product_mean_tendsto (w v : List Bool) :
    Tendsto (fun n : ℕ => ∫ x,
      gaussianNormalizedWordTrace w x * gaussianNormalizedWordTrace v x
      ∂gaussianSquareMatrixLaw n) atTop
      (𝓝 ((gaussianWordMeanCount w : ℂ) * (gaussianWordMeanCount v : ℂ))) := by
  have h := (gaussian_normalized_word_covariance_tendsto w v).add
    ((gaussian_word_mean_count_tendsto w).mul (gaussian_word_mean_count_tendsto v))
  simpa only [gaussianNormalizedWordCovariance, sub_add_cancel, zero_add] using h

def gaussianShiftedNormalizedTrace {n : ℕ} (z : ℂ) (k : ℕ)
    (x : GaussianSquareSample n) : ℂ :=
  ((normalizedShiftedGaussianMatrix z x *
    (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace / n

theorem gaussian_shifted_normalized_trace_expansion {n : ℕ} (z : ℂ) (k : ℕ)
    (x : GaussianSquareSample n) :
    gaussianShiftedNormalizedTrace z k x =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun p => p.1 * gaussianNormalizedWordTrace p.2 x)).sum :=
  gaussian_shifted_normalized_trace_word_expansion z k x

theorem gaussian_shifted_normalized_trace_square_integrable (n : ℕ) (z : ℂ) (k : ℕ) :
    Integrable (fun x => gaussianShiftedNormalizedTrace z k x ^ 2)
      (gaussianSquareMatrixLaw n) := by
  simp only [gaussian_shifted_normalized_trace_expansion]
  exact finite_list_weighted_square_integrable _ _ Prod.fst
    (fun p x => gaussianNormalizedWordTrace p.2 x)
    (fun p _ q _ => gaussian_normalized_word_product_integrable n p.2 q.2)

theorem gaussian_shifted_normalized_trace_square_integral (n : ℕ) (z : ℂ) (k : ℕ) :
    (∫ x, gaussianShiftedNormalizedTrace z k x ^ 2 ∂gaussianSquareMatrixLaw n) =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map (fun p =>
        ((scalarShiftWordExpansion z (gramMatrixWord k)).map (fun q =>
          (p.1 * q.1) * (∫ x, gaussianNormalizedWordTrace p.2 x *
            gaussianNormalizedWordTrace q.2 x ∂gaussianSquareMatrixLaw n))).sum)).sum := by
  simp only [gaussian_shifted_normalized_trace_expansion]
  exact finite_list_weighted_square_integral _ _ Prod.fst
    (fun p x => gaussianNormalizedWordTrace p.2 x)
    (fun p _ q _ => gaussian_normalized_word_product_integrable n p.2 q.2)

theorem gaussian_shifted_normalized_trace_square_mean_tendsto (z : ℂ) (k : ℕ) :
    Tendsto (fun n : ℕ => ∫ x, gaussianShiftedNormalizedTrace z k x ^ 2
      ∂gaussianSquareMatrixLaw n) atTop (𝓝 (gaussianShiftedMomentMeanLimit z k ^ 2)) := by
  simp only [gaussian_shifted_normalized_trace_square_integral, gaussianShiftedMomentMeanLimit,
    finite_list_weighted_square_expansion]
  apply finite_list_sum_tendsto
  intro p _
  apply finite_list_sum_tendsto
  intro q _
  exact tendsto_const_nhds.mul (gaussian_normalized_word_product_mean_tendsto p.2 q.2)

end CircularLaw
