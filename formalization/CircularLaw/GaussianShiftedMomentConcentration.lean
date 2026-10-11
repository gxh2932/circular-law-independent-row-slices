import CircularLaw.GaussianShiftedSecondMomentLimits
import CircularLaw.GaussianMomentVariance
import CircularLaw.VaryingMeanSquareConvergence

/-!
# Every actual shifted Gaussian singular moment concentrates

Hermitian reality identifies the normalized Gram trace with the real
even singular moment. Its first and second means have the same limiting
square, so the actual centered-square integral tends to zero. Markov's
inequality gives convergence in probability for every shift and order.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

def gaussianShiftedSingularMoment {n : ℕ} (z : ℂ) (k : ℕ)
    (x : GaussianSquareSample n) : ℝ :=
  ∫ t, (t : ℝ) ^ (2 * k) ∂gaussianSingularMeasure z x

theorem gaussian_shifted_singular_moment_ofReal {n : ℕ} (z : ℂ) (k : ℕ)
    (x : GaussianSquareSample n) :
    Complex.ofReal (gaussianShiftedSingularMoment z k x) =
      gaussianShiftedNormalizedTrace z k x := by
  rw [gaussianShiftedSingularMoment, gaussian_shifted_singular_even_moment_trace,
    gaussianShiftedNormalizedTrace, Complex.ofReal_div, Complex.ofReal_natCast]
  exact congrArg (fun t : ℂ => t / (n : ℂ))
    (hermitian_trace_pow_eq_ofReal_re _ (Matrix.isHermitian_mul_conjTranspose_self _) k).symm

theorem gaussian_shifted_singular_moment_integrable (n : ℕ) (z : ℂ) (k : ℕ) :
    Integrable (gaussianShiftedSingularMoment (n := n) z k) (gaussianSquareMatrixLaw n) :=
  gaussian_shifted_singular_even_moment_integrable n z k

theorem gaussian_shifted_singular_moment_square_integrable (n : ℕ) (z : ℂ) (k : ℕ) :
    Integrable (fun x => gaussianShiftedSingularMoment z k x ^ 2)
      (gaussianSquareMatrixLaw n) := by
  have h := (gaussian_shifted_normalized_trace_square_integrable n z k).re
  simpa only [← gaussian_shifted_singular_moment_ofReal, ← Complex.ofReal_pow,
    Complex.ofReal_re] using h

theorem gaussian_shifted_singular_moment_square_mean_eq (n : ℕ) (z : ℂ) (k : ℕ) :
    (∫ x, gaussianShiftedSingularMoment z k x ^ 2 ∂gaussianSquareMatrixLaw n) =
      (∫ x, gaussianShiftedNormalizedTrace z k x ^ 2 ∂gaussianSquareMatrixLaw n).re := by
  change _ = RCLike.re (∫ x, gaussianShiftedNormalizedTrace z k x ^ 2 ∂gaussianSquareMatrixLaw n)
  rw [← integral_re (gaussian_shifted_normalized_trace_square_integrable n z k)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change _ = (gaussianShiftedNormalizedTrace z k x ^ 2).re
    simp only [← gaussian_shifted_singular_moment_ofReal, ← Complex.ofReal_pow,
      Complex.ofReal_re])

theorem gaussian_shifted_moment_mean_limit_eq_real (z : ℂ) (k : ℕ) :
    Complex.ofReal (gaussianShiftedMomentMeanLimit z k).re =
      gaussianShiftedMomentMeanLimit z k := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im, gaussian_shifted_moment_mean_limit_im_zero]

theorem gaussian_shifted_singular_moment_square_mean_tendsto (z : ℂ) (k : ℕ) :
    Tendsto (fun n : ℕ => ∫ x, gaussianShiftedSingularMoment z k x ^ 2
      ∂gaussianSquareMatrixLaw n) atTop (𝓝 ((gaussianShiftedMomentMeanLimit z k).re ^ 2)) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (gaussian_shifted_normalized_trace_square_mean_tendsto z k)
  change Tendsto (fun n : ℕ => (∫ x, gaussianShiftedNormalizedTrace z k x ^ 2
    ∂gaussianSquareMatrixLaw n).re) atTop (𝓝 (gaussianShiftedMomentMeanLimit z k ^ 2).re) at h
  rw [← gaussian_shifted_moment_mean_limit_eq_real z k, ← Complex.ofReal_pow,
    Complex.ofReal_re] at h
  simpa only [gaussian_shifted_singular_moment_square_mean_eq] using h

theorem gaussian_shifted_singular_moment_centered_square_integrable (n : ℕ) (z : ℂ)
    (k : ℕ) (a : ℝ) :
    Integrable (fun x => (gaussianShiftedSingularMoment z k x - a) ^ 2)
      (gaussianSquareMatrixLaw n) := by
  have hEq : (fun x : GaussianSquareSample n => (gaussianShiftedSingularMoment z k x - a) ^ 2) =
      fun x => gaussianShiftedSingularMoment z k x ^ 2 -
        2 * a * gaussianShiftedSingularMoment z k x + a ^ 2 := by
    funext x
    ring
  rw [hEq]
  exact ((gaussian_shifted_singular_moment_square_integrable n z k).sub
    ((gaussian_shifted_singular_moment_integrable n z k).const_mul (2 * a))).add
      (integrable_const _)

theorem gaussian_shifted_singular_moment_centered_square_integral (n : ℕ) (z : ℂ)
    (k : ℕ) (a : ℝ) :
    (∫ x, (gaussianShiftedSingularMoment z k x - a) ^ 2 ∂gaussianSquareMatrixLaw n) =
      (∫ x, gaussianShiftedSingularMoment z k x ^ 2 ∂gaussianSquareMatrixLaw n) -
        2 * a * (∫ x, gaussianShiftedSingularMoment z k x ∂gaussianSquareMatrixLaw n) + a ^ 2 :=
  integral_centered_square_real _ _ (gaussian_shifted_singular_moment_integrable n z k)
    (gaussian_shifted_singular_moment_square_integrable n z k) a

theorem gaussian_shifted_singular_moment_mean_square_tendsto (z : ℂ) (k : ℕ) :
    Tendsto (fun n : ℕ => ∫ x,
      (gaussianShiftedSingularMoment z k x - (gaussianShiftedMomentMeanLimit z k).re) ^ 2
      ∂gaussianSquareMatrixLaw n) atTop (𝓝 0) := by
  let a := (gaussianShiftedMomentMeanLimit z k).re
  have hMean : Tendsto (fun n : ℕ => ∫ x, gaussianShiftedSingularMoment z k x
      ∂gaussianSquareMatrixLaw n) atTop (𝓝 a) :=
    gaussian_shifted_even_moment_mean_tendsto z k
  have h := ((gaussian_shifted_singular_moment_square_mean_tendsto z k).sub
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * a) atTop (𝓝 (2 * a))).mul hMean)).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => a ^ 2) atTop (𝓝 (a ^ 2)))
  change Tendsto _ atTop (𝓝 (a ^ 2 - 2 * a * a + a ^ 2)) at h
  have hZero : a ^ 2 - 2 * a * a + a ^ 2 = 0 := by ring
  simpa only [gaussian_shifted_singular_moment_centered_square_integral, hZero] using h

theorem gaussian_shifted_singular_moment_converges_in_probability (z : ℂ) (k : ℕ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ => gaussianShiftedSingularMoment z k) (gaussianShiftedMomentMeanLimit z k).re :=
  varying_probability_of_mean_square gaussianSquareMatrixLaw _ _
    (fun n => gaussian_shifted_singular_moment_centered_square_integrable n z k _)
    (gaussian_shifted_singular_moment_mean_square_tendsto z k)

end CircularLaw
