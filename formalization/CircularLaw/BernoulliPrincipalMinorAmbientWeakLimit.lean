import CircularLaw.BernoulliPrincipalMinorWeakLimit
import CircularLaw.ScaledEmpiricalWeakTransfer

/-!
# The ambient-normalized weak law of an actual Bernoulli principal minor

For a limiting minor dimension ratio theta > 0, the source keeps the
ambient square-root-degree normalization. Its singular law is the
sqrt(theta) pushforward of the Gaussian law shifted by z/sqrt(theta).
The varying finite-dimensional scale is handled by a checked relative
perturbation argument, with the actual ambient probability measure.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def gaussianMinorSingularLimit (theta : ℝ) (z : ℂ) : Measure ℝ≥0 :=
  (gaussianShiftedSingularLimit (z / (Real.sqrt theta : ℂ))).map
    (fun t : ℝ≥0 => Real.toNNReal (Real.sqrt theta) * t)

instance gaussianMinorSingularLimit_probability (theta : ℝ) (z : ℂ) :
    IsProbabilityMeasure (gaussianMinorSingularLimit theta z) :=
  (gaussianShiftedSingularLimit (z / (Real.sqrt theta : ℂ))).isProbabilityMeasure_map
    (continuous_const.mul continuous_id).measurable.aemeasurable

theorem bernoulli_principal_minor_ambient_affine_rescaling {m n : ℕ}
    (hmn : m ≤ n) (hm : 0 < m) (hn : 0 < n)
    (d : ℕ) (z w : ℂ) (x : BernoulliSquareSample n) :
    squarePrincipalMinor (normalizedShiftedBernoulliMatrix d z x) hmn =
      (Real.sqrt ((m : ℝ) / n) : ℂ) •
          parameterNormalizedShiftedBernoulliMatrix (rowBernoulliParameter n d) w
            (bernoulliPrincipalMinorSample hmn x) +
        ((Real.sqrt ((m : ℝ) / n) : ℂ) * w - z) • 1 := by
  have hPos : 0 < Real.sqrt ((m : ℝ) / n) :=
    Real.sqrt_pos.2 (div_pos (by exact_mod_cast hm) (by exact_mod_cast hn))
  have hNonzero : (Real.sqrt ((m : ℝ) / n) : ℂ) ≠ 0 := by
    exact_mod_cast hPos.ne'
  have hZero := bernoulli_principal_minor_effective_rescaling hmn d 0 x
  simp only [zero_div] at hZero
  have hScale := congrArg
    (fun M => (Real.sqrt ((m : ℝ) / n) : ℂ) • M) hZero
  dsimp only at hScale
  rw [smul_inv_smul₀ hNonzero] at hScale
  have hShift : parameterNormalizedShiftedBernoulliMatrix (rowBernoulliParameter n d) w
      (bernoulliPrincipalMinorSample hmn x) =
      parameterNormalizedShiftedBernoulliMatrix (rowBernoulliParameter n d) 0
        (bernoulliPrincipalMinorSample hmn x) - w • 1 := by
    simp only [parameterNormalizedShiftedBernoulliMatrix, zero_smul, sub_zero]
  have hMinorShift : squarePrincipalMinor (normalizedShiftedBernoulliMatrix d z x) hmn =
      squarePrincipalMinor (normalizedShiftedBernoulliMatrix d 0 x) hmn - z • 1 := by
    simp only [bernoulli_shifted_principal_minor_matrix_eq, zero_smul, sub_zero]
  rw [hShift, hMinorShift, ← hScale]
  module

theorem bernoulli_principal_minor_ambient_weak_convergence (q d : ℕ → ℕ)
    (hq : ∀ n, q n ≤ n) (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    {theta : ℝ} (hTheta : 0 < theta)
    (hRatio : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 theta)) (z : ℂ) :
    EmpiricalWeakConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => squareSingularValuesNNReal
        (squarePrincipalMinor (normalizedShiftedBernoulliMatrix (d n) z x) (hq n)))
      (gaussianMinorSingularLimit theta z) := by
  let c := Real.sqrt theta
  let w := z / (c : ℂ)
  let r := fun n => Real.sqrt ((q n : ℝ) / n)
  have hc : 0 < c := Real.sqrt_pos.2 hTheta
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hQ := minor_dimension_tendsto_of_positive_ratio q hTheta hRatio
  have hr : Tendsto r atTop (𝓝 c) := Real.continuous_sqrt.continuousAt.tendsto.comp hRatio
  have hrC : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 (c : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hw : Tendsto (fun n => (r n : ℂ) * w - z) atTop (𝓝 0) := by
    have h := (hrC.mul_const w).sub_const z
    have hEq : (c : ℂ) * w - z = 0 := by
      dsimp [w]
      field_simp
      ring
    rwa [hEq] at h
  have hWeak := bernoulli_principal_minor_effective_weak_convergence q d hq
    hDegree hSparse hTheta hRatio w
  have hAffine := empirical_square_singular_weak_convergence_scale_shift
    (fun n => sparseBernoulliMatrixLaw n (d n)) q hQ
    (fun n x => parameterNormalizedShiftedBernoulliMatrix (min (rowBernoulliParameter n (d n)) 1)
      w (bernoulliPrincipalMinorSample (hq n) x))
    (gaussianShiftedSingularLimit w) (128 + ‖w‖) (by positivity)
    (gaussian_shifted_limit_support w) r (fun n => (r n : ℂ) * w - z) hc
    (fun _ => Real.sqrt_nonneg _) hr hw hWeak
  intro f hf hBound epsilon hEpsilon
  have h := hAffine f hf hBound epsilon hEpsilon
  apply h.congr'
  filter_upwards [sparse_degrees_eventually_valid d hDegree hSparse,
    hQ.eventually_gt_atTop 0] with n hn hqn
  have hMatrix (x : BernoulliSquareSample n) :=
    bernoulli_principal_minor_ambient_affine_rescaling (hq n) hqn hn.1 (d n) z w x
  dsimp only [r] at hMatrix ⊢
  rw [min_eq_left (rowBernoulliParameter_le_one hn.1 hn.2.2)]
  simp only [← hMatrix]
  rfl

theorem bernoulli_fixed_fraction_minor_ambient_weak_convergence (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    {epsilon : ℝ} (hNonneg : 0 ≤ epsilon) (hOne : epsilon < 1) (z : ℂ) :
    EmpiricalWeakConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => squareSingularValuesNNReal
        (squarePrincipalMinor (normalizedShiftedBernoulliMatrix (d n) z x)
          (bernoulli_squeeze_lengths_le (n := n) hNonneg).2))
      (gaussianMinorSingularLimit (1 - epsilon) z) :=
  bernoulli_principal_minor_ambient_weak_convergence
    (fun n => bernoulliSqueezeMinorDimension n epsilon) d
    (fun n => (bernoulli_squeeze_lengths_le (n := n) hNonneg).2) hDegree hSparse
    (by linarith : 0 < 1 - epsilon) (bernoulli_squeeze_fixed_minor_ratio_tendsto hOne) z

end CircularLaw
