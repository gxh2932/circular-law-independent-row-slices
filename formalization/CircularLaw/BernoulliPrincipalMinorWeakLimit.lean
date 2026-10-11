import CircularLaw.BernoulliPrincipalMinorLaw
import CircularLaw.ParameterBernoulliWeakLimit
import CircularLaw.BernoulliSqueezeRounding

/-!
# The effective-degree weak law of an actual Bernoulli principal minor

The minor is drawn by restricting the actual ambient sample, with its
unchanged entry probability. A positive limiting dimension ratio makes
its real effective degree grow. Normalizing by that effective degree
gives the checked Gaussian singular law. The source's ambient-degree
normalization and its untruncated logarithmic upper estimate are separate.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem minor_dimension_tendsto_of_positive_ratio (q : ℕ → ℕ)
    {theta : ℝ} (hTheta : 0 < theta)
    (hRatio : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 theta)) :
    Tendsto q atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have h := hRatio.pos_mul_atTop hTheta
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  exact div_mul_cancel₀ _ hnR

theorem clipped_bernoulli_parameter_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n => (min (rowBernoulliParameter n (d n)) 1 : ℝ≥0).toReal)
      atTop (𝓝 0) := by
  apply hSparse.congr'
  filter_upwards [sparse_degrees_eventually_valid d hDegree hSparse] with n hn
  simp only [min_eq_left (rowBernoulliParameter_le_one hn.1 hn.2.2), rowBernoulliParameter_coe]

theorem clipped_bernoulli_minor_effective_degree_tendsto (q d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    {theta : ℝ} (hTheta : 0 < theta)
    (hRatio : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 theta)) :
    Tendsto (fun n => bernoulliEffectiveDegree (q n) (min (rowBernoulliParameter n (d n)) 1))
      atTop atTop := by
  apply (bernoulli_minor_effective_degree_tendsto q d hDegree hTheta hRatio).congr'
  filter_upwards [sparse_degrees_eventually_valid d hDegree hSparse] with n hn
  rw [min_eq_left (rowBernoulliParameter_le_one hn.1 hn.2.2)]

theorem bernoulli_principal_minor_effective_weak_convergence (q d : ℕ → ℕ)
    (hq : ∀ n, q n ≤ n) (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    {theta : ℝ} (hTheta : 0 < theta)
    (hRatio : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 theta)) (z : ℂ) :
    EmpiricalWeakConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => squareSingularValuesNNReal
        (parameterNormalizedShiftedBernoulliMatrix (min (rowBernoulliParameter n (d n)) 1) z
          (bernoulliPrincipalMinorSample (hq n) x)))
      (gaussianShiftedSingularLimit z) := by
  have hWeak := parameter_bernoulli_weak_convergence q
    (fun n => min (rowBernoulliParameter n (d n)) 1) (fun _ => min_le_right _ _)
    (minor_dimension_tendsto_of_positive_ratio q hTheta hRatio)
    (clipped_bernoulli_minor_effective_degree_tendsto q d hDegree hSparse hTheta hRatio)
    (clipped_bernoulli_parameter_tendsto_zero d hDegree hSparse) z
  intro f hf hBound ε hε
  have h := hWeak f hf hBound ε hε
  apply h.congr'
  refine Eventually.of_forall (fun n => ?_)
  dsimp only
  rw [← bernoulli_sparse_principal_minor_sample_law (hq n),
    map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  rfl

theorem bernoulli_squeeze_fixed_minor_ratio_tendsto {epsilon : ℝ}
    (hOne : epsilon < 1) :
    Tendsto (fun n => (bernoulliSqueezeMinorDimension n epsilon : ℝ) / n)
      atTop (𝓝 (1 - epsilon)) := by
  change Tendsto (fun n : ℕ => (⌊(1 - epsilon) * n⌋₊ : ℝ) / n) atTop (𝓝 (1 - epsilon))
  apply floor_div_nat_tendsto
  · exact Eventually.of_forall (fun n => mul_nonneg (by linarith) (Nat.cast_nonneg n))
  · apply (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 - epsilon : ℝ)) atTop (𝓝 (1 - epsilon))).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    exact (mul_div_cancel_right₀ (1 - epsilon) hnR).symm

theorem bernoulli_fixed_fraction_minor_effective_weak_convergence (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    {epsilon : ℝ} (hNonneg : 0 ≤ epsilon) (hOne : epsilon < 1) (z : ℂ) :
    EmpiricalWeakConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => squareSingularValuesNNReal
        (parameterNormalizedShiftedBernoulliMatrix (min (rowBernoulliParameter n (d n)) 1) z
          (bernoulliPrincipalMinorSample
            (bernoulli_squeeze_lengths_le (n := n) hNonneg).2 x)))
      (gaussianShiftedSingularLimit z) :=
  bernoulli_principal_minor_effective_weak_convergence
    (fun n => bernoulliSqueezeMinorDimension n epsilon) d
    (fun n => (bernoulli_squeeze_lengths_le (n := n) hNonneg).2) hDegree hSparse
    (by linarith : 0 < 1 - epsilon) (bernoulli_squeeze_fixed_minor_ratio_tendsto hOne) z

theorem bernoulli_principal_minor_effective_rescaling {m n : ℕ} (hmn : m ≤ n)
    (d : ℕ) (z : ℂ) (x : BernoulliSquareSample n) :
    parameterNormalizedShiftedBernoulliMatrix (rowBernoulliParameter n d)
        (z / (Real.sqrt ((m : ℝ) / n) : ℂ)) (bernoulliPrincipalMinorSample hmn x) =
      (Real.sqrt ((m : ℝ) / n) : ℂ)⁻¹ •
        squarePrincipalMinor (normalizedShiftedBernoulliMatrix d z x) hmn := by
  have hSqrt : Real.sqrt (bernoulliEffectiveDegree m (rowBernoulliParameter n d)) =
      Real.sqrt ((m : ℝ) / n) * Real.sqrt (d : ℝ) := by
    rw [bernoulli_principal_minor_effective_degree,
      Real.sqrt_mul (div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))]
  rw [parameterNormalizedShiftedBernoulliMatrix, hSqrt, Complex.ofReal_mul,
    mul_inv_rev, bernoulli_shifted_principal_minor_matrix_eq]
  simp only [smul_sub, smul_smul, div_eq_mul_inv, mul_comm]

end CircularLaw
