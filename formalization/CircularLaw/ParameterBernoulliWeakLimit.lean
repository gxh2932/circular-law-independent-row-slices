import CircularLaw.ParameterBernoulliShiftedMoments
import CircularLaw.CompactTargetMomentConvergence
import CircularLaw.InterlacedEmpiricalWeakTransfer
import CircularLaw.GaussianShiftedLimitProperties

/-!
# The actual weak singular law for arbitrary sparse Bernoulli parameters

The dimension may be any growing sequence, the probability tends to zero,
and the real effective degree tends to infinity. Moment concentration
proves the centered law; the actual constant-entry mean has rank at most
one and transfers bounded continuous tests to the uncentered law.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def parameterBernoulliCenteredSquaredSingularValues {n : ℕ} (p : ℝ≥0) (z : ℂ)
    (x : BernoulliSquareSample n) (j : Fin n) : ℝ :=
  (squareSingularValuesNNReal (parameterNormalizedCenteredBernoulliMatrix p x - z • 1) j : ℝ) ^ 2

theorem parameter_bernoulli_squared_singular_moment_eq {n : ℕ}
    (p : ℝ≥0) (z : ℂ) (m : ℕ) (x : BernoulliSquareSample n) :
    finiteMean (fun j => parameterBernoulliCenteredSquaredSingularValues p z x j ^ m) =
      parameterBernoulliCenteredShiftedSingularMoment p z m x := by
  simp only [parameterBernoulliCenteredShiftedSingularMoment, squareSingularMeasure,
    empiricalNonnegativeMeasure_integral, empiricalNonnegativeMean,
    parameterBernoulliCenteredSquaredSingularValues, pow_mul]

theorem parameter_bernoulli_squared_singular_moments_converge
    (q : ℕ → ℕ) (p : ℕ → ℝ≥0) (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (hSparse : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0)) (z : ℂ) (m : ℕ) :
    VaryingConvergesInProbability (fun n => bernoulliSquareMatrixLaw (q n) (p n) (hp n))
      (fun n x => finiteMean (fun j => parameterBernoulliCenteredSquaredSingularValues (p n) z x j ^ m))
      (gaussianShiftedSquaredMomentLimit z m) := by
  simp only [parameter_bernoulli_squared_singular_moment_eq, gaussianShiftedSquaredMomentLimit]
  exact parameter_bernoulli_centered_shifted_moment_converges q p hp hQ hDegree hSparse z m

theorem parameter_bernoulli_centered_weak_convergence (q : ℕ → ℕ) (p : ℕ → ℝ≥0)
    (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (hSparse : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0)) (z : ℂ) :
    EmpiricalWeakConvergenceInProbability (fun n => bernoulliSquareMatrixLaw (q n) (p n) (hp n))
      (fun n x => squareSingularValuesNNReal (parameterNormalizedCenteredBernoulliMatrix (p n) x - z • 1))
      (gaussianShiftedSingularLimit z) := by
  intro f hf hBound
  let F : ℝ → ℝ := fun r => f (nonnegativeRealSquareRoot r)
  have hF : Continuous F := hf.comp continuous_nonnegative_real_square_root
  have hFBound : ∃ M : ℝ, ∀ r, |F r| ≤ M := by
    obtain ⟨M, hM⟩ := hBound
    exact ⟨M, fun r => hM (nonnegativeRealSquareRoot r)⟩
  have hLimit := varying_probability_bounded_continuous_of_indexed_compact_target_moments
    (fun n => bernoulliSquareMatrixLaw (q n) (p n) (hp n)) q (hQ.eventually_gt_atTop 0)
    (fun n => parameterBernoulliCenteredSquaredSingularValues (p n) z)
    (gaussianShiftedSquaredMomentLimit z) ((128 + ‖z‖) ^ 2) (sq_nonneg _)
    (fun _ _ _ => sq_nonneg _)
    (parameter_bernoulli_squared_singular_moments_converge q p hp hQ hDegree hSparse z)
    (gaussianShiftedSquaredLimit z) (gaussian_shifted_squared_limit_moments z) F hF hFBound
  have hIntegral : (∫ t, f t ∂gaussianShiftedSingularLimit z) =
      ∫ t, F (t : ℝ)
        ∂(gaussianShiftedSquaredLimit z : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2))) :=
    integral_map_of_stronglyMeasurable
      (μ := (gaussianShiftedSquaredLimit z : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2))))
      (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable
      hf.measurable.stronglyMeasurable
  rw [← hIntegral] at hLimit
  simpa only [F, parameterBernoulliCenteredSquaredSingularValues, nonnegative_real_square_root_sq,
    empiricalNonnegativeMean] using hLimit

def parameterNormalizedShiftedBernoulliMatrix {n : ℕ} (p : ℝ≥0) (z : ℂ)
    (x : BernoulliSquareSample n) : Matrix (Fin n) (Fin n) ℂ :=
  (Real.sqrt (bernoulliEffectiveDegree n p) : ℂ)⁻¹ • bernoulliSquareMatrix x - z • 1

theorem parameter_bernoulli_centered_decomposition {n : ℕ}
    (p : ℝ≥0) (z : ℂ) (x : BernoulliSquareSample n) :
    parameterNormalizedShiftedBernoulliMatrix p z x =
      parameterNormalizedCenteredBernoulliMatrix p x - z • 1 +
        constantEntryMatrix n ((Real.sqrt (bernoulliEffectiveDegree n p) : ℂ)⁻¹ * p) := by
  have hMean : (Real.sqrt (bernoulliEffectiveDegree n p) : ℂ)⁻¹ • bernoulliSquareMeanMatrix p =
      constantEntryMatrix n ((Real.sqrt (bernoulliEffectiveDegree n p) : ℂ)⁻¹ * p) := by
    ext i j
    rfl
  rw [parameterNormalizedCenteredBernoulliMatrix, bernoulli_centered_square_matrix_eq,
    smul_sub, ← hMean]
  unfold parameterNormalizedShiftedBernoulliMatrix
  abel

theorem parameter_bernoulli_weak_convergence (q : ℕ → ℕ) (p : ℕ → ℝ≥0)
    (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (hSparse : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0)) (z : ℂ) :
    EmpiricalWeakConvergenceInProbability (fun n => bernoulliSquareMatrixLaw (q n) (p n) (hp n))
      (fun n x => squareSingularValuesNNReal (parameterNormalizedShiftedBernoulliMatrix (p n) z x))
      (gaussianShiftedSingularLimit z) := by
  apply indexed_empirical_weak_convergence_of_one_index_interlacing
    (fun n => bernoulliSquareMatrixLaw (q n) (p n) (hp n)) q hQ _
    (fun n x => squareSingularValuesNNReal (parameterNormalizedCenteredBernoulliMatrix (p n) x - z • 1))
    (gaussianShiftedSingularLimit z) (128 + ‖z‖) (by positivity)
    (gaussian_shifted_limit_support z)
  · intro n x
    exact orderedSquareSingularValues_antitone _
  · intro n x
    exact orderedSquareSingularValues_antitone _
  · intro n x i j h
    simp only [parameter_bernoulli_centered_decomposition, squareSingularValuesNNReal, NNReal.coe_mk]
    exact (constant_entry_perturbation_singular_values_interlace _ _ i j h).1
  · intro n x i j h
    simp only [parameter_bernoulli_centered_decomposition, squareSingularValuesNNReal, NNReal.coe_mk]
    exact (constant_entry_perturbation_singular_values_interlace _ _ i j h).2
  · exact parameter_bernoulli_centered_weak_convergence q p hp hQ hDegree hSparse z

end CircularLaw
