import CircularLaw.BernoulliPrincipalMinorSmallValues
import CircularLaw.BernoulliSecondMoment

/-!
# Uniform second-moment bounds for the actual ambient-normalized minor

The minor keeps the ambient normalization and entry probability. Its
expected empirical singular second moment is at most 2 + 2 norm(z)^2,
uniformly over every principal minor. Markov gives the corresponding
actual ambient-law tail bound, with no weak or logarithmic assumption.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem bernoulli_second_moment_parameter_integral_bound {m d : ℕ}
    (hm : 0 < m) (hd : 0 < d) (p : ℝ≥0) (hp : p ≤ 1) (z : ℂ) :
    (∫ x, bernoulliSingularSecondMoment d z x ∂bernoulliSquareMatrixLaw m p hp) ≤
      2 * m * (p : ℝ) / d + 2 * ‖z‖ ^ 2 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    _ ≤ ∫ x, (2 / ((m : ℝ) * d)) * bernoulliSquareCount x + 2 * ‖z‖ ^ 2
        ∂bernoulliSquareMatrixLaw m p hp :=
      integral_mono .of_finite .of_finite (bernoulliSingularSecondMoment_bound hm z)
    _ = _ := by
      rw [integral_add .of_finite .of_finite, integral_const_mul,
        bernoulliSquareCount_integral, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      field_simp

def bernoulliPrincipalMinorSecondMoment {m n : ℕ} (hmn : m ≤ n) (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) : ℝ :=
  empiricalNonnegativeMean
    (squareSingularValuesNNReal (squarePrincipalMinor (normalizedShiftedBernoulliMatrix d z x) hmn))
    (fun t => (t : ℝ) ^ 2)

theorem bernoulli_principal_minor_second_moment_eq_sample {m n : ℕ} (hmn : m ≤ n)
    (d : ℕ) (z : ℂ) (x : BernoulliSquareSample n) :
    bernoulliPrincipalMinorSecondMoment hmn d z x =
      bernoulliSingularSecondMoment d z (bernoulliPrincipalMinorSample hmn x) := by
  have hMatrix : squarePrincipalMinor (normalizedShiftedBernoulliMatrix d z x) hmn =
      normalizedShiftedBernoulliMatrix d z (bernoulliPrincipalMinorSample hmn x) :=
    bernoulli_shifted_principal_minor_matrix_eq hmn d z x
  rw [bernoulliPrincipalMinorSecondMoment, hMatrix]
  exact (empiricalNonnegativeMeasure_integral _ _).symm

theorem bernoulli_principal_minor_second_moment_nonneg {m n : ℕ} (hmn : m ≤ n)
    (d : ℕ) (z : ℂ) (x : BernoulliSquareSample n) :
    0 ≤ bernoulliPrincipalMinorSecondMoment hmn d z x := by
  rw [bernoulli_principal_minor_second_moment_eq_sample]
  exact bernoulliSingularSecondMoment_nonneg _ _ _

theorem bernoulli_principal_minor_second_moment_integral_bound {m n d : ℕ}
    (hmn : m ≤ n) (hm : 0 < m) (hd : 0 < d) (hdn : d ≤ n) (z : ℂ) :
    (∫ x, bernoulliPrincipalMinorSecondMoment hmn d z x ∂sparseBernoulliMatrixLaw n d) ≤
      2 + 2 * ‖z‖ ^ 2 := by
  have hn : 0 < n := hm.trans_le hmn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hMap : (∫ y, bernoulliSingularSecondMoment d z y
      ∂(sparseBernoulliMatrixLaw n d).map (bernoulliPrincipalMinorSample hmn)) =
      ∫ x, bernoulliSingularSecondMoment d z (bernoulliPrincipalMinorSample hmn x)
        ∂sparseBernoulliMatrixLaw n d :=
    integral_map_of_stronglyMeasurable (measurable_of_countable _)
      (measurable_of_countable _).stronglyMeasurable
  rw [bernoulli_sparse_principal_minor_sample_law] at hMap
  simp only [min_eq_left (rowBernoulliParameter_le_one hn hdn)] at hMap
  calc
    _ = ∫ y, bernoulliSingularSecondMoment d z y
        ∂bernoulliSquareMatrixLaw m (rowBernoulliParameter n d)
          (rowBernoulliParameter_le_one hn hdn) := by
      simp only [bernoulli_principal_minor_second_moment_eq_sample]
      exact hMap.symm
    _ ≤ 2 * m * (rowBernoulliParameter n d : ℝ) / d + 2 * ‖z‖ ^ 2 :=
      bernoulli_second_moment_parameter_integral_bound hm hd _ _ z
    _ = 2 * ((m : ℝ) / n) + 2 * ‖z‖ ^ 2 := by
      rw [rowBernoulliParameter_coe]
      field_simp
    _ ≤ _ := by
      have hRatio : (m : ℝ) / n ≤ 1 :=
        (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr (by exact_mod_cast hmn)
      linarith

theorem bernoulli_principal_minor_second_moment_tail_bound {m n d : ℕ}
    (hmn : m ≤ n) (hm : 0 < m) (hd : 0 < d) (hdn : d ≤ n) (z : ℂ)
    {M : ℝ} (hM : 0 < M) :
    (sparseBernoulliMatrixLaw n d).real
      {x | M < |bernoulliPrincipalMinorSecondMoment hmn d z x|} ≤
        (2 + 2 * ‖z‖ ^ 2) / M := by
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (bernoulli_principal_minor_second_moment_nonneg hmn d z))
    (show Integrable (bernoulliPrincipalMinorSecondMoment hmn d z)
      (sparseBernoulliMatrixLaw n d) from .of_finite) M
  have hSubset : {x : BernoulliSquareSample n | M < |bernoulliPrincipalMinorSecondMoment hmn d z x|} ⊆
      {x | M ≤ bernoulliPrincipalMinorSecondMoment hmn d z x} := by
    intro x hx
    change M < |bernoulliPrincipalMinorSecondMoment hmn d z x| at hx
    simpa only [abs_of_nonneg (bernoulli_principal_minor_second_moment_nonneg hmn d z x)] using hx.le
  apply (le_div_iff₀ hM).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (μ := sparseBernoulliMatrixLaw n d) hSubset)
    hM.le).trans (hMark.trans (bernoulli_principal_minor_second_moment_integral_bound hmn hm hd hdn z))

theorem bernoulli_minor_second_moment_bounded_in_probability (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {epsilon : ℝ} (hNonneg : 0 ≤ epsilon) (hOne : epsilon < 1) :
    VaryingBoundedInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => empiricalNonnegativeMean (bernoulliMinorSingularArray d z epsilon hNonneg n x)
        (fun t => (t : ℝ) ^ 2)) := by
  intro delta hDelta
  let C : ℝ := 2 + 2 * ‖z‖ ^ 2
  let M : ℝ := C / delta + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  have hQ := minor_dimension_tendsto_of_positive_ratio
    (fun n => bernoulliSqueezeMinorDimension n epsilon) (by linarith : 0 < 1 - epsilon)
    (bernoulli_squeeze_fixed_minor_ratio_tendsto hOne)
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse,
    hQ.eventually_gt_atTop 0] with n hn hqn
  apply (bernoulli_principal_minor_second_moment_tail_bound
    (bernoulli_squeeze_lengths_le hNonneg).2 hqn hn.1 hn.2 z hM).trans_lt
  change C / M < delta
  apply (div_lt_iff₀ hM).mpr
  dsimp [M]
  rw [mul_add, mul_div_cancel₀ C hDelta.ne', mul_one]
  linarith

end CircularLaw
