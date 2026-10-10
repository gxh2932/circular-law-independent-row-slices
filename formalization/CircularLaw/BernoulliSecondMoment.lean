import CircularLaw.BernoulliSquareMatrixLaw
import CircularLaw.VaryingProbabilityConvergence
import CircularLaw.Statement

/-!
# The Bernoulli hermitization second-moment bound

For the actual independent-entry matrix `B/sqrt(d) - z I`, the empirical
singular-value second moment has expectation at most `2 + 2*|z|^2`.
Markov's inequality proves the manuscript's `O_P(1)` assertion on varying
sample spaces. No spectral or logarithmic convergence is assumed here.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix NNReal Topology

namespace CircularLaw

def bernoulliSingularSecondMoment {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) : ℝ :=
  ∫ t, (t : ℝ) ^ 2 ∂bernoulliSingularMeasure d z x

theorem bernoulliSingularSecondMoment_eq {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) :
    bernoulliSingularSecondMoment d z x =
      squareMatrixEnergy (normalizedShiftedBernoulliMatrix d z x) / n :=
  squareSingularMeasure_second_moment _

theorem bernoulliSingularSecondMoment_nonneg {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) : 0 ≤ bernoulliSingularSecondMoment d z x :=
  squareSingularMeasure_second_moment_nonneg _

theorem bernoulliSingularSecondMoment_bound {n d : ℕ} (hn : 0 < n) (z : ℂ)
    (x : BernoulliSquareSample n) :
    bernoulliSingularSecondMoment d z x ≤
      (2 / ((n : ℝ) * d)) * bernoulliSquareCount x + 2 * ‖z‖ ^ 2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [bernoulliSingularSecondMoment_eq]
  have hBound := squareMatrixEnergy_shift_le
    ((Real.sqrt (d : ℝ) : ℂ)⁻¹ • bernoulliSquareMatrix x) z
  rw [squareMatrixEnergy_sqrt_normalization, bernoulliSquareMatrix_energy] at hBound
  calc
    _ ≤ (2 * (bernoulliSquareCount x / d) + 2 * n * ‖z‖ ^ 2) / n :=
      div_le_div_of_nonneg_right hBound (Nat.cast_nonneg n)
    _ = _ := by
      by_cases hd : d = 0
      · simp only [hd, Nat.cast_zero, div_zero, mul_zero, zero_mul, zero_add]
        field_simp
      · field_simp

theorem bernoulliSingularSecondMoment_integral_bound {n d : ℕ} (hd : 0 < d)
    (hdn : d ≤ n) (z : ℂ) :
    (∫ x, bernoulliSingularSecondMoment d z x ∂sparseBernoulliMatrixLaw n d) ≤
      2 + 2 * ‖z‖ ^ 2 := by
  have hn : 0 < n := lt_of_lt_of_le hd hdn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hInt (f : BernoulliSquareSample n → ℝ) : Integrable f (sparseBernoulliMatrixLaw n d) :=
    Integrable.of_finite
  calc
    _ ≤ ∫ x, (2 / ((n : ℝ) * d)) * bernoulliSquareCount x + 2 * ‖z‖ ^ 2
        ∂sparseBernoulliMatrixLaw n d :=
      integral_mono (hInt _) (hInt _) (bernoulliSingularSecondMoment_bound hn z)
    _ = 2 + 2 * ‖z‖ ^ 2 := by
      rw [integral_add (hInt _) (hInt _), integral_const_mul,
        sparseBernoulliSquareCount_integral hn hdn, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      field_simp

theorem bernoulliSingularSecondMoment_tail_bound {n d : ℕ} (hd : 0 < d)
    (hdn : d ≤ n) (z : ℂ) {M : ℝ} (hM : 0 < M) :
    (sparseBernoulliMatrixLaw n d).real
        {x | M < |bernoulliSingularSecondMoment d z x|} ≤ (2 + 2 * ‖z‖ ^ 2) / M := by
  let μ := sparseBernoulliMatrixLaw n d
  have hInt : Integrable (bernoulliSingularSecondMoment (n := n) d z) μ :=
    Integrable.of_finite
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (bernoulliSingularSecondMoment_nonneg d z)) hInt M
  have hSubset : {x : BernoulliSquareSample n | M < |bernoulliSingularSecondMoment d z x|} ⊆
      {x | M ≤ bernoulliSingularSecondMoment d z x} := by
    intro x hx
    change M < |bernoulliSingularSecondMoment d z x| at hx
    change M ≤ bernoulliSingularSecondMoment d z x
    simpa only [abs_of_nonneg (bernoulliSingularSecondMoment_nonneg d z x)] using hx.le
  apply (le_div_iff₀ hM).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hSubset) hM.le).trans
    (hMark.trans (bernoulliSingularSecondMoment_integral_bound hd hdn z))

theorem eventually_valid_bernoulli_degrees {d : ℕ → ℕ}
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d) :
    ∀ᶠ n in atTop, 0 < d n ∧ d n ≤ n := by
  have hPos := hd.eventually (eventually_gt_atTop 0)
  have hRatio := hsparse.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hPos, hRatio, eventually_ge_atTop 1] with n hdn hr hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdnR := (div_lt_one hnR).mp hr
  exact ⟨hdn, le_of_lt (by exact_mod_cast hdnR)⟩

theorem bernoulli_second_moment_bounded_in_probability (d : ℕ → ℕ) (z : ℂ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d) :
    VaryingBoundedInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n => bernoulliSingularSecondMoment (d n) z) := by
  intro δ hδ
  let C : ℝ := 2 + 2 * ‖z‖ ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  let M : ℝ := C / δ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  filter_upwards [eventually_valid_bernoulli_degrees hd hsparse] with n hn
  apply (bernoulliSingularSecondMoment_tail_bound hn.1 hn.2 z hM).trans_lt
  change C / M < δ
  apply (div_lt_iff₀ hM).mpr
  dsimp [M]
  rw [mul_add, mul_div_cancel₀ C hδ.ne', mul_one]
  linarith

end CircularLaw
