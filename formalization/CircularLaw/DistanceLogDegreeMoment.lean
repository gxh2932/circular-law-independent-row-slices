import CircularLaw.TruncatedGaussianMoment
import CircularLaw.RegularizedDistanceConcentration

/-!
# The slice-distance absolute first moment grows as sqrt(log(e*d))

The explicit cutoff absorbs the actual square-root-degree tail prefactor.
The same bound applies to the Bernoulli comparator. No first-moment or
tail-integration estimate is assumed.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal ENNReal

namespace CircularLaw

def rowDistanceTailConstant : ℝ := 4 * Real.exp 1 ^ 2 * (4 * Real.exp 16)

def rowLogDegree (d : ℕ) : ℝ := Real.log (Real.exp 1 * (d : ℝ))

theorem rowLogDegree_eq (d : ℕ) (hd : 0 < d) : rowLogDegree d = 1 + Real.log (d : ℝ) := by
  rw [rowLogDegree, Real.log_mul (Real.exp_pos _).ne' (by exact_mod_cast hd.ne'), Real.log_exp]

theorem rowLogDegree_ge_one {d : ℕ} (hd : 0 < d) : 1 ≤ rowLogDegree d := by
  rw [rowLogDegree_eq d hd]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith [Real.log_nonneg hdR]

theorem rowLogDegree_cutoff_absorption {d : ℕ} (hd : 0 < d) :
    (rowDistanceTailConstant * Real.sqrt (d : ℝ)) *
      Real.exp (-(1 / 1024) * (256 * Real.sqrt (rowLogDegree d)) ^ 2) ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  have hL : 0 ≤ rowLogDegree d := (by norm_num : (0 : ℝ) ≤ 1).trans (rowLogDegree_ge_one hd)
  have hR : -(1 / 1024) * (256 * Real.sqrt (rowLogDegree d)) ^ 2 = -64 * rowLogDegree d := by
    nlinarith [Real.sq_sqrt hL]
  have hA : rowDistanceTailConstant * Real.sqrt (d : ℝ) ≤ Real.exp (34 + Real.log (d : ℝ) / 2) := by
    have hSixteen : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
    have hRoot : Real.sqrt (d : ℝ) = Real.exp (Real.log (d : ℝ) / 2) := by
      rw [← Real.log_sqrt hdR.le, Real.exp_log (Real.sqrt_pos.mpr hdR)]
    have hConst : rowDistanceTailConstant = 16 * Real.exp 18 := by
      dsimp [rowDistanceTailConstant]
      have hExp : Real.exp 1 ^ 2 * Real.exp 16 = Real.exp 18 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        norm_num
      calc
        _ = 16 * (Real.exp 1 ^ 2 * Real.exp 16) := by ring
        _ = 16 * Real.exp 18 := by rw [hExp]
    rw [hConst, hRoot]
    calc
      _ ≤ Real.exp 16 * Real.exp 18 * Real.exp (Real.log (d : ℝ) / 2) := by
        gcongr
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  rw [hR]
  calc
    _ ≤ Real.exp (34 + Real.log (d : ℝ) / 2) * Real.exp (-64 * rowLogDegree d) :=
      mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ = Real.exp (34 + Real.log (d : ℝ) / 2 - 64 * rowLogDegree d) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by rw [rowLogDegree_eq d hd]; nlinarith)

theorem gaussian_row_logdegree_first_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (hfInt : Integrable f μ)
    {d : ℕ} (hd : 0 < d)
    (hTail : ∀ t : ℝ, 0 < t → μ.real {ω | t ≤ f ω} ≤
      (rowDistanceTailConstant * Real.sqrt (d : ℝ)) * Real.exp (-(1 / 1024) * t ^ 2)) :
    (∫ ω, f ω ∂μ) ≤ 288 * Real.sqrt (rowLogDegree d) := by
  have h := gaussian_tail_first_moment_cutoff μ hf hfInt
    (by dsimp [rowDistanceTailConstant]; positivity : 0 ≤ rowDistanceTailConstant * Real.sqrt (d : ℝ))
    (by norm_num : (0 : ℝ) < 1 / 1024)
    (by positivity : 0 ≤ 256 * Real.sqrt (rowLogDegree d))
    (rowLogDegree_cutoff_absorption hd) hTail
  have hSqrt : Real.sqrt (Real.pi / (1 / 1024)) ≤ 64 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [Real.pi_lt_four]⟩
  have hRoot : 1 ≤ Real.sqrt (rowLogDegree d) := Real.one_le_sqrt.mpr (rowLogDegree_ge_one hd)
  exact h.trans (by linarith)

theorem regularizedDistance_slice_absolute_moment {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsPositiveMatrixContraction P)
    (η : ℝ) (u : EuclideanSpace ℂ (Fin n)) :
    (∫ s, |regularizedDistance P η u (rowSliceEuclideanRow s) -
      regularizedDistanceMean P η u (rowBernoulliParameter n d)
        (rowBernoulliParameter_le_one (by omega) hdn)| ∂rowSliceLaw n d) ≤
      288 * Real.sqrt (rowLogDegree d) := by
  letI := rowSliceLaw_probability hdn
  apply gaussian_row_logdegree_first_moment (rowSliceLaw n d) (measurable_of_countable _) Integrable.of_finite hd
  intro t ht
  simpa only [rowDistanceTailConstant, mul_assoc] using regularizedDistance_slice_mean_tail hd hdn hP η u ht

theorem regularizedDistance_bernoulli_absolute_moment {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsPositiveMatrixContraction P)
    (η : ℝ) (u : EuclideanSpace ℂ (Fin n)) :
    (∫ x, |regularizedDistance P η u (bernoulliCubeVector x) -
      regularizedDistanceMean P η u (rowBernoulliParameter n d)
        (rowBernoulliParameter_le_one (by omega) hdn)|
      ∂bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d) (rowBernoulliParameter_le_one (by omega) hdn)) ≤
      288 * Real.sqrt (rowLogDegree d) := by
  apply gaussian_row_logdegree_first_moment _ (measurable_of_countable _) Integrable.of_finite hd
  intro t ht
  have h := regularizedDistance_bernoulli_mean_tail hP (rowBernoulliParameter n d)
    (rowBernoulliParameter_le_one (by omega) hdn) η u ht
  apply h.trans
  have hExp : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hRoot : 1 ≤ Real.sqrt (d : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have hFactor : 1 ≤ 4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ) := by nlinarith
  have hMul := mul_le_mul_of_nonneg_right hFactor
    (show 0 ≤ (4 * Real.exp 16) * Real.exp (-(1 / 1024) * t ^ 2) from by positivity)
  dsimp [rowDistanceTailConstant]
  nlinarith

theorem regularizedDistance_bernoulli_sqrt_degree_tail {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsPositiveMatrixContraction P)
    (η : ℝ) (u : EuclideanSpace ℂ (Fin n)) {t : ℝ} (ht : 0 < t) :
    (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d) (rowBernoulliParameter_le_one (by omega) hdn)).real
      {x | t ≤ |regularizedDistance P η u (bernoulliCubeVector x) -
        regularizedDistanceMean P η u (rowBernoulliParameter n d) (rowBernoulliParameter_le_one (by omega) hdn)|} ≤
      (rowDistanceTailConstant * Real.sqrt (d : ℝ)) * Real.exp (-(1 / 1024) * t ^ 2) := by
  have h := regularizedDistance_bernoulli_mean_tail hP (rowBernoulliParameter n d)
    (rowBernoulliParameter_le_one (by omega) hdn) η u ht
  apply h.trans
  have hExp : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hRoot : 1 ≤ Real.sqrt (d : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have hFactor : 1 ≤ 4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ) := by nlinarith
  have hMul := mul_le_mul_of_nonneg_right hFactor
    (show 0 ≤ (4 * Real.exp 16) * Real.exp (-(1 / 1024) * t ^ 2) from by positivity)
  dsimp [rowDistanceTailConstant]
  nlinarith

end CircularLaw
