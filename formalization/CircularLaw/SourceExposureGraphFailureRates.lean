import CircularLaw.SourceExposureUniqueEvents
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The simultaneous source graph event has probability tending to one

The large-set schedule error is bounded by a polynomial times an
exponential in sqrt(N). The small-set schedule error vanishes as the
effective degree grows. This proves the graph probability input under
the actual varying Bernoulli law.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology NNReal

namespace CircularLaw

def sourceExposureGraphFailureError (N : ℕ) (d : ℝ) : ℝ :=
  2 * ((N : ℝ)⁻¹) ^ 3 + 786444 * Real.exp (-d / 16) +
    4 * ((N + 1 : ℕ) : ℝ) * N * Real.exp (-(N : ℝ) / (64 * Real.log d))

theorem large_source_schedule_error_le_sqrt_exponential {n d : ℝ}
    (hd : 1 < d) (hdn : d ≤ n) :
    4 * (n + 1) * n * Real.exp (-n / (64 * Real.log d)) ≤
      8 * n ^ 2 * Real.exp (-Real.sqrt n / 128) := by
  have hn : 0 < n := by linarith
  have hnOne : 1 ≤ n := by linarith
  have hLogD : 0 < Real.log d := Real.log_pos hd
  have hLog := log_nat_power_le_sqrt hnOne (by norm_num : (0 : ℕ) < 1)
  norm_num only [pow_one, Nat.cast_one, mul_one] at hLog
  have hLogUpper : Real.log d ≤ 2 * Real.sqrt n :=
    (Real.log_le_log (by linarith : 0 < d) hdn).trans hLog
  have hSquare := Real.sq_sqrt hn.le
  have hDiv : Real.sqrt n / 128 ≤ n / (64 * Real.log d) := by
    apply (le_div_iff₀ (by positivity : 0 < 64 * Real.log d)).mpr
    have h := mul_le_mul_of_nonneg_left hLogUpper (Real.sqrt_nonneg n)
    nlinarith
  have hExp : Real.exp (-n / (64 * Real.log d)) ≤ Real.exp (-Real.sqrt n / 128) := by
    apply Real.exp_le_exp.mpr
    simp only [neg_div]
    linarith
  exact mul_le_mul (by nlinarith : 4 * (n + 1) * n ≤ 8 * n ^ 2) hExp
    (Real.exp_pos _).le (by positivity)

theorem natural_square_sqrt_exponential_tendsto :
    Tendsto (fun n : ℕ => 8 * (n : ℝ) ^ 2 * Real.exp (-Real.sqrt n / 128)) atTop (𝓝 0) := by
  have hRoot : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / 128) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hRoot).const_mul
    (8 * (128 : ℝ) ^ 4)
  simp only [mul_zero] at h
  apply h.congr
  intro n
  change 8 * (128 : ℝ) ^ 4 * ((Real.sqrt (n : ℝ) / 128) ^ 4 *
    Real.exp (-(Real.sqrt (n : ℝ) / 128))) = 8 * (n : ℝ) ^ 2 * Real.exp (-Real.sqrt n / 128)
  have hSquare := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hFourth : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by nlinarith [sq_nonneg (Real.sqrt (n : ℝ) ^ 2 - n)]
  rw [div_pow, hFourth]
  simp only [neg_div]
  field_simp

theorem large_source_schedule_error_tendsto (d : ℕ → ℝ)
    (hLower : ∀ᶠ n in atTop, 1 < d n) (hUpper : ∀ᶠ n in atTop, d n ≤ n) :
    Tendsto (fun n : ℕ => 4 * ((n + 1 : ℕ) : ℝ) * n *
      Real.exp (-(n : ℝ) / (64 * Real.log (d n)))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds natural_square_sqrt_exponential_tendsto
    (Eventually.of_forall (fun n => by positivity))
  filter_upwards [hLower, hUpper] with n hn hnUpper
  simpa only [Nat.cast_add, Nat.cast_one] using large_source_schedule_error_le_sqrt_exponential hn hnUpper

theorem source_exposure_graph_failure_error_tendsto (d : ℕ → ℝ)
    (hD : Tendsto d atTop atTop) (hUpper : ∀ᶠ n in atTop, d n ≤ n) :
    Tendsto (fun n => sourceExposureGraphFailureError n (d n)) atTop (𝓝 0) := by
  have hInverse : Tendsto (fun n : ℕ => 2 * ((n : ℝ)⁻¹) ^ 3) atTop (𝓝 0) := by
    have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    simpa only [zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero] using
      (hInv.pow 3).const_mul 2
  have hNeg : Tendsto (fun n => (-1 / 16 : ℝ) * d n) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by norm_num : (-1 / 16 : ℝ) < 0)).mpr hD
  have hExp : Tendsto (fun n => 786444 * Real.exp (-d n / 16)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp hNeg).const_mul 786444
    simp only [mul_zero] at h
    apply h.congr
    intro n
    change 786444 * Real.exp ((-1 / 16 : ℝ) * d n) = 786444 * Real.exp (-d n / 16)
    congr 1
    congr 1
    ring
  have hLarge := large_source_schedule_error_tendsto d (hD.eventually (eventually_gt_atTop 1)) hUpper
  simpa only [sourceExposureGraphFailureError, add_zero] using (hInverse.add hExp).add hLarge

theorem bernoulli_bidirectional_source_exposure_graph_failure_tendsto
    (p : ℕ → ℝ≥0) (hp : ∀ n, p n ≤ 1) (hHalf : ∀ᶠ n in atTop, (p n : ℝ) ≤ 1 / 2)
    (hD : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop atTop)
    {β : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) :
    Tendsto (fun n => (bernoulliSquareMatrixLaw n (p n) (hp n)).real {x |
      ¬ BidirectionalSourceExposureGraphBudget (bernoulliSquareMatrix x) β ((n : ℝ) * p n)})
      atTop (𝓝 0) := by
  have hUpper : ∀ n : ℕ, (n : ℝ) * p n ≤ n := by
    intro n
    have hpReal : (p n : ℝ) ≤ 1 := by exact_mod_cast hp n
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpReal (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hError := source_exposure_graph_failure_error_tendsto (fun n : ℕ => (n : ℝ) * p n)
    hD (Eventually.of_forall hUpper)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hError
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_gt_atTop 0, hHalf, hD.eventually (eventually_ge_atTop (Real.exp 1024))]
    with n hn hnHalf hnD
  exact bernoulli_bidirectional_source_exposure_graph_failure hn (p n) (hp n) hnHalf rfl hnD hβ hβOne

end CircularLaw
