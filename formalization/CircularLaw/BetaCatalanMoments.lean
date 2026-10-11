import CircularLaw.BetaMeasureMoments
import CircularLaw.GaussianZeroCatalanMoments

/-!
# The scaled beta law has Catalan moments

The beta constant's gamma recurrence gives the same one-step ratio as
the Catalan numbers. Thus four times the actual beta(1/2,3/2) variable
has every natural moment equal to the corresponding Catalan number.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory

namespace CircularLaw

theorem beta_constant_step {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    beta (α + 1) β = (α / (α + β)) * beta α β := by
  simp only [beta]
  rw [Real.Gamma_add_one hα.ne', show α + 1 + β = (α + β) + 1 by ring,
    Real.Gamma_add_one (add_pos hα hβ).ne']
  field_simp

theorem catalan_successor_mul (k : ℕ) :
    (k + 2) * catalan (k + 1) = (4 * k + 2) * catalan k := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [← succ_mul_catalan_eq_centralBinom (k + 1),
    ← succ_mul_catalan_eq_centralBinom k] at h
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 1)
  nlinarith [h]

def betaCatalanMoment (k : ℕ) : ℝ :=
  4 ^ k * (beta (1 / 2 + k) (3 / 2) / beta (1 / 2) (3 / 2))

theorem beta_catalan_moment_zero : betaCatalanMoment 0 = 1 := by
  simp only [betaCatalanMoment, Nat.cast_zero, add_zero, pow_zero, one_mul]
  exact div_self (ne_of_gt (beta_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 3 / 2)))

theorem beta_catalan_moment_succ (k : ℕ) :
    betaCatalanMoment (k + 1) =
      ((4 * k + 2) / (k + 2)) * betaCatalanMoment k := by
  simp only [betaCatalanMoment, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [show (1 : ℝ) / 2 + ((k : ℝ) + 1) = (1 / 2 + k) + 1 by ring,
    beta_constant_step (by positivity : (0 : ℝ) < 1 / 2 + k) (by norm_num : (0 : ℝ) < 3 / 2)]
  rw [show (1 : ℝ) / 2 + k + 3 / 2 = k + 2 by ring]
  field_simp
  ring

theorem beta_catalan_moment_eq (k : ℕ) : betaCatalanMoment k = (catalan k : ℝ) := by
  induction k with
  | zero => simpa only [catalan_zero, Nat.cast_one] using beta_catalan_moment_zero
  | succ k ih =>
    rw [beta_catalan_moment_succ, ih]
    have h : ((k : ℝ) + 2) * (catalan (k + 1) : ℝ) =
        (4 * (k : ℝ) + 2) * (catalan k : ℝ) := by
      exact_mod_cast catalan_successor_mul k
    have hDen : (k : ℝ) + 2 ≠ 0 := by positivity
    calc
      _ = ((4 * (k : ℝ) + 2) * (catalan k : ℝ)) / ((k : ℝ) + 2) := by ring
      _ = _ := (div_eq_iff hDen).mpr (by nlinarith [h])

theorem beta_scaled_half_power_integral (k : ℕ) :
    (∫ x, ((4 : ℝ) * x) ^ k ∂betaMeasure (1 / 2) (3 / 2)) = (catalan k : ℝ) := by
  simp only [mul_pow]
  rw [integral_const_mul, beta_measure_power_integral
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 3 / 2)]
  exact beta_catalan_moment_eq k

theorem beta_half_three_halves_constant : beta (1 / 2 : ℝ) (3 / 2) = Real.pi / 2 := by
  have hThree : Real.Gamma (3 / 2) = (1 / 2) * Real.Gamma (1 / 2) := by
    convert Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0) using 1; norm_num
  have hTwo : Real.Gamma 2 = 1 := by
    convert Real.Gamma_add_one (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num [Real.Gamma_one]
  rw [beta, show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num, hThree, hTwo, div_one,
    Real.Gamma_one_half_eq]
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

end CircularLaw
