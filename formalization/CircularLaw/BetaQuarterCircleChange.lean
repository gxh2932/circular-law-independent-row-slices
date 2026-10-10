import CircularLaw.GaussianZeroBetaProperties
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Change from beta coordinates to quarter-circle coordinates

The square map s -> s^2/4 maps (0,2) bijectively onto (0,1). Its
Jacobian turns the beta(1/2,3/2) density into sqrt(4-s^2)/pi.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace CircularLaw

def betaQuarterCircleSquare (s : ℝ) : ℝ := s ^ 2 / 4

theorem beta_quarter_circle_square_deriv (s : ℝ) :
    HasDerivAt betaQuarterCircleSquare (s / 2) s := by
  unfold betaQuarterCircleSquare
  convert ((hasDerivAt_id s).pow 2).div_const 4 using 1
  simp only [id_eq]
  ring

theorem beta_quarter_circle_square_inj :
    InjOn betaQuarterCircleSquare (Ioo (0 : ℝ) 2) := by
  intro s hs t ht hEq
  dsimp only [betaQuarterCircleSquare] at hEq
  nlinarith [hs.1, ht.1]

theorem beta_quarter_circle_square_image :
    betaQuarterCircleSquare '' Ioo (0 : ℝ) 2 = Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    dsimp only [betaQuarterCircleSquare]
    constructor <;> nlinarith [hs.1, hs.2]
  · intro hx
    rcases hx with ⟨hx0, hx1⟩
    refine ⟨Real.sqrt (4 * x), ⟨Real.sqrt_pos.2 (by linarith), ?_⟩, ?_⟩
    · have hSquare := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 * x)
      have hNonneg := Real.sqrt_nonneg (4 * x)
      nlinarith
    · dsimp only [betaQuarterCircleSquare]
      rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 * x)]
      ring

theorem beta_quarter_circle_sqrt_square {s : ℝ} (hs : 0 < s) :
    Real.sqrt (betaQuarterCircleSquare s) = s / 2 := by
  rw [betaQuarterCircleSquare, Real.sqrt_div (sq_nonneg s), Real.sqrt_sq hs.le]
  norm_num

theorem beta_quarter_circle_complement_sqrt (s : ℝ) :
    Real.sqrt (1 - betaQuarterCircleSquare s) = Real.sqrt (4 - s ^ 2) / 2 := by
  rw [show 1 - betaQuarterCircleSquare s = (4 - s ^ 2) / 4 by
    dsimp only [betaQuarterCircleSquare]; ring]
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem beta_quarter_circle_jacobian_density {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    |s / 2| * betaPDFReal (1 / 2) (3 / 2) (betaQuarterCircleSquare s) =
      Real.sqrt (4 - s ^ 2) / Real.pi := by
  have hx : 0 < betaQuarterCircleSquare s ∧ betaQuarterCircleSquare s < 1 := by
    dsimp only [betaQuarterCircleSquare]
    constructor <;> nlinarith [hs.1, hs.2]
  rw [beta_half_density_real, if_pos hx, abs_of_pos (div_pos hs.1 (by norm_num)),
    Real.rpow_neg hx.1.le, ← Real.sqrt_eq_rpow,
    beta_quarter_circle_sqrt_square hs.1, ← Real.sqrt_eq_rpow,
    beta_quarter_circle_complement_sqrt]
  field_simp [hs.1.ne']

theorem beta_quarter_circle_sqrt_map {s : ℝ} (hs : 0 ≤ s) :
    nonnegativeRealSquareRoot (4 * betaQuarterCircleSquare s) = Real.toNNReal s := by
  apply NNReal.eq
  change Real.sqrt (4 * betaQuarterCircleSquare s) = (Real.toNNReal s : ℝ)
  rw [betaQuarterCircleSquare,
    show 4 * (s ^ 2 / 4) = s ^ 2 by ring, Real.sqrt_sq hs,
    Real.coe_toNNReal s hs]

theorem beta_quarter_circle_change_integral (f : ℝ≥0 → ℝ) :
    (∫ x in Ioo (0 : ℝ) 1,
      betaPDFReal (1 / 2) (3 / 2) x * f (nonnegativeRealSquareRoot (4 * x))) =
        ∫ s in Ioo (0 : ℝ) 2,
          (Real.sqrt (4 - s ^ 2) / Real.pi) * f (Real.toNNReal s) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun s _ => (beta_quarter_circle_square_deriv s).hasDerivWithinAt)
    beta_quarter_circle_square_inj
    (fun x => betaPDFReal (1 / 2) (3 / 2) x * f (nonnegativeRealSquareRoot (4 * x)))
  rw [beta_quarter_circle_square_image] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [smul_eq_mul, ← mul_assoc, beta_quarter_circle_jacobian_density hs,
    beta_quarter_circle_sqrt_map hs.1.le]

end CircularLaw
