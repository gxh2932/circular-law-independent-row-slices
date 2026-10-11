import CircularLaw.HighHeightTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A stronger upper cutoff for high-height coordinates

The cutoff `H/(d*sqrt(s))` improves the elementary `H/d` threshold.
Coordinates of height at least `H` below this cutoff have mass at most
`512*(2-log_2(s)/2)*d^(-1/3)*n`. The coefficient tends to zero with
the degree, independently of the height scale and the creation orders.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem sqrt_height_cutoff_log {H s D : ℝ} (hH : 0 < H) (hs : 0 < s) (hD : 0 < D) :
    Real.logb 2 (H / (D * Real.sqrt s)) =
      Real.logb 2 H - Real.logb 2 D - Real.logb 2 s / 2 := by
  rw [Real.logb_div hH.ne' (mul_pos hD (Real.sqrt_pos.mpr hs)).ne',
    Real.logb_mul hD.ne' (Real.sqrt_pos.mpr hs).ne']
  simp only [Real.logb, Real.log_sqrt hs.le]
  ring

theorem sqrt_height_cutoff_bounds {H s : ℝ} {d : ℕ}
    (hH : 0 < H) (hs : 0 < s) (hsOne : s ≤ 1) (hd : 0 < d)
    (hDegree : 1 ≤ Real.sqrt s * (d : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ)) :
    H / d ≤ H / ((d : ℝ) * Real.sqrt s) ∧
      H / ((d : ℝ) * Real.sqrt s) ≤ H * Real.rpow (d : ℝ) (-1 / 3 : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hSqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  constructor
  · exact div_le_div_of_nonneg_left hH.le (mul_pos hdR hSqrt)
      (by have h := Real.sqrt_le_one.mpr hsOne; nlinarith)
  · apply (div_le_iff₀ (mul_pos hdR hSqrt)).mpr
    have h := mul_le_mul_of_nonneg_left hDegree hH.le
    nlinarith

theorem profile_sqrt_height_cutoff_mass {n : ℕ} (hn : 0 < n) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (P : RowProfile (Fin n) ι)
    (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) {H s : ℝ} (hH : 0 < H) (hs : 0 < s) (hsOne : s ≤ 1)
    (hDegree : 1 ≤ Real.sqrt s * (d : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ)) :
    profileSelectedMass P (profileHighLowParts P d H (H / ((d : ℝ) * Real.sqrt s))) ≤
      512 * (2 - Real.logb 2 s / 2) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) * n := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨hLow, hHigh⟩ := sqrt_height_cutoff_bounds hH hs hsOne hd hDegree
  have hMass := profile_high_low_mass_bound hn P order hGeometry hd hH
    (div_pos hH (mul_pos hdR (Real.sqrt_pos.mpr hs))) hLow hHigh
  have hLog : Real.logb 2 (H / ((d : ℝ) * Real.sqrt s)) - Real.logb 2 (H / d) + 2 =
      2 - Real.logb 2 s / 2 := by
    rw [sqrt_height_cutoff_log hH hs hdR, Real.logb_div hH.ne' hdR.ne']
    ring
  rw [hLog] at hMass
  exact hMass

theorem eventually_sqrt_height_cutoff_degree {s : ℝ} (hs : 0 < s) :
    ∀ᶠ d : ℕ in atTop,
      1 ≤ Real.sqrt s * (d : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) := by
  have hLimit := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  filter_upwards [hLimit.eventually_ge_atTop (1 / Real.sqrt s), eventually_ge_atTop 1] with d hd hdOne
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdOne
  change 1 / Real.sqrt s ≤ Real.rpow (d : ℝ) (2 / 3 : ℝ) at hd
  have hPower : (d : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) = Real.rpow (d : ℝ) (2 / 3 : ℝ) := by
    have hOne : Real.rpow (d : ℝ) (1 : ℝ) = (d : ℝ) := Real.rpow_one _
    calc
      _ = Real.rpow (d : ℝ) (1 : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) := by rw [hOne]
      _ = Real.rpow (d : ℝ) (1 + (-1 / 3 : ℝ)) := (Real.rpow_add hdR _ _).symm
      _ = _ := by congr 1; norm_num
  rw [mul_assoc, hPower]
  have h := (div_le_iff₀ (Real.sqrt_pos.mpr hs)).mp hd
  simpa only [mul_comm] using h

theorem eventually_sqrt_height_cutoff_budget {s : ℝ} (hs : 0 < s) :
    ∀ᶠ d : ℕ in atTop,
      512 * (2 - Real.logb 2 s / 2) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ s / 4 := by
  have hLimit := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).const_mul
      (512 * (2 - Real.logb 2 s / 2))
  have hLimitZero : Tendsto
      (fun d : ℕ => 512 * (2 - Real.logb 2 s / 2) * Real.rpow (d : ℝ) (-1 / 3 : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, neg_div, Real.rpow_eq_pow] using hLimit
  have hEvent := hLimitZero.eventually (gt_mem_nhds (show (0 : ℝ) < s / 4 by positivity))
  filter_upwards [hEvent] with d hd
  exact hd.le

end CircularLaw
