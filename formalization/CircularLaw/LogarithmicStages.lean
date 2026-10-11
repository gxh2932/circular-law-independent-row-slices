import CircularLaw.SlowDiagonal
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit logarithmic cutoff stages

At stage `k`, the cutoff is the integer `k+K` and the removed fraction is
`4*C*exp(-(k+K))`. A single offset makes every fraction at most one. The
fraction decreases to zero and its product with the cutoff also tends to
zero, as required by the retained-prefix error estimate.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def logarithmicStageCutoff (K k : ℕ) : ℕ := k + K

def logarithmicStageFraction (C : ℝ) (K k : ℕ) : ℝ :=
  4 * C * Real.exp (-(logarithmicStageCutoff K k : ℝ))

theorem exists_logarithmic_stage_offset (C : ℝ) :
    ∃ K : ℕ, Real.log (4 * C) ≤ (K : ℝ) := exists_nat_ge _

theorem logarithmicStageCutoff_tendsto (K : ℕ) :
    Tendsto (logarithmicStageCutoff K) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  exact hk.trans (Nat.le_add_right _ _)

theorem logarithmicStageFraction_pos {C : ℝ} (hC : 0 < C) (K k : ℕ) :
    0 < logarithmicStageFraction C K k := by
  exact mul_pos (mul_pos (by norm_num) hC) (Real.exp_pos _)

theorem logarithmicStageFraction_le_one {C : ℝ} (hC : 0 < C) {K : ℕ}
    (hK : Real.log (4 * C) ≤ (K : ℝ)) (k : ℕ) :
    logarithmicStageFraction C K k ≤ 1 := by
  have hKC : (K : ℝ) ≤ logarithmicStageCutoff K k := by
    exact_mod_cast (Nat.le_add_left K k)
  calc
    _ = Real.exp (Real.log (4 * C) - logarithmicStageCutoff K k) := by
      rw [Real.exp_sub, Real.exp_log (by positivity : (0 : ℝ) < 4 * C),
        logarithmicStageFraction, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem logarithmicStageFraction_antitone {C : ℝ} (hC : 0 ≤ C) (K : ℕ) :
    Antitone (logarithmicStageFraction C K) := by
  intro k l hkl
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg (by norm_num) hC)
  have h : (logarithmicStageCutoff K k : ℝ) ≤ logarithmicStageCutoff K l := by
    exact_mod_cast (Nat.add_le_add_right hkl K)
  linarith

theorem logarithmicStageFraction_threshold {C : ℝ} (hC : 0 < C) (K k : ℕ) :
    logarithmicStageFraction C K k / (4 * C) =
      Real.exp (-(logarithmicStageCutoff K k : ℝ)) := by
  exact mul_div_cancel_left₀ _ (by positivity : (4 * C : ℝ) ≠ 0)

theorem logarithmicStageFraction_tendsto (C : ℝ) (K : ℕ) :
    Tendsto (logarithmicStageFraction C K) atTop (𝓝 0) := by
  have hReal : Tendsto (fun k => (logarithmicStageCutoff K k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (logarithmicStageCutoff_tendsto K)
  simpa only [logarithmicStageFraction, mul_zero] using
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hReal)).const_mul (4 * C)

theorem logarithmicStageFraction_mul_cutoff_tendsto (C : ℝ) (K : ℕ) :
    Tendsto (fun k => logarithmicStageFraction C K k * logarithmicStageCutoff K k)
      atTop (𝓝 0) := by
  have hReal : Tendsto (fun k => (logarithmicStageCutoff K k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (logarithmicStageCutoff_tendsto K)
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hReal).const_mul (4 * C)
  have hEq : (fun k => logarithmicStageFraction C K k * logarithmicStageCutoff K k) =
      fun k => (4 * C) * ((logarithmicStageCutoff K k : ℝ) *
        Real.exp (-(logarithmicStageCutoff K k : ℝ))) := by
    funext k
    unfold logarithmicStageFraction
    ring
  rw [hEq]
  simpa only [Function.comp_apply, pow_one, mul_zero] using h

def diagonalAccuracy (k : ℕ) : ℝ := 1 / ((k + 1 : ℕ) : ℝ)

theorem diagonalAccuracy_pos (k : ℕ) : 0 < diagonalAccuracy k := by
  exact div_pos zero_lt_one (by exact_mod_cast Nat.succ_pos k)

theorem diagonalAccuracy_tendsto : Tendsto diagonalAccuracy atTop (𝓝 0) := by
  exact (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (logarithmicStageCutoff_tendsto 1)

end CircularLaw
