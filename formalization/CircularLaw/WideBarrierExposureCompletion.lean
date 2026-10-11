import CircularLaw.WideBarrierExposureDrift
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Terminal completion with the wider integer barrier

The exponential-moment estimate gives terminal failure at most
16*q^(1/8), including q=0. The constant also covers large q without
imposing an artificial smallness assumption on the insertion error.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem wide_barrier_exposure_terminal_probability_bound
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m0) (H : ℕ → Ω → ℕ) (T : ℕ)
    (hMeas : ∀ s, s ≤ T → Measurable[F s] (H s))
    (hInitial : ∀ x, (H 0 x : ℝ) ≤ (T : ℝ) / 2)
    (hGrowth : ∀ s, s < T → ∀ x, H (s + 1) x ≤ H s x + 2)
    {q : ℝ} (hq : 0 ≤ q)
    (hDrift : ∀ s, s < T → ∀ᵐ x ∂μ,
      2 * ((T - s) / 8) ≤ H s x →
      (μ[({y | H s y - 1 < H (s + 1) y}).indicator (fun _ => (1 : ℝ)) | F s]) x ≤ q) :
    μ.real {x | 0 < H T x} ≤ 16 * q ^ (1 / 8 : ℝ) := by
  by_cases hZero : q = 0
  · have hBounds (k : ℕ) : μ.real {x | 0 < H T x} ≤
        2 * Real.exp (-2 * (Real.log 4 + k)) := by
      apply wide_barrier_exposure_terminal_exponential_bound μ F H T hMeas hInitial hGrowth
        (le_add_of_nonneg_right (Nat.cast_nonneg k))
      intro s hs
      filter_upwards [hDrift s hs] with x hx hActive
      exact (hx hActive).trans (by rw [hZero]; exact (Real.exp_pos _).le)
    have hLimit : Tendsto (fun k : ℕ => 2 * Real.exp (-2 * (Real.log 4 + k))) atTop (𝓝 0) := by
      have hArg : Tendsto (fun k : ℕ => -2 * (Real.log 4 + k)) atTop atBot :=
        (tendsto_atTop_add_const_left atTop (Real.log 4) (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop_of_neg
          (by norm_num : (-2 : ℝ) < 0)
      simpa only [mul_zero] using (Real.tendsto_exp_atBot.comp hArg).const_mul 2
    have hLe : μ.real {x | 0 < H T x} ≤ 0 := ge_of_tendsto hLimit (Eventually.of_forall hBounds)
    simpa only [hZero, Real.zero_rpow (by norm_num : (1 / 8 : ℝ) ≠ 0), mul_zero] using hLe
  have hqPos : 0 < q := lt_of_le_of_ne hq (Ne.symm hZero)
  by_cases hSmall : q < Real.exp (-16 * Real.log 4)
  · let a := -Real.log q / 16
    have hLog : Real.log q < -16 * Real.log 4 := by
      simpa only [Real.log_exp] using Real.log_lt_log hqPos hSmall
    have ha : Real.log 4 ≤ a := by dsimp [a]; linarith
    have hEq : Real.exp (-16 * a) = q := by
      rw [show -16 * a = Real.log q by dsimp [a]; ring, Real.exp_log hqPos]
    have hBound := wide_barrier_exposure_terminal_exponential_bound μ F H T hMeas hInitial
      hGrowth ha (by simpa only [hEq] using hDrift)
    have hPower : Real.exp (-2 * a) = q ^ (1 / 8 : ℝ) := by
      rw [Real.rpow_def_of_pos hqPos]
      congr 1
      dsimp [a]
      ring
    rw [hPower] at hBound
    have hNonneg : 0 ≤ q ^ (1 / 8 : ℝ) := Real.rpow_nonneg hq _
    linarith
  · have hLarge : Real.exp (-16 * Real.log 4) ≤ q := le_of_not_gt hSmall
    have hCompare := Real.rpow_le_rpow (Real.exp_pos (-16 * Real.log 4)).le hLarge
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hBase : Real.exp (-16 * Real.log 4) ^ (1 / 8 : ℝ) = 1 / 16 := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [show -16 * Real.log 4 * (1 / 8 : ℝ) = -(Real.log (4 * 4)) by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
        ring]
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [hBase] at hCompare
    exact (measureReal_le_one (μ := μ)).trans (by linarith)

end CircularLaw
