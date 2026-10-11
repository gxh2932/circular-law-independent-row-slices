import CircularLaw.SmallestSingularFailureTransfer

/-!
# Completing degree sequences before final regime assembly

Each regime's degrees are left unchanged on its own indices. Outside
that regime, a rounded logarithmic degree supplies a global admissible
sequence. This permits the checked whole-sequence regime deductions to
feed the literal two-filter assembly in the main theorem. The final
deduction still requires the actual minimum failure estimates.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

def completedLowerDegree (C : ℝ) (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  if n ∈ lowerRegime d then d n else ⌈C * Real.log n⌉₊

def completedUpperDegree (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  if n ∈ lowerRegime d then ⌈Real.rpow (Real.log n) (3 / 2)⌉₊ else d n

theorem eventually_log_lower_ceiling_in_band {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, (⌈C * Real.log n⌉₊ : ℝ) ≤ Real.rpow (Real.log n) (3 / 2) := by
  have hLog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hRoot := Real.tendsto_sqrt_atTop.comp hLog
  filter_upwards [hLog.eventually_ge_atTop 1, hRoot.eventually_ge_atTop (C + 1)] with n hn hRootN
  dsimp only [Function.comp_apply] at hn hRootN
  have hLogPos : 0 < Real.log (n : ℝ) := by linarith
  have hCeil := (Nat.ceil_lt_add_one (mul_nonneg hC.le hLogPos.le)).le
  have hPower : Real.rpow (Real.log n) (3 / 2) = Real.log n * Real.sqrt (Real.log n) := by
    simp only [Real.rpow_eq_pow]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hLogPos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hScale := mul_le_mul_of_nonneg_left hRootN hLogPos.le
  rw [hPower]
  nlinarith

theorem completed_lower_degree_in_band {C : ℝ} (hC : 0 < C) (d : ℕ → ℕ)
    (hLower : LogLowerBound C d) :
    ∀ᶠ n : ℕ in atTop, InLowerBand C (1 / 2) n (completedLowerDegree C d n) := by
  filter_upwards [hLower, eventually_log_lower_ceiling_in_band hC] with n hn hCeil
  unfold completedLowerDegree
  split_ifs with hReg
  · exact ⟨hn, by simpa only [InLowerBand, lowerRegime, Set.mem_setOf_eq,
      show (1 + 1 / 2 : ℝ) = 3 / 2 by norm_num] using hReg⟩
  · exact ⟨Nat.le_ceil _, by simpa only [show (1 + 1 / 2 : ℝ) = 3 / 2 by norm_num] using hCeil⟩

theorem completed_upper_degree_lower_bound (d : ℕ → ℕ) :
    ∀ n : ℕ, Real.rpow (Real.log n) (3 / 2) ≤ (completedUpperDegree d n : ℝ) := by
  intro n
  unfold completedUpperDegree
  split_ifs with hReg
  · exact Nat.le_ceil _
  · exact (lt_of_not_ge hReg).le

theorem completed_upper_degree_sparse (d : ℕ → ℕ) (hSparse : SparseDegrees d) :
    SparseDegrees (completedUpperDegree d) := by
  have hOne : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).inv_tendsto_atTop
  have hUpper := (hSparse.add (log_power_div_self_tendsto_zero (3 / 2))).add hOne
  simp only [add_zero] at hUpper
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hUpper
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hLog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hPower : 0 ≤ Real.rpow (Real.log n) (3 / 2) := Real.rpow_nonneg hLog _
  have hDegree : (completedUpperDegree d n : ℝ) ≤
      (d n : ℝ) + Real.rpow (Real.log n) (3 / 2) + 1 := by
    unfold completedUpperDegree
    split_ifs
    · have hCeil := (Nat.ceil_lt_add_one hPower).le
      have hd : (0 : ℝ) ≤ d n := Nat.cast_nonneg _
      linarith
    · linarith
  simpa only [add_div] using div_le_div_of_nonneg_right hDegree (Nat.cast_nonneg n)

theorem main_theorem_of_circular_regimes {C : ℝ} (hC : 0 < C)
    (hLow : ∀ d : ℕ → ℕ, (∀ᶠ n : ℕ in atTop, InLowerBand C (1 / 2) n (d n)) →
      CircularConvergence d)
    (hHigh : ∀ d : ℕ → ℕ, SparseDegrees d →
      (∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (3 / 2) ≤ (d n : ℝ)) → CircularConvergence d) :
    MainTheorem := by
  refine ⟨C, hC, ?_⟩
  intro d hLog hSparse
  have hLowLimit := hLow (completedLowerDegree C d) (completed_lower_degree_in_band hC d hLog)
  have hHighLimit := hHigh (completedUpperDegree d) (completed_upper_degree_sparse d hSparse)
    (Eventually.of_forall (completed_upper_degree_lower_bound d))
  apply convergence_of_regime_tail_bounds d
  · intro ε hε
    apply ((hLowLimit ε hε).mono_left inf_le_left).congr'
    apply eventually_inf_principal.mpr
    exact Eventually.of_forall (fun n hReg => by
      have hEq : completedLowerDegree C d n = d n := if_pos hReg
      unfold circularTail
      rw [hEq])
  · intro ε hε
    apply ((hHighLimit ε hε).mono_left inf_le_left).congr'
    apply eventually_inf_principal.mpr
    exact Eventually.of_forall (fun n hReg => by
      have hn : n ∉ lowerRegime d := hReg
      have hEq : completedUpperDegree d n = d n := if_neg hn
      unfold circularTail
      rw [hEq])

theorem main_theorem_of_uniform_minimum_failures :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ C : ℝ, Cstar ≤ C →
      (∀ d : ℕ → ℕ, (∀ᶠ n : ℕ in atTop, InLowerBand C (1 / 2) n (d n)) →
        ∀ z : ℂ, z ≠ 0 → ∃ CL : ℝ, 0 ≤ CL ∧
          Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
            (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
              (lowerHermitizationCutoff n CL))) atTop (𝓝 0)) →
      (∀ d : ℕ → ℕ, SparseDegrees d →
        (∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (3 / 2) ≤ (d n : ℝ)) →
        ∀ z : ℂ, z ≠ 0 → ∃ B : ℝ, 0 ≤ B ∧
          Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
            (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
              (polynomialHermitizationCutoff n B))) atTop (𝓝 0)) →
      MainTheorem := by
  obtain ⟨Cstar, hCstar, hLow⟩ := lower_band_circular_law_of_minimum_failure
  refine ⟨Cstar, hCstar, ?_⟩
  intro C hC hLowMinimum hHighMinimum
  apply main_theorem_of_circular_regimes (hCstar.trans_le hC)
  · intro d hBand
    exact hLow C hC (1 / 2) (by norm_num) (by norm_num) d hBand (hLowMinimum d hBand)
  · intro d hSparse hLower
    apply superlog_circular_law_of_minimum_failure d hSparse (ε := 1 / 2) (by norm_num)
    · simpa only [show (1 + 1 / 2 : ℝ) = 3 / 2 by norm_num] using hLower
    · exact hHighMinimum d hSparse hLower

end CircularLaw
