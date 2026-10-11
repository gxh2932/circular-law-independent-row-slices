import CircularLaw.LLYSecondSourceKernelProbability
import CircularLaw.LLYSourceRadius

/-!
# Source budgets for the strict first prefix and gradual branches

The ceiling rank charges only its strict prefix. This gives the literal
floor-rank load budget even when the first rank is one and the degree
is close to half the dimension. All other rounded source ranks and the
actual spectral window are retained.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem lly_source_first_strict_prefix_floor_budget {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {C a : ℝ} (hC : 1920000 ≤ C) (hLower : C * Real.log (n : ℝ) ≤ d)
    (ha : 0 ≤ a) (haOne : a ≤ 1) :
    llySourceFirstRank n d a - 1 ≤ almostConstantRank n d := by
  have hEps := lly_source_epsilon_upper hn hd (by norm_num : (0 : ℝ) ≤ 1 / 200)
    (by nlinarith : (48 : ℝ) ≤ C * (1 / 200 : ℝ) ^ 2) hLower
  have hEpsNonneg : 0 ≤ llySourceEpsilon n d := Real.sqrt_nonneg _
  have hCoefficient : 16 * a * llySourceEpsilon n d ≤ 1 := by nlinarith
  have hPrev := lly_source_first_rank_prev_upper (n := n) hd ha
  have hPrevD := (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mp hPrev
  have hCoeffN := mul_le_mul_of_nonneg_right hCoefficient (Nat.cast_nonneg (α := ℝ) n)
  rw [almostConstantRank_eq_floor]
  apply Nat.le_floor
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mpr
  nlinarith

theorem lly_source_first_nonunit_rank_floor_budget {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {C a : ℝ} (hC : 1920000 ≤ C) (hLower : C * Real.log (n : ℝ) ≤ d)
    (ha : 0 < a) (haOne : a ≤ 1) (hNotOne : llySourceFirstRank n d a ≠ 1) :
    llySourceFirstRank n d a ≤ almostConstantRank n d := by
  have hRare := lly_source_first_rank_switching_density hn hd hC hLower ha haOne
  have hDensity := hRare.resolve_left hNotOne
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hProduct : (llySourceFirstRank n d a : ℝ) * d ≤ (n : ℝ) / 100 := by
    rw [← mul_div_assoc] at hDensity
    have h := (div_le_iff₀ hnR).mp hDensity
    linarith
  rw [almostConstantRank_eq_floor]
  apply Nat.le_floor
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem lly_source_first_nonunit_rank_expansion_budget {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) (hNotOne : llySourceFirstRank n d a ≠ 1) :
    (d : ℝ) * llySourceFirstRank n d a ≤ 2 * llySourceEpsilon n d * n := by
  have hFirst := lly_source_first_rank_pos hn hd ha
  have hRatio : 1 < a * llySourceEpsilon n d * n / d := by
    by_contra h
    have hCeil : llySourceFirstRank n d a ≤ 1 := Nat.ceil_le.mpr
      (by simpa only [Nat.cast_one] using le_of_not_gt h)
    omega
  have hCeil := Nat.ceil_lt_add_one (by
    have hEps := (lly_source_epsilon_pos hn hd).le
    positivity : 0 ≤ a * llySourceEpsilon n d * n / d)
  change (llySourceFirstRank n d a : ℝ) < a * llySourceEpsilon n d * n / d + 1 at hCeil
  have hUpper : (llySourceFirstRank n d a : ℝ) ≤ 2 * (a * llySourceEpsilon n d * n / d) := by
    linarith
  have hScaled := mul_le_mul_of_nonneg_right hUpper (by exact_mod_cast hd.le : (0 : ℝ) ≤ d)
  have hCancel : 2 * (a * llySourceEpsilon n d * n / d) * d =
      2 * a * llySourceEpsilon n d * n := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    field_simp
  rw [hCancel] at hScaled
  have hEpsNonneg : 0 ≤ llySourceEpsilon n d := Real.sqrt_nonneg _
  have hCoeff := mul_le_mul_of_nonneg_right haOne
    (by positivity : 0 ≤ 2 * llySourceEpsilon n d * (n : ℝ))
  nlinarith

theorem lly_source_second_gradual_scale_budget {n d : ℕ} (hd : 0 < d) {a : ℝ}
    (ha : 0 ≤ a) (haSmall : a ≤ 1 / 1000) :
    (llySourceSecondRank n d a : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000 := by
  have hRank := (le_div_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hd : (0 : ℝ) < d) _)).mp
    (lly_source_second_rank_upper (n := n) (d := d) ha)
  have hCoeff := mul_le_mul_of_nonneg_right haSmall (Nat.cast_nonneg (α := ℝ) n)
  linarith

theorem lly_source_third_gradual_scale_budget {n : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (haSmall : a ≤ 1 / 1000) :
    (llySourceThirdRank n a : ℝ) ≤ (n : ℝ) / 1000 := by
  apply (lly_source_third_rank_upper (n := n) ha).trans
  have h := mul_le_mul_of_nonneg_right haSmall (Nat.cast_nonneg (α := ℝ) n)
  linarith

theorem lly_source_stride_epsilon_budget {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) :
    llySourceEpsilon n d * llySourceStride n d ≤ 1 / 100 := by
  have hEps := lly_source_epsilon_pos hn hd
  have hFloor := Nat.floor_le (by positivity : 0 ≤ 1 / (100 * llySourceEpsilon n d))
  change (llySourceStride n d : ℝ) ≤ 1 / (100 * llySourceEpsilon n d) at hFloor
  have h := (le_div_iff₀ (by positivity : 0 < 100 * llySourceEpsilon n d)).mp hFloor
  nlinarith

theorem lly_source_epsilon_square_degree {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) :
    llySourceEpsilon n d ^ 2 * d = 48 * Real.log (n : ℝ) := by
  unfold llySourceEpsilon
  have hLog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hLog)
    (by exact_mod_cast hd.le : (0 : ℝ) ≤ d))]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp

theorem lly_source_stride_sqrt_log_budget {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) :
    (llySourceStride n d : ℝ) ≤ Real.sqrt ((d : ℝ) / Real.log (n : ℝ)) := by
  have hLog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hProduct : llySourceEpsilon n d ^ 2 * ((d : ℝ) / Real.log (n : ℝ)) = 48 := by
    have hEps := lly_source_epsilon_square_degree hn hd
    rw [← mul_div_assoc]
    apply (div_eq_iff hLog.ne').mpr
    exact hEps
  have hBound := lly_source_stride_epsilon_budget hn hd
  have hEpsNonneg : 0 ≤ llySourceEpsilon n d := Real.sqrt_nonneg _
  have hSquare := pow_le_pow_left₀ (mul_nonneg hEpsNonneg (Nat.cast_nonneg _)) hBound 2
  have hScaled := mul_le_mul_of_nonneg_right hSquare (div_nonneg hdR.le hLog.le)
  have hLeft : (llySourceEpsilon n d * llySourceStride n d) ^ 2 *
      ((d : ℝ) / Real.log (n : ℝ)) = 48 * (llySourceStride n d : ℝ) ^ 2 := by
    rw [mul_pow]
    calc
      _ = (llySourceStride n d : ℝ) ^ 2 *
          (llySourceEpsilon n d ^ 2 * ((d : ℝ) / Real.log (n : ℝ))) := by ring
      _ = _ := by rw [hProduct]; ring
  rw [hLeft] at hScaled
  apply (Real.le_sqrt (Nat.cast_nonneg _) (div_nonneg hdR.le hLog.le)).mpr
  nlinarith

theorem lly_source_stride_quarter_degree_budget {n d : ℕ} (hn : 2 ≤ n)
    (hd : 16 ≤ d) (hLog : 1 ≤ Real.log (n : ℝ)) :
    (llySourceStride n d : ℝ) ≤ (d : ℝ) / 4 := by
  have hdPos : 0 < d := by omega
  have hdR : (16 : ℝ) ≤ d := by exact_mod_cast hd
  have hRatio : (d : ℝ) / Real.log (n : ℝ) ≤ d :=
    div_le_self (Nat.cast_nonneg d) hLog
  apply (lly_source_stride_sqrt_log_budget hn hdPos).trans
  apply (Real.sqrt_le_sqrt hRatio).trans
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  nlinarith

theorem eventually_lly_spectral_window_gradual_budget :
    ∀ᶠ d : ℕ in atTop, 0 < d ∧ ∀ ζ : ℂ,
      ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) → ‖ζ‖ ≤ 4 * (d : ℝ) / 25 := by
  have hLog : ∀ᶠ d : ℕ in atTop, 1 ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 1, hLog,
    eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 4 / 25) 0 1 (by norm_num)] with d hd hLog hBudget
  have hdPos : 0 < d := by omega
  refine ⟨hdPos, ?_⟩
  intro ζ hShift
  have hLogLog : Real.log (Real.log (d : ℝ)) ≤ Real.log (d : ℝ) :=
    (Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log (d : ℝ))).trans (by linarith)
  simp only [zero_add, one_mul, Real.rpow_eq_pow, ← Real.sqrt_eq_rpow] at hBudget
  have hScaled := mul_le_mul_of_nonneg_left (hLogLog.trans hBudget) (Real.sqrt_nonneg d)
  have hRoot := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  apply hShift.trans
  nlinarith only [hScaled, hRoot]

end CircularLaw
