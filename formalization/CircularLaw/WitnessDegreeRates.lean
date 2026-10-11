import CircularLaw.UniformWitnessEntropy
import CircularLaw.ProfileRange

/-!
# Degree thresholds for witness entropy and shifts

At the literal floor scale `m0`, the number of set pairs costs only
`O(s*log(d))`; this is absorbed into the row-witness exponent as the
degree grows. The source shift window also fits the deterministic bound.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_witness_degree_entropy :
    ∀ᶠ d : ℕ in atTop, 0 < d ∧
      8 * Real.log (400 * Real.exp 1 * d) ≤ binomialHalfRate * d := by
  have hLimit := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  simp only [Real.rpow_one] at hLimit
  have hSmall : ∀ᶠ d : ℕ in atTop,
      Real.log (d : ℝ) / d < binomialHalfRate / 16 :=
    hLimit.eventually (gt_mem_nhds (div_pos binomialHalfRate_pos (by norm_num)))
  have hLarge : ∀ᶠ d : ℕ in atTop,
      16 * Real.log (400 * Real.exp 1) / binomialHalfRate ≤ (d : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [hSmall, hLarge, eventually_ge_atTop 1] with d hSmall hLarge hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLog := (div_lt_iff₀ hdR).mp hSmall
  have hConstant := (div_le_iff₀ binomialHalfRate_pos).mp hLarge
  refine ⟨hd, ?_⟩
  rw [Real.log_mul (by positivity : (400 * Real.exp 1 : ℝ) ≠ 0) hdR.ne']
  linarith

theorem equalBlockScale_witness_failure {n d : ℕ} (hd : 0 < d) (hn : 400 * d ≤ n)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) {cw : ℝ} (hcw : cw ≤ 1 / 4)
    (hEntropy : 8 * Real.log (400 * Real.exp 1 * d) ≤ binomialHalfRate * d) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬UniformEqualBlockWitness cw (equalBlockScale n d) (fun i : I => rows i.val)) ≤
        Real.exp (-(binomialHalfRate / 1600) * n) := by
  have hnTwo : 2 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdn : d ≤ n := by omega
  have hs := equalBlockScale_pos hd hn
  have hsR : (0 : ℝ) < equalBlockScale n d := by exact_mod_cast hs
  have hDensity := equalBlockScale_density_lower hd hn
  have hSmall : 100 * d * equalBlockScale n d ≤ n := by
    have h := equalBlockScale_density_upper (n := n) (d := d)
    have hReal : (100 : ℝ) * d * equalBlockScale n d ≤ n := by linarith
    exact_mod_cast hReal
  have hRatio : Real.exp 1 * n / equalBlockScale n d ≤ 400 * Real.exp 1 * d := by
    apply (div_le_iff₀ hsR).mpr
    have hScaled := mul_le_mul_of_nonneg_left hDensity (Real.exp_pos 1).le
    nlinarith
  have hLog : Real.log (Real.exp 1 * n / equalBlockScale n d) ≤
      Real.log (400 * Real.exp 1 * d) :=
    Real.log_le_log (by positivity) hRatio
  have hScaleEntropy : 8 * Real.log (Real.exp 1 * n / equalBlockScale n d) ≤
      binomialHalfRate * d := by linarith
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  rw [uniformProbability_pi_restrict (α := fun _ : Fin n => RowSlice n d) I
    (fun retained => ¬UniformEqualBlockWitness cw (equalBlockScale n d) retained)]
  apply (uniform_equal_block_failure_absorbed hnTwo hd hdn hs
    (by simpa only [Fintype.card_coe] using hRows) hSmall hcw hScaleEntropy).trans
  apply Real.exp_le_exp.mpr
  have hScaled := mul_le_mul_of_nonneg_left hDensity binomialHalfRate_pos.le
  nlinarith

theorem eventually_equalBlockScale_witness_failure :
    ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, 400 * d ≤ n →
      ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card → ∀ cw : ℝ, cw ≤ 1 / 4 →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ¬UniformEqualBlockWitness cw (equalBlockScale n d) (fun i : I => rows i.val)) ≤
            Real.exp (-(binomialHalfRate / 1600) * n) := by
  filter_upwards [eventually_witness_degree_entropy] with d hd
  intro n hn I hRows cw hcw
  exact equalBlockScale_witness_failure hd.1 hn I hRows hcw hd.2

theorem eventually_witness_shift_window :
    ∀ᶠ d : ℕ in atTop, Real.sqrt d * Real.log d ≤ (d : ℝ) / 20 := by
  have hLimit := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  simp only [← Real.sqrt_eq_rpow] at hLimit
  have hSmall : ∀ᶠ d : ℕ in atTop, Real.log d / Real.sqrt d < (1 / 20 : ℝ) :=
    hLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))
  filter_upwards [hSmall, eventually_ge_atTop 1] with d hSmall hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot := Real.sqrt_pos.mpr hdR
  have hLog := (div_lt_iff₀ hRoot).mp hSmall
  have hScaled := mul_le_mul_of_nonneg_left hLog.le hRoot.le
  nlinarith [Real.sq_sqrt hdR.le]

theorem eventually_fixed_shift_witness_window (Z₀ : ℝ) :
    ∀ᶠ d : ℕ in atTop, ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d → ‖ζ‖ ≤ (d : ℝ) / 20 := by
  have hLog : ∀ᶠ d : ℕ in atTop, Z₀ ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop Z₀
  filter_upwards [eventually_witness_shift_window, hLog] with d hWindow hLog
  intro ζ hζ
  have hScaled := mul_le_mul_of_nonneg_right hLog (Real.sqrt_nonneg (d : ℝ))
  nlinarith

theorem eventually_floor_witness_failure_degree_band {C : ℝ} (hC : 0 < C)
    {d : ℕ → ℕ} (hLower : LogLowerBound C d) (power : ℝ)
    (hUpper : ∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ Real.rpow (Real.log n) power) :
    ∀ᶠ n : ℕ in atTop, ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card →
      ∀ cw : ℝ, cw ≤ 1 / 4 →
        uniformProbability (fun rows : RowSliceMatrix n (d n) =>
          ¬UniformEqualBlockWitness cw (equalBlockScale n (d n)) (fun i : I => rows i.val)) ≤
            Real.exp (-(binomialHalfRate / 1600) * n) := by
  have hDegree := (degree_tendsto_atTop_of_log_lower hC hLower).eventually
    eventually_witness_degree_entropy
  filter_upwards [hDegree, eventually_equal_block_dimension power, hUpper]
    with n hDegree hDimension hUpper
  intro I hRows cw hcw
  exact equalBlockScale_witness_failure hDegree.1 (hDimension.2 (d n) hUpper)
    I hRows hcw hDegree.2

end CircularLaw
