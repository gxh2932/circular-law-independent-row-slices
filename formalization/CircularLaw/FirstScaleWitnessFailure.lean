import CircularLaw.FirstSteepScale

/-!
# Uniform witness failure at the ceiling scale

This proves the `n1` branch of the manuscript's witness-scale failures
for the actual ceiling and full matrix law, and discharges its finite
conditions throughout the surrounding degree band.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem firstSteepScale_entropy {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    Real.log (Real.exp 1 * n / firstSteepScale n d) ≤
      1 + (3 / 2 : ℝ) * Real.log d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : (0 : ℝ) < Real.sqrt d := by positivity
  have hsR : (0 : ℝ) < firstSteepScale n d := by
    exact_mod_cast firstSteepScale_pos hn hd
  have hLower := (div_le_iff₀ (mul_pos hdR hRoot)).mp
    (firstSteepScale_lower (n := n) hd)
  have hRatio : Real.exp 1 * n / firstSteepScale n d ≤ Real.exp 1 * d * Real.sqrt d := by
    apply (div_le_iff₀ hsR).mpr
    have hScaled := mul_le_mul_of_nonneg_left hLower (Real.exp_pos 1).le
    nlinarith
  calc
    _ ≤ Real.log (Real.exp 1 * d * Real.sqrt d) := Real.log_le_log (by positivity) hRatio
    _ = _ := by
      rw [Real.log_mul (mul_pos (Real.exp_pos 1) hdR).ne' hRoot.ne',
        Real.log_mul (Real.exp_pos 1).ne' hdR.ne', Real.log_exp, Real.log_sqrt hdR.le]
      ring

theorem eventually_firstSteepScale_entropy :
    ∀ᶠ d : ℕ in atTop, 8 * (1 + (3 / 2 : ℝ) * Real.log d) ≤ binomialHalfRate * d := by
  have hLimit := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  simp only [Real.rpow_one] at hLimit
  have hSmall : ∀ᶠ d : ℕ in atTop, Real.log (d : ℝ) / d < binomialHalfRate / 24 :=
    hLimit.eventually (gt_mem_nhds (div_pos binomialHalfRate_pos (by norm_num)))
  have hLarge : ∀ᶠ d : ℕ in atTop, 16 / binomialHalfRate ≤ (d : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [hSmall, hLarge, eventually_ge_atTop 1] with d hSmall hLarge hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLog := (div_lt_iff₀ hdR).mp hSmall
  have hConstant := (div_le_iff₀ binomialHalfRate_pos).mp hLarge
  linarith

theorem firstSteepScale_witness_failure {n d : ℕ} (hdLarge : 40000 ≤ d)
    (hDimension : (d : ℝ) * Real.sqrt d ≤ n) (I : Finset (Fin n))
    (hRows : (n : ℝ) / 2 ≤ I.card) {cw : ℝ} (hcw : cw ≤ 1 / 4)
    (hEntropy : 8 * (1 + (3 / 2 : ℝ) * Real.log d) ≤ binomialHalfRate * d) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬UniformEqualBlockWitness cw (firstSteepScale n d) (fun i : I => rows i.val)) ≤
        Real.exp (-(binomialHalfRate / 4) * n / Real.sqrt d) := by
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : (200 : ℝ) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg (d : ℝ))).mp
    rw [Real.sq_sqrt hdR.le]
    exact_mod_cast hdLarge
  have hdnR : (d : ℝ) ≤ n := (by nlinarith : (d : ℝ) ≤ d * Real.sqrt d).trans hDimension
  have hdn : d ≤ n := by exact_mod_cast hdnR
  have hn : 2 ≤ n := by omega
  have hs := firstSteepScale_pos (by omega : 0 < n) hd
  have hSmall := firstSteepScale_small hd hDimension hRoot
  have hLog := firstSteepScale_entropy (by omega : 0 < n) hd
  have hScaleEntropy : 8 * Real.log (Real.exp 1 * n / firstSteepScale n d) ≤
      binomialHalfRate * d := by linarith
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  rw [uniformProbability_pi_restrict (α := fun _ : Fin n => RowSlice n d) I
    (fun retained => ¬UniformEqualBlockWitness cw (firstSteepScale n d) retained)]
  apply (uniform_equal_block_failure_absorbed hn hd hdn hs
    (by simpa only [Fintype.card_coe] using hRows) hSmall hcw hScaleEntropy).trans
  apply Real.exp_le_exp.mpr
  calc
    -(binomialHalfRate / 4) * (d : ℝ) * firstSteepScale n d =
        -(binomialHalfRate / 4) * ((d : ℝ) * firstSteepScale n d) := by ring
    _ ≤ -(binomialHalfRate / 4) * ((n : ℝ) / Real.sqrt d) :=
      mul_le_mul_of_nonpos_left (firstSteepScale_density_lower (n := n) hd)
        (by nlinarith [binomialHalfRate_pos])
    _ = _ := by ring

theorem eventually_firstSteepScale_dimension (power : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0 < d →
      (d : ℝ) ≤ Real.rpow (Real.log n) power → (d : ℝ) * Real.sqrt d ≤ n := by
  have hSmall : ∀ᶠ n : ℕ in atTop,
      Real.rpow (Real.log n) (2 * power) / n < 1 :=
    (log_power_div_self_tendsto_zero (2 * power)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hSmall, eventually_ge_atTop 2] with n hSmall hn
  intro d hd hUpper
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hLog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hSquare : (d : ℝ) ^ 2 ≤ Real.rpow (Real.log n) (2 * power) := by
    calc
      _ ≤ (Real.rpow (Real.log n) power) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg d) hUpper 2
      _ = _ := by
        have h := Real.rpow_mul hLog power (2 : ℝ)
        rw [Real.rpow_two] at h
        simpa only [mul_comm] using h.symm
  have hUpperN := (div_lt_iff₀ hnR).mp hSmall
  have hRootLe : Real.sqrt d ≤ (d : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg (d : ℝ)) (Nat.cast_nonneg d)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    nlinarith
  have hScaled := mul_le_mul_of_nonneg_left hRootLe (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  nlinarith

theorem eventually_first_scale_witness_failure_degree_band {C : ℝ} (hC : 0 < C)
    {d : ℕ → ℕ} (hLower : LogLowerBound C d) (power : ℝ)
    (hUpper : ∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ Real.rpow (Real.log n) power) :
    ∀ᶠ n : ℕ in atTop, ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card →
      ∀ cw : ℝ, cw ≤ 1 / 4 →
        uniformProbability (fun rows : RowSliceMatrix n (d n) =>
          ¬UniformEqualBlockWitness cw (firstSteepScale n (d n)) (fun i : I => rows i.val)) ≤
            Real.exp (-(binomialHalfRate / 4) * n / Real.sqrt (d n)) := by
  have hDegree := degree_tendsto_atTop_of_log_lower hC hLower
  have hLarge := hDegree.eventually (eventually_ge_atTop 40000)
  have hEntropy := hDegree.eventually eventually_firstSteepScale_entropy
  filter_upwards [hLarge, hEntropy, eventually_firstSteepScale_dimension power, hUpper]
    with n hLarge hEntropy hDimension hUpper
  intro I hRows cw hcw
  exact firstSteepScale_witness_failure hLarge (hDimension (d n) (by omega) hUpper)
    I hRows hcw hEntropy

end CircularLaw
