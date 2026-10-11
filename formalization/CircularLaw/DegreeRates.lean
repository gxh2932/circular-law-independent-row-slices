import CircularLaw.Conditioning
import CircularLaw.Assembly
import CircularLaw.Statement

/-!
# Degree rates and subexponential conditioning

The common lower regime `d ≤ (log n)^(3/2)` makes both `d/n` and `d^2/n`
vanish, even if this regime occurs only on a subsequence. The exact
conditioning estimate then has logarithmic cost `o(n)` for `K ≤ n`.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace CircularLaw

theorem log_power_div_self_tendsto_zero (a : ℝ) :
    Tendsto (fun n : ℕ => Real.rpow (Real.log n) a / n) atTop (𝓝 0) := by
  simpa only [Real.rpow_one] using
    ((isLittleO_log_rpow_rpow_atTop a (s := 1) zero_lt_one).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

theorem degree_div_self_lowerRegime (d : ℕ → ℕ) :
    Tendsto (fun n : ℕ => (d n : ℝ) / n) (atTop ⊓ 𝓟 (lowerRegime d)) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity))
    (g := fun n : ℕ => Real.rpow (Real.log n) (3 / 2 : ℝ) / n)
  · apply eventually_inf_principal.mpr
    exact Eventually.of_forall fun n hreg => div_le_div_of_nonneg_right hreg (by positivity)
  · exact (log_power_div_self_tendsto_zero (3 / 2)).mono_left inf_le_left

theorem degree_square_div_self_lowerRegime (d : ℕ → ℕ) :
    Tendsto (fun n : ℕ => (d n : ℝ) ^ 2 / n) (atTop ⊓ 𝓟 (lowerRegime d)) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity))
    (g := fun n : ℕ => Real.rpow (Real.log n) (3 : ℝ) / n)
  · apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop 1] with n hn hreg
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hsquare : (Real.rpow (Real.log n) (3 / 2 : ℝ)) ^ 2 =
        Real.rpow (Real.log n) (3 : ℝ) := by
      have h := Real.rpow_mul hlog (3 / 2 : ℝ) (2 : ℝ)
      norm_num only at h
      simpa only [Real.rpow_two] using h.symm
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← hsquare]
    exact pow_le_pow_left₀ (by positivity) hreg 2
  · exact (log_power_div_self_tendsto_zero 3).mono_left inf_le_left

theorem eventually_twice_degree_le_lowerRegime (d : ℕ → ℕ) :
    ∀ᶠ n : ℕ in atTop ⊓ 𝓟 (lowerRegime d), 0 < n ∧ 2 * d n ≤ n := by
  have hsmall : ∀ᶠ n : ℕ in atTop ⊓ 𝓟 (lowerRegime d), (d n : ℝ) / n < 1 / 2 :=
    (degree_div_self_lowerRegime d).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hnpos : ∀ᶠ n : ℕ in atTop ⊓ 𝓟 (lowerRegime d), 1 ≤ n :=
    (eventually_ge_atTop 1).filter_mono inf_le_left
  filter_upwards [hsmall, hnpos] with n hn hn1
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdreal : (2 : ℝ) * d n ≤ n := by
    have h := (div_lt_iff₀ hnreal).mp hn
    linarith
  exact ⟨by omega, by exact_mod_cast hdreal⟩

theorem conditioning_log_ratio_nonneg {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    0 ≤ Real.log ((n : ℝ) ^ d / (n.descFactorial d : ℝ)) := by
  rw [conditioning_log_ratio hn hdn]
  apply Finset.sum_nonneg
  intro j hj
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hjn : (j : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (Finset.mem_range.mp hj) hdn
  have hx : 0 < 1 - (j : ℝ) / n := sub_pos.mpr ((div_lt_one hn').mpr hjn)
  exact neg_nonneg.mpr (Real.log_nonpos hx.le (by
    have : 0 ≤ (j : ℝ) / n := by positivity
    linarith))

/-- The Section 3 conditioning cost is subexponential in the lower degree
regime for every row-count sequence `K(n) ≤ n`. -/
theorem conditioning_cost_div_self_lowerRegime (d K : ℕ → ℕ)
    (hK : ∀ᶠ n : ℕ in atTop, K n ≤ n) :
    Tendsto (fun n : ℕ => (K n : ℝ) *
      Real.log ((n : ℝ) ^ d n / (n.descFactorial (d n) : ℝ)) / n)
      (atTop ⊓ 𝓟 (lowerRegime d)) (𝓝 0) := by
  have hvalid := eventually_twice_degree_le_lowerRegime d
  apply squeeze_zero'
    (hvalid.mono fun n hn => div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (conditioning_log_ratio_nonneg hn.1 (by omega)))
      (Nat.cast_nonneg _))
    (g := fun n : ℕ => 2 * ((d n : ℝ) ^ 2 / n))
  · filter_upwards [hvalid, hK.filter_mono inf_le_left] with n hn hKn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn.1
    calc
      _ ≤ (2 * K n * (d n : ℝ) ^ 2 / n) / n :=
        div_le_div_of_nonneg_right (conditioning_log_cost hn.1 hn.2) hnreal.le
      _ ≤ 2 * ((d n : ℝ) ^ 2 / n) := by
        have hkreal : (K n : ℝ) ≤ n := by exact_mod_cast hKn
        have hmul := mul_le_mul_of_nonneg_right hkreal (sq_nonneg (d n : ℝ))
        apply (div_le_iff₀ hnreal).mpr
        rw [show 2 * ((d n : ℝ) ^ 2 / n) * n = 2 * (d n : ℝ) ^ 2 by
          field_simp]
        apply (div_le_iff₀ hnreal).mpr
        nlinarith
  · simpa only [mul_zero] using (degree_square_div_self_lowerRegime d).const_mul 2

/-- The paper's dyadic weight-range bound fits the proved max-weight lemma
once the logarithmic lower constant is at least 96. -/
theorem weight_range_le_degree {n d : ℕ} (hlogn : 2 ≤ Real.log (n : ℝ))
    (hd : 0 < d) (hdn : d ≤ n) (hlower : 96 * Real.log (n : ℝ) ≤ d) :
    Real.logb 2 n + (3 / 2 : ℝ) * Real.logb 2 d + 2 ≤ (d : ℝ) / 12 := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hln : 0 ≤ Real.log (n : ℝ) := by linarith
  have hld : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hldn : Real.log (d : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdn)
  have hnb : Real.logb 2 n ≤ 2 * Real.log (n : ℝ) := by
    rw [Real.logb]
    have h := div_le_div_of_nonneg_left hln (by norm_num : (0 : ℝ) < 1 / 2) h2
    linarith
  have hdb : Real.logb 2 d ≤ 2 * Real.log (d : ℝ) := by
    rw [Real.logb]
    have h := div_le_div_of_nonneg_left hld (by norm_num : (0 : ℝ) < 1 / 2) h2
    linarith
  linarith

theorem eventually_weight_range_le_degree {C : ℝ} {d : ℕ → ℕ} (hC : 96 ≤ C)
    (hlog : LogLowerBound C d) (hsparse : SparseDegrees d) :
    ∀ᶠ n : ℕ in atTop,
      Real.logb 2 n + (3 / 2 : ℝ) * Real.logb 2 (d n) + 2 ≤ (d n : ℝ) / 12 := by
  have hCpos : 0 < C := by linarith
  have hloglarge : ∀ᶠ n : ℕ in atTop, 2 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop 2
  filter_upwards [eventually_valid_degrees hCpos hlog hsparse, hlog, hloglarge]
    with n hn hln hlarge
  exact weight_range_le_degree hlarge hn.1 hn.2.le
    ((mul_le_mul_of_nonneg_right hC (by linarith)).trans hln)

end CircularLaw
