import CircularLaw.RoundedMinorLogReview
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exact floor estimates and limits for the Bernoulli squeeze

Both manuscript floors are retained literally. The lost prefix fraction
is at least `epsilon`, while the minor and prefix dimension ratios tend
to one as `epsilon` tends to zero. These estimates do not assume any
random-matrix convergence theorem.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem floor_div_nat_error_bounds {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x / n - (⌊x⌋₊ : ℝ) / n ∧ x / n - (⌊x⌋₊ : ℝ) / n ≤ 1 / n := by
  rw [← sub_div]
  have hFloor := Nat.floor_le hx
  have hFloorLower := Nat.lt_floor_add_one x
  constructor
  · exact div_nonneg (sub_nonneg.mpr hFloor) (Nat.cast_nonneg n)
  · exact (div_lt_div_of_pos_right (by linarith) (by exact_mod_cast hn : (0 : ℝ) < n)).le

theorem floor_div_nat_tendsto {x : ℕ → ℝ} {a : ℝ}
    (hx : ∀ᶠ n in atTop, 0 ≤ x n)
    (hLimit : Tendsto (fun n => x n / n) atTop (𝓝 a)) :
    Tendsto (fun n => (⌊x n⌋₊ : ℝ) / n) atTop (𝓝 a) := by
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0))
  have hError : Tendsto (fun n => x n / n - (⌊x n⌋₊ : ℝ) / n) atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [hx, eventually_ge_atTop 1] with n hn hn1
      exact (floor_div_nat_error_bounds (by omega) hn).1
    · filter_upwards [hx, eventually_ge_atTop 1] with n hn hn1
      exact (floor_div_nat_error_bounds (by omega) hn).2
    · exact hInv
  simpa only [sub_sub_cancel, sub_zero] using hLimit.sub hError

theorem bernoulli_squeeze_lengths_le {n : ℕ} {epsilon : ℝ} (hEpsilon : 0 ≤ epsilon) :
    bernoulliSqueezePrefixLength n epsilon ≤ bernoulliSqueezeMinorDimension n epsilon ∧
      bernoulliSqueezeMinorDimension n epsilon ≤ n := by
  constructor
  · apply Nat.floor_le_of_le
    have hProduct := mul_nonneg hEpsilon (Nat.cast_nonneg (bernoulliSqueezeMinorDimension n epsilon))
    nlinarith
  · apply Nat.floor_le_of_le
    have hProduct := mul_nonneg hEpsilon (Nat.cast_nonneg n)
    nlinarith

theorem bernoulli_squeeze_prefix_le {n : ℕ} {epsilon : ℝ} (hEpsilon : 0 ≤ epsilon) :
    bernoulliSqueezePrefixLength n epsilon ≤ n :=
  (bernoulli_squeeze_lengths_le hEpsilon).1.trans
    (bernoulli_squeeze_lengths_le hEpsilon).2

theorem bernoulli_squeeze_removed_fraction_lower {n : ℕ} (hn : 0 < n)
    {epsilon : ℝ} (hEpsilon : 0 ≤ epsilon) (hEpsilonOne : epsilon ≤ 1) :
    epsilon ≤ (n - bernoulliSqueezePrefixLength n epsilon : ℕ) / (n : ℝ) := by
  have hLengths := bernoulli_squeeze_lengths_le (n := n) hEpsilon
  have hMinor : (bernoulliSqueezeMinorDimension n epsilon : ℝ) ≤ (1 - epsilon) * n :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr hEpsilonOne) (Nat.cast_nonneg n))
  have hPrefix : (bernoulliSqueezePrefixLength n epsilon : ℝ) ≤
      bernoulliSqueezeMinorDimension n epsilon := by exact_mod_cast hLengths.1
  rw [Nat.cast_sub (hLengths.1.trans hLengths.2)]
  apply (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
  nlinarith

theorem bernoulli_squeeze_minor_ratio_tendsto {epsilon : ℕ → ℝ}
    (hEpsilon : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => (bernoulliSqueezeMinorDimension n (epsilon n) : ℝ) / n)
      atTop (𝓝 1) := by
  apply floor_div_nat_tendsto
  · filter_upwards [hEpsilon.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn
    exact mul_nonneg (by linarith) (Nat.cast_nonneg n)
  · have hEq : (fun n : ℕ => ((1 - epsilon n) * n) / n) =ᶠ[atTop] fun n => 1 - epsilon n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      exact mul_div_cancel_right₀ _ hnR
    rw [tendsto_congr' hEq]
    simpa only [sub_zero] using tendsto_const_nhds.sub hEpsilon

theorem bernoulli_squeeze_prefix_ratio_tendsto {epsilon : ℕ → ℝ}
    (hEpsilon : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => (bernoulliSqueezePrefixLength n (epsilon n) : ℝ) / n)
      atTop (𝓝 1) := by
  apply floor_div_nat_tendsto
  · filter_upwards [hEpsilon.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn
    exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
  · have hFactor : Tendsto (fun n => 1 - epsilon n / 4) atTop (𝓝 1) := by
      simpa only [zero_div, sub_zero] using tendsto_const_nhds.sub (hEpsilon.div_const 4)
    simpa only [← mul_div_assoc, mul_one] using
      hFactor.mul (bernoulli_squeeze_minor_ratio_tendsto hEpsilon)

theorem bernoulli_squeeze_normalizing_factor_tendsto {epsilon : ℕ → ℝ}
    (hEpsilon : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) / bernoulliSqueezePrefixLength n (epsilon n))
      atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using
    (bernoulli_squeeze_prefix_ratio_tendsto hEpsilon).inv₀ (by norm_num : (1 : ℝ) ≠ 0)

theorem bernoulli_squeeze_prefix_eventually_positive {epsilon : ℕ → ℝ}
    (hEpsilon : Tendsto epsilon atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 0 < bernoulliSqueezePrefixLength n (epsilon n) := by
  filter_upwards [(bernoulli_squeeze_prefix_ratio_tendsto hEpsilon).eventually
    (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  by_contra h
  have hZero : bernoulliSqueezePrefixLength n (epsilon n) = 0 := by omega
  simp only [hZero, Nat.cast_zero, zero_div] at hn
  exact (lt_irrefl 0 hn)

theorem removed_fraction_tendsto_zero {ell : ℕ → ℕ} (hElln : ∀ n, ell n ≤ n)
    (hRatio : Tendsto (fun n => (ell n : ℝ) / n) atTop (𝓝 1)) :
    Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0) := by
  have hEq : (fun n : ℕ => (n - ell n : ℕ) / (n : ℝ)) =ᶠ[atTop]
      fun n => 1 - (ell n : ℝ) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [Nat.cast_sub (hElln n), sub_div, div_self hnR]
  rw [tendsto_congr' hEq]
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [sub_self] using hOne.sub hRatio

theorem bernoulli_squeeze_prefix_removed_fraction_tendsto {epsilon : ℕ → ℝ}
    (hNonneg : ∀ n, 0 ≤ epsilon n) (hEpsilon : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => (n - bernoulliSqueezePrefixLength n (epsilon n) : ℕ) / (n : ℝ))
      atTop (𝓝 0) :=
  removed_fraction_tendsto_zero (fun n =>
    (bernoulli_squeeze_lengths_le (n := n) (hNonneg n)).1.trans
      (bernoulli_squeeze_lengths_le (n := n) (hNonneg n)).2)
    (bernoulli_squeeze_prefix_ratio_tendsto hEpsilon)

theorem bernoulli_squeeze_minor_removed_fraction_tendsto {epsilon : ℕ → ℝ}
    (hNonneg : ∀ n, 0 ≤ epsilon n) (hEpsilon : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => (n - bernoulliSqueezeMinorDimension n (epsilon n) : ℕ) / (n : ℝ))
      atTop (𝓝 0) :=
  removed_fraction_tendsto_zero
    (fun n => (bernoulli_squeeze_lengths_le (n := n) (hNonneg n)).2)
    (bernoulli_squeeze_minor_ratio_tendsto hEpsilon)

theorem bernoulli_squeeze_exact_base_le_prefix {n : ℕ} {epsilon : ℝ}
    (hEpsilon : 0 ≤ epsilon) (hEpsilonOne : epsilon ≤ 1) :
    bernoulliSqueezeMinorDimension n epsilon - 2 * (n - bernoulliSqueezeMinorDimension n epsilon) ≤
      bernoulliSqueezePrefixLength n epsilon := by
  let m := bernoulliSqueezeMinorDimension n epsilon
  let delta := n - m
  have hmn : m ≤ n := (bernoulli_squeeze_lengths_le hEpsilon).2
  have hMinor : (m : ℝ) ≤ (1 - epsilon) * n :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr hEpsilonOne) (Nat.cast_nonneg n))
  have hDelta : epsilon * (m : ℝ) ≤ (delta : ℝ) := by
    change epsilon * (m : ℝ) ≤ ((n - m : ℕ) : ℝ)
    rw [Nat.cast_sub hmn]
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hProduct := mul_le_mul_of_nonneg_left hmnR hEpsilon
    nlinarith
  change m - 2 * delta ≤ ⌊(1 - epsilon / 4) * m⌋₊
  by_cases hZero : delta = 0
  · have hProduct : epsilon * (m : ℝ) = 0 := by
      have hNonneg := mul_nonneg hEpsilon (Nat.cast_nonneg m)
      simp only [hZero, Nat.cast_zero] at hDelta
      linarith
    have hArg : (1 - epsilon / 4) * (m : ℝ) = m := by nlinarith
    simp only [hZero, mul_zero, Nat.sub_zero, hArg, Nat.floor_natCast]
    exact le_rfl
  · by_cases hTwice : 2 * delta ≤ m
    · apply (Nat.cast_le (α := ℝ)).mp
      rw [Nat.cast_sub hTwice, Nat.cast_mul, Nat.cast_ofNat]
      have hDeltaOne : (1 : ℝ) ≤ delta := by exact_mod_cast (by omega : 1 ≤ delta)
      have hFloor := Nat.lt_floor_add_one ((1 - epsilon / 4) * (m : ℝ))
      nlinarith
    · omega

theorem bernoulli_squeeze_deleted_shift_eventually_fits {epsilon : ℕ → ℝ}
    (hNonneg : ∀ n, 0 ≤ epsilon n) (hEpsilon : Tendsto epsilon atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 2 * (n - bernoulliSqueezeMinorDimension n (epsilon n)) ≤
      bernoulliSqueezeMinorDimension n (epsilon n) := by
  have hMinor := (bernoulli_squeeze_minor_ratio_tendsto hEpsilon).eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hDeleted := (bernoulli_squeeze_minor_removed_fraction_tendsto hNonneg hEpsilon).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hMinor, hDeleted, eventually_ge_atTop 1] with n hm hd hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmR := (lt_div_iff₀ hnR).mp hm
  have hdR := (div_lt_iff₀ hnR).mp hd
  have hBound : (2 : ℝ) * (n - bernoulliSqueezeMinorDimension n (epsilon n) : ℕ) ≤
      bernoulliSqueezeMinorDimension n (epsilon n) := by linarith
  exact_mod_cast hBound

end CircularLaw
