import CircularLaw.BernoulliSqueezeRounding

/-!
# The literal rounded source cutoff fits the greedy process

For epsilon <= 1/8 and epsilon*N >= 4, the two original floors give
enough initial rows, the required initial-height bound, and an omitted
rank fraction at most 2*epsilon. The dimension condition holds eventually
at every fixed positive epsilon; neither floor is replaced by its limit.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem bernoulli_rounded_greedy_cutoff_bounds {N : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hEighth : ε ≤ 1 / 8) (hScale : 4 ≤ ε * N) :
    3 * (N : ℝ) / 4 ≤ bernoulliSqueezeMinorDimension N ε ∧
      2 * (bernoulliSqueezeMinorDimension N ε - bernoulliSqueezePrefixLength N ε) ≤
        N - bernoulliSqueezeMinorDimension N ε ∧
      ((N - bernoulliSqueezePrefixLength N ε : ℕ) : ℝ) / N ≤ 2 * ε := by
  have hOne : ε ≤ 1 := by linarith
  have hLengths := bernoulli_squeeze_lengths_le (n := N) hε.le
  have hMN : (bernoulliSqueezeMinorDimension N ε : ℝ) ≤ N := by exact_mod_cast hLengths.2
  have hMUpper : (bernoulliSqueezeMinorDimension N ε : ℝ) ≤ (1 - ε) * N :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr hOne) (Nat.cast_nonneg N))
  have hMLower := Nat.lt_floor_add_one ((1 - ε) * (N : ℝ))
  have hRLower := Nat.lt_floor_add_one ((1 - ε / 4) * (bernoulliSqueezeMinorDimension N ε : ℝ))
  change (1 - ε) * (N : ℝ) < (bernoulliSqueezeMinorDimension N ε : ℝ) + 1 at hMLower
  change (1 - ε / 4) * (bernoulliSqueezeMinorDimension N ε : ℝ) <
    (bernoulliSqueezePrefixLength N ε : ℝ) + 1 at hRLower
  have hEpsM : ε * (bernoulliSqueezeMinorDimension N ε : ℝ) ≤ ε * N :=
    mul_le_mul_of_nonneg_left hMN hε.le
  have hEpsN : ε * (N : ℝ) ≤ (N : ℝ) / 8 := by
    have h := mul_le_mul_of_nonneg_right hEighth (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    linarith
  have hN : 0 < (N : ℝ) := by nlinarith
  refine ⟨by nlinarith, ?_, ?_⟩
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hLengths.1, Nat.cast_sub hLengths.2]
    nlinarith
  · rw [Nat.cast_sub (hLengths.1.trans hLengths.2)]
    apply (div_le_iff₀ hN).mpr
    nlinarith

theorem bernoulli_rounded_greedy_cutoff_eventually {ε : ℝ}
    (hε : 0 < ε) (hEighth : ε ≤ 1 / 8) :
    ∀ᶠ N : ℕ in atTop,
      3 * (N : ℝ) / 4 ≤ bernoulliSqueezeMinorDimension N ε ∧
      2 * (bernoulliSqueezeMinorDimension N ε - bernoulliSqueezePrefixLength N ε) ≤
        N - bernoulliSqueezeMinorDimension N ε ∧
      ((N - bernoulliSqueezePrefixLength N ε : ℕ) : ℝ) / N ≤ 2 * ε := by
  have hGrowth : Tendsto (fun N : ℕ => ε * (N : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hε).mpr tendsto_natCast_atTop_atTop
  filter_upwards [hGrowth.eventually_ge_atTop 4] with N hN
  exact bernoulli_rounded_greedy_cutoff_bounds hε hEighth hN

end CircularLaw
