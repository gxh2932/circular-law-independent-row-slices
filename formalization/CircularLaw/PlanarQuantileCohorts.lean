import CircularLaw.RankQuantiles
import CircularLaw.Discretization

/-!
# Separated cohorts from planar nonconcentration

Apply trimmed real and imaginary quantiles to the literal floor-rounded
vector. If neither coordinate has a large quantile gap, the intersection
of the two cores places too many original coordinates in a single disk.
The one-sided floor error retains the source scale `k >= 5/theta`.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem complex_real_gap_le_dist (z w : ℂ) : w.re - z.re ≤ dist z w := by
  calc
    _ ≤ |w.re - z.re| := le_abs_self _
    _ ≤ ‖w - z‖ := by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
    _ = dist z w := by rw [dist_eq_norm, norm_sub_rev]

theorem complex_imag_gap_le_dist (z w : ℂ) : w.im - z.im ≤ dist z w := by
  calc
    _ ≤ |w.im - z.im| := le_abs_self _
    _ ≤ ‖w - z‖ := by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
    _ = dist z w := by rw [dist_eq_norm, norm_sub_rev]

theorem quantile_cohort_rounding {n r : ℕ} (hn : 2 ≤ n) (hr : 0 < r) (hrn : r ≤ n) :
    0 < (r + 3) / 4 ∧ 2 * ((r + 3) / 4) ≤ n ∧
      4 * ((r + 3) / 4 - 1) < r ∧ r ≤ 4 * ((r + 3) / 4) := by
  omega

theorem canonicalApprox_separated_cohorts {n r k : ℕ} (hn : 2 ≤ n)
    (hr : 0 < r) (hrn : r ≤ n) (hk : 0 < k) {θ : ℝ} (hθ : 0 < θ)
    (hScale : 5 / θ ≤ (k : ℝ)) (x : Fin n → ℂ)
    (hNoCenter : ∀ c : ℂ,
      (Finset.univ.filter (fun i => ‖x i - c‖ ≤ θ)).card ≤ n - r) :
    ∃ I J : Finset (Fin n), Disjoint I J ∧ (r : ℝ) / 4 ≤ I.card ∧
      (r : ℝ) / 4 ≤ J.card ∧
      ∀ i ∈ I, ∀ j ∈ J,
        θ / 2 ≤ dist (canonicalApprox k (x i)) (canonicalApprox k (x j)) := by
  let m := (r + 3) / 4
  have hRound := quantile_cohort_rounding hn hr hrn
  have hm : 0 < m := hRound.1
  have hHalf : 2 * m ≤ n := hRound.2.1
  have hmn : m ≤ n := by omega
  have hCount : (r : ℝ) / 4 ≤ (m : ℝ) := by
    have hCast : (r : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast hRound.2.2.2
    linarith
  let y : Fin n → ℂ := fun i => canonicalApprox k (x i)
  let f : Fin n → ℝ := fun i => (y i).re
  let g : Fin n → ℝ := fun i => (y i).im
  let lo : Fin n := ⟨m - 1, by omega⟩
  let hi : Fin n := ⟨n - m, by omega⟩
  by_cases hRe : θ / 2 ≤ f (Tuple.sort f hi) - f (Tuple.sort f lo)
  · obtain ⟨I, J, hDisjoint, hI, hJ, hSep⟩ := real_quantile_gap_cohorts f hm hHalf hRe
    refine ⟨I, J, hDisjoint, by simpa only [hI] using hCount,
      by simpa only [hJ] using hCount, ?_⟩
    intro i hi j hj
    exact (hSep i hi j hj).trans (complex_real_gap_le_dist (y i) (y j))
  by_cases hIm : θ / 2 ≤ g (Tuple.sort g hi) - g (Tuple.sort g lo)
  · obtain ⟨I, J, hDisjoint, hI, hJ, hSep⟩ := real_quantile_gap_cohorts g hm hHalf hIm
    refine ⟨I, J, hDisjoint, by simpa only [hI] using hCount,
      by simpa only [hJ] using hCount, ?_⟩
    intro i hi j hj
    exact (hSep i hi j hj).trans (complex_imag_gap_le_dist (y i) (y j))
  have hReGap : f (Tuple.sort f hi) - f (Tuple.sort f lo) < θ / 2 := lt_of_not_ge hRe
  have hImGap : g (Tuple.sort g hi) - g (Tuple.sort g lo) < θ / 2 := lt_of_not_ge hIm
  let F := (rankCore (Tuple.sort f) m) ∩ rankCore (Tuple.sort g) m
  let c : ℂ := ⟨f (Tuple.sort f lo), g (Tuple.sort g lo)⟩
  have hMany : n - r < F.card := by
    have hCore := two_rankCore_inter_card_lower (Tuple.sort f) (Tuple.sort g) hmn
    change n ≤ 4 * (m - 1) + F.card at hCore
    have hRemoved : 4 * (m - 1) < r := hRound.2.2.1
    omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hError : 1 / (k : ℝ) ≤ θ / 5 := by
    have hProduct := (div_le_iff₀ hθ).mp hScale
    apply (div_le_iff₀ hkR).mpr
    nlinarith
  have hSqrt : Real.sqrt 2 ≤ 10 / 7 := by
    have hSq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hNonneg := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hSub : F ⊆ Finset.univ.filter (fun i => ‖x i - c‖ ≤ θ) := by
    intro i hiF
    have hF := real_rankCore_value_bounds f hm hmn i (Finset.mem_inter.mp hiF).1
    have hG := real_rankCore_value_bounds g hm hmn i (Finset.mem_inter.mp hiF).2
    have hFloorRe := real_floor_approx_error hk (x i).re
    have hFloorIm := real_floor_approx_error hk (x i).im
    have hRe0 : 0 ≤ (x i - c).re := by
      change 0 ≤ (x i).re - f (Tuple.sort f lo)
      change 0 ≤ (x i).re - f i ∧ _ at hFloorRe
      linarith [hF.1]
    have hIm0 : 0 ≤ (x i - c).im := by
      change 0 ≤ (x i).im - g (Tuple.sort g lo)
      change 0 ≤ (x i).im - g i ∧ _ at hFloorIm
      linarith [hG.1]
    have hReB : |(x i - c).re| ≤ 7 * θ / 10 := by
      rw [abs_of_nonneg hRe0]
      change (x i).re - f (Tuple.sort f lo) ≤ _
      change _ ∧ (x i).re - f i < 1 / (k : ℝ) at hFloorRe
      linarith [hF.2, hFloorRe.2]
    have hImB : |(x i - c).im| ≤ 7 * θ / 10 := by
      rw [abs_of_nonneg hIm0]
      change (x i).im - g (Tuple.sort g lo) ≤ _
      change _ ∧ (x i).im - g i < 1 / (k : ℝ) at hFloorIm
      linarith [hG.2, hFloorIm.2]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    calc
      ‖x i - c‖ ≤ Real.sqrt 2 * max |(x i - c).re| |(x i - c).im| :=
        Complex.norm_le_sqrt_two_mul_max _
      _ ≤ Real.sqrt 2 * (7 * θ / 10) :=
        mul_le_mul_of_nonneg_left (max_le hReB hImB) (Real.sqrt_nonneg _)
      _ ≤ (10 / 7) * (7 * θ / 10) :=
        mul_le_mul_of_nonneg_right hSqrt (by positivity)
      _ = θ := by ring
  have hCard := (Finset.card_le_card hSub).trans (hNoCenter c)
  omega

end CircularLaw
