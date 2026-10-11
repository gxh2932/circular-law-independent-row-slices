import CircularLaw.CanonicalSpreadSum

/-!
# The full canonical conditional row-local small-ball lemma

Every visited canonical block has a proved inverse-weight bound. Exact
count conditioning and convolution reduce the actual row sum to a block;
taking the visited minimum and truncating by one proves the manuscript
estimator bound. No block concentration estimate remains a hypothesis.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def rowSmallBallConstant : ℝ := 40000 + spreadBlockConstant

theorem rowSmallBallConstant_ge_regular : 40000 ≤ rowSmallBallConstant := by
  unfold rowSmallBallConstant
  linarith [spreadBlockConstant_ge_one]

theorem rowSmallBallConstant_ge_spread : spreadBlockConstant ≤ rowSmallBallConstant := by
  unfold rowSmallBallConstant
  linarith

theorem rowSmallBallConstant_ge_one : 1 ≤ rowSmallBallConstant := by
  linarith [rowSmallBallConstant_ge_regular]

theorem canonical_profile_block_small_ball {n k d : ℕ}
    (hd : 65536 ≤ d) (hk : 0 < k) (y : Fin n → ℂ) (hy : IsKVector k y)
    (reference : Fin d → Fin n) (q : CanonicalLabel y ((d : ℝ) / (k : ℝ)))
    (hm : 0 < profileCounts (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part reference q)
    {τ : ℝ} (hτ : 1 ≤ τ) (z : ℂ) :
    uniformProbability (fun b :
      Fin (profileCounts (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part reference q) →
      {a : Fin n // (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part a = q} =>
        ‖(∑ a, y (b a).val) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) ≤
      rowSmallBallConstant * τ ^ 2 *
        (actualProfileWeight (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) reference q)⁻¹ := by
  have hmd := trialCount_le_degree (fun i =>
    (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part i = q) reference
  have hmOne : 1 ≤ profileCounts
      (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part reference q := by omega
  have hCountBound : profileCounts
      (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part reference q ≤ d := hmd
  have hWeight := actualProfileWeight_nonneg
    (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) reference q
  cases hq : q.val.1
  · have h := canonical_regular_profile_block_small_ball hk hmOne hCountBound y hy q hq hτ z
    apply h.trans
    simp only [actualProfileWeight, canonicalRowProfile, hq, Bool.false_eq_true,
      ↓reduceIte, mul_div_assoc] at hWeight ⊢
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right rowSmallBallConstant_ge_regular (sq_nonneg τ))
      (inv_nonneg.mpr hWeight)
  · have h := canonical_spread_profile_block_small_ball hd hk hmOne hCountBound y q hq hτ z
    apply h.trans
    simp only [actualProfileWeight, canonicalRowProfile, hq, ↓reduceIte] at hWeight ⊢
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right rowSmallBallConstant_ge_spread (sq_nonneg τ))
      (inv_nonneg.mpr hWeight)

theorem canonical_conditional_row_small_ball {n k d : ℕ}
    (hd : 65536 ≤ d) (hk : 0 < k) (y : Fin n → ℂ) (hy : IsKVector k y)
    (reference : Fin d → Fin n) {τ : ℝ} (hτ : 1 ≤ τ) (z : ℂ) :
    uniformProbability (fun samples : ProfileFiber
      (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part d
      (profileCounts (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part reference) =>
        ‖(∑ i, y (samples.val i)) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) ≤
      rowSmallBallConstant * τ ^ 2 * profileEstimator
        (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part
        (actualProfileWeight (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) reference)
        (by omega) reference := by
  have hK : 1 ≤ rowSmallBallConstant * τ ^ 2 := by
    have hτSq : 1 ≤ τ ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hτSq
      (by linarith [rowSmallBallConstant_ge_one] : 0 ≤ rowSmallBallConstant)
    nlinarith [rowSmallBallConstant_ge_one]
  exact conditional_profile_estimator_of_block_bounds _ (by omega) reference y hK
    (fun q hm z => canonical_profile_block_small_ball hd hk y hy reference q hm hτ z) z

def ConditionalRowSmallBallLemma : Prop :=
  ∃ (C : ℝ) (d₀ : ℕ), 0 < C ∧ ∀ (n k d : ℕ), ∀ (_hd : max 1 d₀ ≤ d), 0 < k →
    ∀ (y : Fin n → ℂ), IsKVector k y → ∀ (reference : Fin d → Fin n),
    ∀ (τ : ℝ), 1 ≤ τ → ∀ z : ℂ,
      uniformProbability (fun samples : ProfileFiber
        (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part d
        (profileCounts (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part reference) =>
          ‖(∑ i, y (samples.val i)) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) ≤
        C * τ ^ 2 * profileEstimator
          (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part
          (actualProfileWeight (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) reference)
          (by omega) reference

theorem conditional_row_small_ball_lemma : ConditionalRowSmallBallLemma := by
  refine ⟨rowSmallBallConstant, 65536, by linarith [rowSmallBallConstant_ge_one], ?_⟩
  intro n k d hd hk y hy reference τ hτ z
  exact canonical_conditional_row_small_ball hd hk y hy reference hτ z

end CircularLaw
