import CircularLaw.ConditionalRow

/-!
# Both conclusions of the averaged row-profile proposition

The actual conditional bound is averaged over count fibers and combined
with the checked max-weight and occupancy estimates. The theorem includes
the planar small-ball conclusion and deterministic scalar translations.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

theorem canonical_averaged_row_small_ball {n k d : ℕ}
    (hn : 0 < n) (hd : 65536 ≤ d) (hk : 0 < k) (y : Fin n → ℂ) (hy : IsKVector k y)
    (hrange : ∀ a b,
      |dyadicWeight (truncatedProfileWeight
        (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) d
        ((canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part a)) -
       dyadicWeight (truncatedProfileWeight
        (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) d
        ((canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part b))| ≤ (d : ℝ) / 12)
    (hdegree : Real.rpow (d : ℝ) (1 / 3 : ℝ) *
      Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) ≤
        Real.exp (-(binomialHalfRate / 2) * Real.rpow (d : ℝ) (2 / 3 : ℝ)))
    {τ : ℝ} (hτ : 1 ≤ τ) (z v : ℂ) :
    let P := canonicalRowProfile y ((d : ℝ) / (k : ℝ))
    uniformProbability (fun samples : Fin d → Fin n =>
      ‖(∑ i, y (samples i)) + v - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) ≤
      rowSmallBallConstant * τ ^ 2 *
        (4 * Real.exp (-averagedProfileRate *
          pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) *
            profileGeometricMean P.part (truncatedProfileWeight P d) +
              Real.exp (-averagedProfileRate * Real.rpow (d : ℝ) (2 / 3 : ℝ))) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hK : 1 ≤ rowSmallBallConstant * τ ^ 2 := by
    have hτSq : 1 ≤ τ ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hτSq
      (by linarith [rowSmallBallConstant_ge_one] : 0 ≤ rowSmallBallConstant)
    nlinarith [rowSmallBallConstant_ge_one]
  have h := averaged_row_small_ball_of_block_bounds
    (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) (by omega) y hK
    (fun reference q hm z => canonical_profile_block_small_ball hd hk y hy reference q hm hτ z)
    (z - v)
  have hMean := averaged_actual_profile
    (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) (by omega) hrange hdegree
  have hTotal := h.trans (mul_le_mul_of_nonneg_left hMean (by linarith : 0 ≤ rowSmallBallConstant * τ ^ 2))
  have hEvent : (fun samples : Fin d → Fin n =>
      ‖(∑ i, y (samples i)) + v - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) =
      (fun samples : Fin d → Fin n =>
        ‖(∑ i, y (samples i)) - (z - v)‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) := by
    funext samples
    have hEq : (∑ i, y (samples i)) + v - z = (∑ i, y (samples i)) - (z - v) := by abel
    rw [hEq]
  rw [hEvent]
  exact hTotal

def averagedRowConstant : ℝ := rowSmallBallConstant + 4

theorem averagedRowConstant_ge_four : 4 ≤ averagedRowConstant := by
  unfold averagedRowConstant
  linarith [rowSmallBallConstant_ge_one]

theorem averagedRowConstant_ge_row : rowSmallBallConstant ≤ averagedRowConstant := by
  unfold averagedRowConstant
  linarith

def AveragedRowProfileLemma : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ,
    ∀ n k d : ℕ, 0 < n → ∀ (_hd : max 65536 d₀ ≤ d), 0 < k →
      ∀ y : Fin n → ℂ, IsKVector k y →
      let P := canonicalRowProfile y ((d : ℝ) / (k : ℝ))
      (∀ a b, |dyadicWeight (truncatedProfileWeight P d (P.part a)) -
        dyadicWeight (truncatedProfileWeight P d (P.part b))| ≤ ε * d) →
      let A := C * Real.exp (-c *
        pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) *
          profileGeometricMean P.part (truncatedProfileWeight P d) +
            Real.exp (-c * Real.rpow (d : ℝ) (2 / 3 : ℝ))
      finiteMean (fun samples : Fin d → Fin n =>
        profileEstimator P.part (actualProfileWeight P samples) (by omega) samples) ≤ A ∧
      ∀ τ : ℝ, 1 ≤ τ → ∀ z v : ℂ,
        uniformProbability (fun samples : Fin d → Fin n =>
          ‖(∑ i, y (samples i)) + v - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) ≤ C * τ ^ 2 * A

theorem averaged_row_profile_lemma : AveragedRowProfileLemma := by
  rcases Filter.eventually_atTop.mp eventually_profile_prefactor_absorbed with ⟨d₀, h₀⟩
  refine ⟨1 / 12, by norm_num, averagedProfileRate, averagedProfileRate_pos,
    averagedRowConstant, by linarith [averagedRowConstant_ge_four], d₀, ?_⟩
  intro n k d hn hd hk y hy P hrange A
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hdLarge : 65536 ≤ d := (le_max_left _ _).trans hd
  have hdegree := h₀ d ((le_max_right _ _).trans hd)
  have hRange : ∀ a b,
      |dyadicWeight (truncatedProfileWeight P d (P.part a)) -
        dyadicWeight (truncatedProfileWeight P d (P.part b))| ≤ (d : ℝ) / 12 := by
    intro a b
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hrange a b
  have hW : 0 ≤ profileGeometricMean P.part (truncatedProfileWeight P d) := by
    rw [profileGeometricMean_eq_exp _ _ (truncatedProfileWeight_pos P (by omega))]
    exact Real.exp_nonneg _
  have hA : 4 * Real.exp (-averagedProfileRate *
      pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) *
        profileGeometricMean P.part (truncatedProfileWeight P d) +
          Real.exp (-averagedProfileRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) ≤ A := by
    exact add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right averagedRowConstant_ge_four (Real.exp_nonneg _)) hW) le_rfl
  refine ⟨(averaged_actual_profile P (by omega) hRange hdegree).trans hA, ?_⟩
  intro τ hτ z v
  have h := canonical_averaged_row_small_ball hn hdLarge hk y hy hRange hdegree hτ z v
  apply h.trans
  have hτSq : 0 ≤ τ ^ 2 := sq_nonneg τ
  have hLeft : 0 ≤ rowSmallBallConstant * τ ^ 2 := mul_nonneg
    (by linarith [rowSmallBallConstant_ge_one]) hτSq
  have hANonneg : 0 ≤ A := by
    dsimp only [A]
    have hC : 0 ≤ averagedRowConstant := by linarith [averagedRowConstant_ge_four]
    positivity
  exact (mul_le_mul_of_nonneg_left hA hLeft).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right averagedRowConstant_ge_row hτSq) hANonneg)

end CircularLaw
