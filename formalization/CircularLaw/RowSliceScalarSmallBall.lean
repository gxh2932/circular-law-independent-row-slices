import CircularLaw.SeparatedPairLowerTail

/-!
# The full fixed-degree slice scalar small-ball estimate

Exact paired sampling, the proved scalar Bernoulli estimate and the actual
separated-pair exponential tail discharge every input of SSS23 Lemma 8.5.
An explicit absolute constant is supplied, uniformly in the slice degree,
coordinate vector, positive radius, density and scalar centre.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem paired_slice_small_ball_of_real_count {n d : ℕ}
    (e : Fin d ⊕ Fin d ↪ Fin n) (y : Fin n → ℂ) {ρ r k : ℝ}
    (hρ : 0 < ρ) (hr : ρ / 2 ≤ r) (hk : 0 < k)
    (hCount : k ≤ ((pairedSeparatedCoordinates y ρ e).card : ℝ)) (z : ℂ) :
    uniformProbability (fun x : Fin d → Bool => ‖rowLinearForm (pairedSlice e x) y - z‖ ≤ r) ≤
      bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt (k / 2) := by
  have hCard : 0 < (pairedSeparatedCoordinates y ρ e).card := by exact_mod_cast hk.trans_le hCount
  have h := paired_slice_conditional_small_ball e y (pairedSeparatedCoordinates y ρ e)
    (Finset.card_pos.mp hCard) hρ (fun _ hj => (Finset.mem_filter.mp hj).2) hr z
  have hrNonneg : 0 ≤ r := (by positivity : 0 ≤ ρ / 2).trans hr
  exact h.trans (div_le_div_of_nonneg_left
    (mul_nonneg bernoulli_scalar_small_ball_constant_pos.le (div_nonneg hrNonneg hρ.le))
    (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hCount (by norm_num))))

theorem row_slice_small_ball_le_real_pair_failure {n d : ℕ} (hSize : 2 * d ≤ n)
    (y : Fin n → ℂ) {ρ r k : ℝ} (hρ : 0 < ρ) (hr : ρ / 2 ≤ r) (hk : 0 < k) (z : ℂ) :
    uniformProbability (fun S : RowSlice n d => ‖rowLinearForm S y - z‖ ≤ r) ≤
      bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt (k / 2) +
        uniformProbability (fun e : Fin d ⊕ Fin d ↪ Fin n =>
          ((pairedSeparatedCoordinates y ρ e).card : ℝ) < k) := by
  haveI : Nonempty (Fin d ⊕ Fin d ↪ Fin n) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_sum, Fintype.card_fin] using (by omega : d + d ≤ n))
  let q := bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt (k / 2)
  have hrNonneg : 0 ≤ r := (by positivity : 0 ≤ ρ / 2).trans hr
  have hq : 0 ≤ q := div_nonneg
    (mul_nonneg bernoulli_scalar_small_ball_constant_pos.le (div_nonneg hrNonneg hρ.le))
    (Real.sqrt_nonneg _)
  rw [uniform_paired_slice_conditioning hSize]
  calc
    _ ≤ finiteMean (fun e : Fin d ⊕ Fin d ↪ Fin n =>
      q + if ((pairedSeparatedCoordinates y ρ e).card : ℝ) < k then (1 : ℝ) else 0) := by
      apply finiteMean_mono
      intro e
      by_cases hCount : k ≤ ((pairedSeparatedCoordinates y ρ e).card : ℝ)
      · simpa only [not_lt.mpr hCount, if_false, add_zero] using
          paired_slice_small_ball_of_real_count e y hρ hr hk hCount z
      · simp only [lt_of_not_ge hCount, if_true]
        exact (uniformProbability_le_one _).trans (by linarith)
    _ = _ := by rw [finiteMean_add, finiteMean_const, finiteMean_indicator]

theorem row_slice_scalar_small_ball_explicit {n d : ℕ} (hd : 0 < d) (hSize : 2 * d ≤ n)
    (y : Fin n → ℂ) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hLevel : ∀ c : ℂ, ((Finset.univ.filter (fun j => ‖y j - c‖ ≤ ρ)).card : ℝ) ≤
      (1 - δ) * n) :
    rowSliceDiskConcentration (d := d) y ρ ≤
      2 * bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) + Real.exp (-δ ^ 2 * d / 64) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : Real.sqrt ((δ * (d : ℝ) / 2) / 2) = Real.sqrt (δ * d) / 2 := by
    rw [show (δ * (d : ℝ) / 2) / 2 = δ * d / 4 by ring,
      Real.sqrt_div (by positivity : 0 ≤ δ * (d : ℝ))]
    norm_num
  have hCoefficient : bernoulliScalarSmallBallConstant / Real.sqrt ((δ * (d : ℝ) / 2) / 2) =
      2 * bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) := by
    rw [hRoot]
    field_simp
  apply finiteDiskConcentration_le
  intro z
  have h := row_slice_small_ball_le_real_pair_failure hSize y hρ
    (by linarith : ρ / 2 ≤ ρ) (show 0 < δ * (d : ℝ) / 2 by positivity) z
  simp only [div_self hρ.ne', mul_one, hCoefficient] at h
  simpa only [rowLinearForm_eq_support_sum] using h.trans
    (add_le_add (le_refl _) (separated_pair_count_lower_tail hd hSize y hδ.le hρ hLevel))

def sliceScalarSmallBallConstant : ℝ := 64 + 2 * bernoulliScalarSmallBallConstant

def SliceScalarSmallBallTheorem : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 0 < d → 2 * d ≤ n →
    ∀ (y : Fin n → ℂ) (δ ρ : ℝ), 0 < δ → 0 < ρ →
      (∀ c : ℂ, ((Finset.univ.filter (fun j => ‖y j - c‖ ≤ ρ)).card : ℝ) ≤ (1 - δ) * n) →
        rowSliceDiskConcentration (d := d) y ρ ≤
          C * (1 / Real.sqrt (δ * d) + Real.exp (-δ ^ 2 * d / C))

theorem slice_scalar_small_ball_theorem : SliceScalarSmallBallTheorem := by
  have hBern := bernoulli_scalar_small_ball_constant_pos
  have hC : 0 < sliceScalarSmallBallConstant := by unfold sliceScalarSmallBallConstant; linarith
  refine ⟨sliceScalarSmallBallConstant, hC, ?_⟩
  intro n d hd hSize y δ ρ hδ hρ hLevel
  have hCoefficient : 2 * bernoulliScalarSmallBallConstant ≤ sliceScalarSmallBallConstant := by
    unfold sliceScalarSmallBallConstant
    linarith
  have h64 : 64 ≤ sliceScalarSmallBallConstant := by unfold sliceScalarSmallBallConstant; linarith
  have hExp : Real.exp (-δ ^ 2 * (d : ℝ) / 64) ≤
      Real.exp (-δ ^ 2 * d / sliceScalarSmallBallConstant) := by
    apply Real.exp_le_exp.mpr
    have hDiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ δ ^ 2 * (d : ℝ))
      (by norm_num : (0 : ℝ) < 64) h64
    simpa only [neg_mul, neg_div] using neg_le_neg hDiv
  calc
    _ ≤ 2 * bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) +
        Real.exp (-δ ^ 2 * d / 64) := row_slice_scalar_small_ball_explicit hd hSize y hδ hρ hLevel
    _ ≤ sliceScalarSmallBallConstant / Real.sqrt (δ * d) +
        sliceScalarSmallBallConstant * Real.exp (-δ ^ 2 * d / sliceScalarSmallBallConstant) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right hCoefficient (Real.sqrt_nonneg _)
      · exact hExp.trans (le_mul_of_one_le_left (Real.exp_nonneg _) (by linarith))
    _ = _ := by ring

theorem row_slice_nonalmost_scalar_small_ball {n d : ℕ} (hd : 0 < d) (hSize : 2 * d ≤ n)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (x : EuclideanSpace ℂ (Fin n))
    (hx : sourceNonAlmostConstant δ ρ x) :
    rowSliceDiskConcentration (d := d) (fun j => x j) (ρ / Real.sqrt n) ≤
      2 * bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) + Real.exp (-δ ^ 2 * d / 64) :=
  row_slice_scalar_small_ball_explicit hd hSize _ hδ
    (div_pos hρ (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n)))) hx

end CircularLaw
