import CircularLaw.GaussianLeadingBernoulliPatterns
import CircularLaw.GaussianWordNoncrossingCounts
import CircularLaw.BernoulliShiftedMomentConcentration

/-!
# Bernoulli leading-pattern counts equal the actual Gaussian word counts

The compatible partner construction and the generated Gaussian kernel
give inverse maps between all leading vertex patterns and all leading
Gaussian matchings. The equality includes unbalanced and empty words.
It identifies every actual centered Bernoulli moment probability limit
with the checked Gaussian moment, including every complex scalar shift.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

local instance bernoulliGaussianCountBEq {α : Type*} (s : Setoid α) :
    BEq (Quotient s × Quotient s) := instBEqOfDecidableEq

def bernoulliGaussianLeadingPatternsEquiv {k : ℕ} (b : Fin (k + 1) → Bool) :
    {s : Setoid (Fin (k + 1)) // BernoulliLeadingPattern b s} ≃
      {e : GaussianWordPairing b // gaussianWordVertexExponent b (finRotate (k + 1)) e =
        Fintype.card (GaussianDirectPositions b) + 1} where
  toFun s := ⟨bernoulliLeadingPairing b s.val s.property,
    bernoulli_leading_pairing_vertex_exponent b s.val s.property⟩
  invFun e := ⟨gaussianWordPairingSetoid b (finRotate (k + 1)) e.val,
    gaussian_leading_pattern_is_bernoulli_leading b e.val e.property⟩
  left_inv s := Subtype.ext (bernoulli_leading_pairing_setoid_eq b s.val s.property)
  right_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change bernoulliLeadingPartner b (gaussianWordPairingSetoid b (finRotate (k + 1)) e.val)
      (gaussian_leading_pattern_is_bernoulli_leading b e.val e.property) a.val = (e.val a).val
    apply (bernoulli_leading_partner_unique b _
      (gaussian_leading_pattern_is_bernoulli_leading b e.val e.property) a.val (e.val a).val _ _).symm
    · apply (gaussian_leading_oriented_entry_eq_iff_label b _ e.val
        (fin_rotate_same_cycle k) e.property _ _).mpr
      rw [gaussian_word_position_label_adjoint, gaussian_word_position_label_direct]
    · simp [(e.val a).property, a.property]

theorem bernoulli_leading_pattern_count_eq_gaussian (k : ℕ) (b : Fin (k + 1) → Bool) :
    bernoulliLeadingPatternCount b = gaussianWordLeadingCount k b := by
  rw [bernoulliLeadingPatternCount, Nat.card_congr (bernoulliGaussianLeadingPatternsEquiv b),
    Nat.card_eq_fintype_card]
  rfl

theorem bernoulli_leading_pattern_count_eq_gaussian_word (k : ℕ) (b : Fin (k + 1) → Bool) :
    bernoulliLeadingPatternCount b = gaussianWordMeanCount (List.ofFn b) := by
  rw [bernoulli_leading_pattern_count_eq_gaussian,
    gaussian_word_leading_count_eq_noncrossing_card, gaussian_word_mean_count_eq_noncrossing_card]

theorem bernoulli_word_mean_limit_eq_gaussian (w : List Bool) :
    bernoulliWordMeanLimit w = gaussianWordMeanCount w := by
  cases w with
  | nil => exact gaussian_word_mean_count_nil.symm
  | cons b w =>
    simpa only [bernoulliWordMeanLimit, List.ofFn_get] using
      bernoulli_leading_pattern_count_eq_gaussian_word w.length ((b :: w).get)

theorem bernoulli_shifted_moment_mean_limit_eq_gaussian (z : ℂ) (k : ℕ) :
    bernoulliShiftedMomentMeanLimit z k = gaussianShiftedMomentMeanLimit z k := by
  simp only [bernoulliShiftedMomentMeanLimit, gaussianShiftedMomentMeanLimit,
    bernoulli_word_mean_limit_eq_gaussian]

theorem bernoulli_centered_word_gaussian_mean_tendsto (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (w : List Bool) :
    Tendsto (fun n => bernoulliNormalizedWordMean n (d n) w) atTop
      (𝓝 (gaussianWordMeanCount w : ℝ)) := by
  rw [← bernoulli_word_mean_limit_eq_gaussian]
  exact bernoulli_all_word_mean_tendsto d hDegree hSparse w

theorem bernoulli_centered_word_gaussian_limit_in_probability (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (w : List Bool) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n => bernoulliNormalizedWordTrace (d n) w) (gaussianWordMeanCount w : ℝ) := by
  rw [← bernoulli_word_mean_limit_eq_gaussian]
  exact bernoulli_word_converges_in_probability d hDegree hSparse w

theorem bernoulli_centered_shifted_gaussian_moment_in_probability (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (z : ℂ) (k : ℕ) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n => bernoulliCenteredShiftedSingularMoment (d n) z k)
      (gaussianShiftedMomentMeanLimit z k).re := by
  rw [← bernoulli_shifted_moment_mean_limit_eq_gaussian]
  exact bernoulli_centered_shifted_moment_converges_in_probability d hDegree hSparse z k

end CircularLaw
