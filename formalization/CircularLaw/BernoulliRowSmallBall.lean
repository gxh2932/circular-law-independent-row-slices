import CircularLaw.BernoulliRareSubset
import CircularLaw.TensorizationFintype
import CircularLaw.RowSliceSelectedAdjointSmallBall
import CircularLaw.BernoulliRowProductLaw

/-!
# Tensorized small balls for independent Bernoulli rows

Both bounds retain every input coefficient and every output row. The rare
bound uses only a selected large family; the large-density bound uses the
checked scalar concentration estimate. The product exponents are the actual
number of rows, including after deterministic row deletions.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace CircularLaw

theorem bernoulli_rows_rare_subset_norm_small_ball {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (a : ι → ℂ) (S : Finset ι) (hRare : (S.card : ℝ) * p ≤ 1 / 2)
    {t : ℝ} (ht : 0 < t) (hLarge : ∀ i ∈ S, t ≤ ‖a i‖) (z : ρ → ℂ) :
    (Measure.pi (fun _ : ρ => bernoulliCubeLaw ι p hp)).real
      {rows | (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (rows j i)) - z j‖ ^ 2) ≤
        t ^ 2 * ((S.card : ℝ) * p) * Fintype.card ρ / 72} ≤
      Real.exp (-((S.card : ℝ) * p) * Fintype.card ρ / 8) := by
  let ν := bernoulliCubeLaw ι p hp
  let μ := Measure.pi (fun _ : ρ => ν)
  let f := fun row : ι → Bool => ∑ i, weightedBernoulliValue (a i) (row i)
  apply finite_rare_small_ball_tensorization_fintype μ (fun j rows => f (rows j))
    (iIndepFun_pi (fun _ => (measurable_of_countable f).aemeasurable)) ht z
  intro j
  rw [finite_law_event_real (measurable_pi_apply j)
    (measurePreserving_eval (fun _ : ρ => ν) j).map_eq
    (fun row : ι → Bool => ‖f row - z j‖ ≤ t / 3)]
  exact bernoulli_cube_rare_subset_linear_form_small_ball p hp a S hRare ht hLarge (z j)

theorem bernoulli_rows_large_subset_norm_small_ball {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (a : ι → ℂ) (S : Finset ι) (hS : S.Nonempty) {t τ : ℝ} (ht : 0 < t)
    (hLarge : ∀ i ∈ S, t ≤ ‖a i‖) (hτ : 1 ≤ τ) (z : ρ → ℂ) :
    (Measure.pi (fun _ : ρ => bernoulliCubeLaw ι p hp)).real
      {rows | (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (rows j i)) - z j‖ ^ 2) ≤
        τ ^ 2 * t ^ 2 * Fintype.card ρ} ≤
      (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
        Real.sqrt ((S.card : ℝ) * p)) * τ ^ 2) ^ Fintype.card ρ := by
  let ν := bernoulliCubeLaw ι p hp
  let μ := Measure.pi (fun _ : ρ => ν)
  let f := fun row : ι → Bool => ∑ i, weightedBernoulliValue (a i) (row i)
  let A := bernoulliScalarSmallBallConstant / Real.sqrt ((S.card : ℝ) * p)
  have hA : 0 ≤ A := div_nonneg bernoulli_scalar_small_ball_constant_pos.le (Real.sqrt_nonneg _)
  apply tensorization_fintype μ (fun j rows => f (rows j)) (fun _ => measurable_of_countable _)
    (iIndepFun_pi (fun _ => (measurable_of_countable f).aemeasurable)) ht.le hA hτ
  intro j σ hσ
  apply iSup_le
  intro c
  apply (ENNReal.le_ofReal_iff_toReal_le (by finiteness) (mul_nonneg hA (sq_nonneg σ))).mpr
  change μ.real {rows | ‖f (rows j) - c‖ ≤ σ * t} ≤ A * σ ^ 2
  rw [finite_law_event_real (measurable_pi_apply j)
    (measurePreserving_eval (fun _ : ρ => ν) j).map_eq
    (fun row : ι → Bool => ‖f row - c‖ ≤ σ * t)]
  have hBound := bernoulli_cube_linear_form_small_ball p hp hpPos hHalf a S hS ht hLarge
    (by nlinarith : t / 2 ≤ σ * t) c
  have hRatio : σ * t / t = σ := by field_simp
  rw [hRatio] at hBound
  apply hBound.trans
  change bernoulliScalarSmallBallConstant * σ / Real.sqrt ((S.card : ℝ) * p) ≤ A * σ ^ 2
  have hLinear : σ ≤ σ ^ 2 := by nlinarith
  convert mul_le_mul_of_nonneg_left hLinear hA using 1
  dsimp [A]
  ring

theorem bernoulli_entries_rare_subset_norm_small_ball {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (a : ι → ℂ) (S : Finset ι) (hRare : (S.card : ℝ) * p ≤ 1 / 2)
    {t : ℝ} (ht : 0 < t) (hLarge : ∀ i ∈ S, t ≤ ‖a i‖) (z : ρ → ℂ) :
    (bernoulliCubeLaw (ρ × ι) p hp).real
      {sample | (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (sample (j, i))) - z j‖ ^ 2) ≤
        t ^ 2 * ((S.card : ℝ) * p) * Fintype.card ρ / 72} ≤
      Real.exp (-((S.card : ℝ) * p) * Fintype.card ρ / 8) := by
  have hLaw := finite_law_event_real
    (bernoulli_row_product_measure_preserving (ρ := ρ) (ι := ι) p hp).measurable
    (bernoulli_row_product_map (ρ := ρ) (ι := ι) p hp)
    (fun rows : ρ → ι → Bool =>
      (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (rows j i)) - z j‖ ^ 2) ≤
        t ^ 2 * ((S.card : ℝ) * p) * Fintype.card ρ / 72)
  exact hLaw.le.trans (bernoulli_rows_rare_subset_norm_small_ball p hp a S hRare ht hLarge z)

theorem bernoulli_entries_large_subset_norm_small_ball {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (a : ι → ℂ) (S : Finset ι) (hS : S.Nonempty) {t τ : ℝ} (ht : 0 < t)
    (hLarge : ∀ i ∈ S, t ≤ ‖a i‖) (hτ : 1 ≤ τ) (z : ρ → ℂ) :
    (bernoulliCubeLaw (ρ × ι) p hp).real
      {sample | (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (sample (j, i))) - z j‖ ^ 2) ≤
        τ ^ 2 * t ^ 2 * Fintype.card ρ} ≤
      (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
        Real.sqrt ((S.card : ℝ) * p)) * τ ^ 2) ^ Fintype.card ρ := by
  have hLaw := finite_law_event_real
    (bernoulli_row_product_measure_preserving (ρ := ρ) (ι := ι) p hp).measurable
    (bernoulli_row_product_map (ρ := ρ) (ι := ι) p hp)
    (fun rows : ρ → ι → Bool =>
      (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (rows j i)) - z j‖ ^ 2) ≤
        τ ^ 2 * t ^ 2 * Fintype.card ρ)
  exact hLaw.le.trans (bernoulli_rows_large_subset_norm_small_ball p hp hpPos hHalf a S hS ht hLarge hτ z)

end CircularLaw
