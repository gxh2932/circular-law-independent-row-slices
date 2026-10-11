import CircularLaw.BernoulliRowsSliceConditioning
import CircularLaw.WeightedBernoulliSmallBall
import CircularLaw.FiniteLawTransport

/-!
# Small balls for the adjoint contribution of selected rows

Only the selected rows pay the Bernoulli conditioning cost. Column
independence is used in the Bernoulli comparator, whose law is proved
by transposing the product sample. The final bound concerns exact slices.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace CircularLaw

theorem bernoulli_rows_columns_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0) (hp : p ≤ 1) :
    (Measure.pi (fun _ : ι => bernoulliCubeLaw κ p hp)).map
      (Function.swap : (ι → κ → Bool) → κ → ι → Bool) =
        Measure.pi (fun _ : κ => bernoulliCubeLaw ι p hp) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x)]
  have hPre : (Function.swap : (ι → κ → Bool) → κ → ι → Bool) ⁻¹' {x} = {Function.swap x} := by
    ext y
    constructor
    · intro h
      have hEq : Function.swap y = x := h
      exact congrArg Function.swap hEq
    · intro h
      have hEq : y = Function.swap x := h
      rw [hEq]
      rfl
  rw [hPre]
  simp only [Measure.pi_singleton, bernoulliCubeLaw, Function.swap]
  exact Finset.prod_comm

theorem bernoulli_columns_weighted_norm_small_ball {ι : Type*} [Fintype ι] {n : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (a : ι → ℂ) (S : Finset ι) (hS : S.Nonempty) {t τ : ℝ} (ht : 0 < t)
    (hLarge : ∀ i ∈ S, t ≤ ‖a i‖) (hτ : 1 ≤ τ) (z : Fin n → ℂ) :
    (Measure.pi (fun _ : Fin n => bernoulliCubeLaw ι p hp)).real
      {x | (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (x j i)) - z j‖ ^ 2) ≤
        τ ^ 2 * t ^ 2 * n} ≤
      (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant / Real.sqrt ((S.card : ℝ) * p)) * τ ^ 2) ^ n := by
  let ν := bernoulliCubeLaw ι p hp
  let μ := Measure.pi (fun _ : Fin n => ν)
  let f := fun x : ι → Bool => ∑ i, weightedBernoulliValue (a i) (x i)
  let A := bernoulliScalarSmallBallConstant / Real.sqrt ((S.card : ℝ) * p)
  have hA : 0 ≤ A := div_nonneg bernoulli_scalar_small_ball_constant_pos.le (Real.sqrt_nonneg _)
  apply tensorization μ (fun j x => f (x j)) (fun _ => measurable_of_countable _)
    (iIndepFun_pi (fun _ => (measurable_of_countable f).aemeasurable)) ht.le hA hτ
  intro j σ hσ
  apply iSup_le
  intro c
  apply (ENNReal.le_ofReal_iff_toReal_le (by finiteness) (mul_nonneg hA (sq_nonneg σ))).mpr
  change μ.real {x | ‖f (x j) - c‖ ≤ σ * t} ≤ A * σ ^ 2
  have hMarginal := (measurePreserving_eval (fun _ : Fin n => ν) j).map_eq
  have hLaw := finite_law_event_real (measurable_pi_apply j) hMarginal
    (fun x : ι → Bool => ‖f x - c‖ ≤ σ * t)
  rw [hLaw]
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

theorem row_slice_selected_rows_adjoint_small_ball {ι : Type*} [Fintype ι] {n d : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n)
    (a : ι → ℂ) (S : Finset ι) (hS : S.Nonempty) {t τ : ℝ} (ht : 0 < t)
    (hLarge : ∀ i ∈ S, t ≤ ‖a i‖) (hτ : 1 ≤ τ) (z : Fin n → ℂ) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      (∑ j, ‖(∑ i, rowEntry (rows i) j * a i) - z j‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * n) ≤
      (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ Fintype.card ι *
        (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
          Real.sqrt ((S.card : ℝ) * ((d : ℝ) / n))) * τ ^ 2) ^ n := by
  have hn : 0 < n := by omega
  let p := rowBernoulliParameter n d
  let hp := rowBernoulliParameter_le_one hn (show d ≤ n by omega)
  have hpPos : 0 < (p : ℝ) := by
    rw [show (p : ℝ) = (d : ℝ) / n from rowBernoulliParameter_coe n d]
    positivity
  have hHalf : (p : ℝ) ≤ 1 / 2 := by
    rw [show (p : ℝ) = (d : ℝ) / n from rowBernoulliParameter_coe n d]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr
    have hDegreeR : 2 * (d : ℝ) ≤ n := by exact_mod_cast hDegree
    linarith
  let E := fun x : ι → Fin n → Bool =>
    (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (x i j)) - z j‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * n
  have hTransfer := bernoulli_rows_slice_event_transfer_sqrt (ι := ι) hd (by omega : d ≤ n) E
  have hEntry : ∀ (s : RowSlice n d) (j : Fin n) (v : ℂ),
      weightedBernoulliValue v (rowSliceBoolRow s j) = rowEntry s j * v := by
    intro s j v
    by_cases hj : j ∈ s.val <;> simp [weightedBernoulliValue, rowSliceBoolRow, rowEntry, hj]
  simp only [E, hEntry] at hTransfer
  apply hTransfer.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hMap := bernoulli_rows_columns_map (ι := ι) (κ := Fin n) p hp
  have hEvent := finite_law_event_real (measurable_of_countable Function.swap) hMap
    (fun x : Fin n → ι → Bool =>
      (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (x j i)) - z j‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * n)
  rw [hEvent]
  simpa only [rowBernoulliParameter_coe] using
    bernoulli_columns_weighted_norm_small_ball p hp hpPos hHalf a S hS ht hLarge hτ z

end CircularLaw
