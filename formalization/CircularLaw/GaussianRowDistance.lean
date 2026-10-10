import CircularLaw.FreshRowGaussianProbability
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# From the actual Gaussian row form to leave-one-row-out distance

The projected row norm is the metric distance to the subspace. The actual
complex Gaussian form has that norm as its scale; if the distance is at
most the radius, its small-ball probability is at least one half. Averaging
this implication bounds the actual row-slice distance probability.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped BigOperators InnerProductSpace

namespace CircularLaw

theorem orthogonalProjection_norm_eq_infDist {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : EuclideanSpace ℂ (Fin n)) :
    ‖Eᗮ.starProjection v‖ = Metric.infDist v (E : Set (EuclideanSpace ℂ (Fin n))) := by
  rw [Submodule.starProjection_orthogonal]
  change ‖v - E.starProjection v‖ = _
  rw [Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

theorem standardComplexGaussian_unit_ball_half :
    (1 / 2 : ℝ) ≤ standardComplexGaussianLaw.real {z : ℂ | ‖z‖ ≤ 1} := by
  have hMeas : MeasurableSet {z : ℂ | ‖z‖ ≤ 1} := (isClosed_le continuous_norm continuous_const).measurableSet
  have hCompl := measureReal_compl (μ := standardComplexGaussianLaw) hMeas
  have hSet : {z : ℂ | ‖z‖ ≤ 1}ᶜ = {z : ℂ | 1 < ‖z‖} := by ext z; simp
  rw [hSet, standardComplexGaussianLaw_strict_radial_tail (by norm_num), probReal_univ] at hCompl
  have hExp : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hInv : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hExp
  norm_num only [one_pow] at hCompl
  linarith

theorem projectedGaussian_inner_small_ball_half {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : EuclideanSpace ℂ (Fin n))
    {r : ℝ} (hDistance : ‖Eᗮ.starProjection v‖ ≤ r) :
    (1 / 2 : ℝ) ≤ (standardComplexGaussianVectorLaw n).real
      {z | ‖⟪v, projectedComplexGaussian E z⟫_ℂ‖ ≤ r} := by
  let σ := ‖Eᗮ.starProjection v‖
  let S := σ • ContinuousLinearMap.id ℝ ℂ
  have hMeas : Measurable (fun z => ⟪v, projectedComplexGaussian E z⟫_ℂ) :=
    ((innerSL ℂ v).continuous.comp (projectedComplexGaussian_continuous E)).measurable
  have hBall : MeasurableSet {w : ℂ | ‖w‖ ≤ r} := (isClosed_le continuous_norm continuous_const).measurableSet
  have hLaw := projectedComplexGaussian_inner_law E v
  have hLeft := map_measureReal_apply (μ := standardComplexGaussianVectorLaw n) hMeas hBall
  have hRight := map_measureReal_apply (μ := standardComplexGaussianLaw) S.continuous.measurable hBall
  have hEq : (standardComplexGaussianVectorLaw n).real {z | ‖⟪v, projectedComplexGaussian E z⟫_ℂ‖ ≤ r} =
      standardComplexGaussianLaw.real {w : ℂ | ‖S w‖ ≤ r} := by
    simp only [Set.preimage_setOf_eq] at hLeft hRight
    rw [← hLeft, hLaw]
    exact hRight
  rw [hEq]
  apply standardComplexGaussian_unit_ball_half.trans
  have hSubset : {w : ℂ | ‖w‖ ≤ 1} ⊆ {w : ℂ | ‖S w‖ ≤ r} := by
    intro w hw
    change ‖σ • w‖ ≤ r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans (by simpa only [mul_one] using hDistance)
  exact measureReal_mono hSubset (measure_ne_top _ _)

def shiftedConjugateRow {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) :
    EuclideanSpace ℂ (Fin n) :=
  retainedConjugateRow Finset.univ ζ rows ⟨i, Finset.mem_univ i⟩

theorem shiftedConjugateRow_gaussian_inner {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin n) (z : Fin n → ℂ) :
    ⟪shiftedConjugateRow ζ rows i,
      projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z⟫_ℂ =
        enlargedRetainedGaussianRowForm I ζ rows i z := by
  have h := retainedConjugateRow_inner Finset.univ ζ rows ⟨i, Finset.mem_univ i⟩
    (fun j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j)
  rw [retainedShiftedMatrix_mulVec] at h
  exact h

def retainedShiftedRowDistance {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin n) : ℝ :=
  Metric.infDist (shiftedConjugateRow ζ rows i)
    (retainedRowSpan I ζ rows : Set (EuclideanSpace ℂ (Fin n)))

theorem retainedShiftedRowDistance_gaussian_implication {n d : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n)
    {r : ℝ} (hDistance : retainedShiftedRowDistance I ζ rows i ≤ r) :
    (1 / 2 : ℝ) ≤ (standardComplexGaussianVectorLaw n).real
      {z | ‖enlargedRetainedGaussianRowForm I ζ rows i z‖ ≤ r} := by
  have hOriginal : ‖(retainedRowSpan I ζ rows)ᗮ.starProjection (shiftedConjugateRow ζ rows i)‖ ≤ r := by
    rw [orthogonalProjection_norm_eq_infDist]
    exact hDistance
  have hEnlarged := (orthogonalProjection_norm_mono (retainedRowSpan_le_enlarged I ζ rows)
    (shiftedConjugateRow ζ rows i)).trans hOriginal
  simpa only [shiftedConjugateRow_gaussian_inner] using
    projectedGaussian_inner_small_ball_half (enlargedRetainedRowSpan I ζ rows)
      (shiftedConjugateRow ζ rows i) hEnlarged

theorem retainedShiftedRowDistance_probability_le_gaussian {n d : ℕ}
    (hdn : d ≤ n) (I : Finset (Fin n)) (ζ : ℂ) (i : Fin n) (r : ℝ) :
    uniformProbability (fun rows : RowSliceMatrix n d => retainedShiftedRowDistance I ζ rows i ≤ r) ≤
      2 * ((rowSliceMatrixLaw n d).prod (standardComplexGaussianVectorLaw n)).real
        {p | ‖enlargedRetainedGaussianRowForm I ζ p.1 i p.2‖ ≤ r} := by
  haveI := rowSlice_nonempty hdn
  have hEventMeas : MeasurableSet {p : RowSliceMatrix n d × (Fin n → ℂ) |
      ‖enlargedRetainedGaussianRowForm I ζ p.1 i p.2‖ ≤ r} := by
    have hForm : Measurable (fun p : RowSliceMatrix n d × (Fin n → ℂ) =>
        enlargedRetainedGaussianRowForm I ζ p.1 i p.2) :=
      measurable_from_prod_countable_right (fun rows =>
        (enlargedRetainedGaussianRowForm_continuous I ζ rows i).measurable)
    exact measurableSet_le hForm.norm measurable_const
  rw [rowSliceMatrixLaw, finiteGaussian_product_event_real _ _ hEventMeas]
  have h := finiteMean_mono (f := fun rows : RowSliceMatrix n d =>
      (1 / 2 : ℝ) * if retainedShiftedRowDistance I ζ rows i ≤ r then 1 else 0)
    (g := fun rows => (standardComplexGaussianVectorLaw n).real
      {z | ‖enlargedRetainedGaussianRowForm I ζ rows i z‖ ≤ r}) (by
      intro rows
      by_cases hDist : retainedShiftedRowDistance I ζ rows i ≤ r
      · simpa only [hDist, if_true, mul_one] using
          retainedShiftedRowDistance_gaussian_implication I ζ rows i hDist
      · simp only [hDist, if_false, mul_zero]
        exact measureReal_nonneg)
  rw [finiteMean_const_mul, finiteMean_indicator] at h
  simp only [Set.mem_setOf_eq]
  linarith

theorem retainedShiftedRowDistance_probability_le_averaged_concentration {n d : ℕ}
    (hdn : d ≤ n) (I : Finset (Fin n)) (ζ : ℂ) (i : Fin n) (hi : i ∉ I) (r : ℝ) :
    uniformProbability (fun rows : RowSliceMatrix n d => retainedShiftedRowDistance I ζ rows i ≤ r) ≤
      2 * finiteMean (fun rows : RowSliceMatrix n d => ∫ z,
        rowSliceDiskConcentration (d := d)
          (fun j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j) r
        ∂standardComplexGaussianVectorLaw n) :=
  (retainedShiftedRowDistance_probability_le_gaussian hdn I ζ i r).trans
    (mul_le_mul_of_nonneg_left
      (actual_omitted_row_gaussian_probability_le_averaged_concentration hdn I ζ i hi r) (by norm_num))

def LeaveOneOutRowDistanceTheorem : Prop :=
  ∃ Cstar R : ℝ, 0 < Cstar ∧ 0 < R ∧
    ∀ C : ℝ, Cstar ≤ C → ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
        ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
          ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d → ∀ i : Fin n, i ∉ I →
            uniformProbability (fun rows : RowSliceMatrix n d =>
              retainedShiftedRowDistance I ζ rows i ≤
                Real.exp (-R * Real.rpow (d : ℝ) (1 / 96))) ≤
              R / (d : ℝ) ^ 3 + R / n

theorem leave_one_out_row_distance_theorem : LeaveOneOutRowDistanceTheorem := by
  obtain ⟨Cstar, R, hCstar, hR, hSmall⟩ := actual_omitted_row_gaussian_small_ball_uniform
  refine ⟨Cstar, 2 * R, hCstar, mul_pos (by norm_num) hR, ?_⟩
  intro C hC σ Z₀ hσ0 hσ1
  obtain ⟨NS, hNS⟩ := hSmall C hC σ Z₀ hσ0 hσ1
  obtain ⟨NP, hNP⟩ := eventually_atTop.mp
    (eventually_fresh_row_gaussian_parameters (hCstar.trans_le hC) hσ1.le)
  refine ⟨max NS NP, ?_⟩
  intro n hn d hBand L hL I hI ζ hShift i hi
  have hnS : NS ≤ n := (le_max_left _ _).trans hn
  have hnP : NP ≤ n := (le_max_right _ _).trans hn
  have hHalf := (hNP n hnP d hBand).2.2.1
  have hRadius : Real.exp (-(2 * R) * Real.rpow (d : ℝ) (1 / 96)) ≤
      Real.exp (-R * Real.rpow (d : ℝ) (1 / 96)) := by
    apply Real.exp_le_exp.mpr
    have hPower := Real.rpow_nonneg (Nat.cast_nonneg d) (1 / 96 : ℝ)
    simp only [Real.rpow_eq_pow]
    nlinarith
  calc
    _ ≤ uniformProbability (fun rows : RowSliceMatrix n d =>
        retainedShiftedRowDistance I ζ rows i ≤
          Real.exp (-R * Real.rpow (d : ℝ) (1 / 96))) :=
      uniformProbability_mono (fun rows h => h.trans hRadius)
    _ ≤ 2 * ((rowSliceMatrixLaw n d).prod (standardComplexGaussianVectorLaw n)).real
        {p | ‖enlargedRetainedGaussianRowForm I ζ p.1 i p.2‖ ≤
          Real.exp (-R * Real.rpow (d : ℝ) (1 / 96))} :=
      retainedShiftedRowDistance_probability_le_gaussian (by omega : d ≤ n) I ζ i _
    _ ≤ 2 * (R / (d : ℝ) ^ 3 + R / n) :=
      mul_le_mul_of_nonneg_left (hNS n hnS d hBand L hL I hI ζ hShift i hi) (by norm_num)
    _ = _ := by ring

end CircularLaw
