import CircularLaw.TruncatedGaussianMixture

/-!
# The planar Esseen concentration estimate

The Gaussian, weighted-Jensen, and periodic-cosine bounds give an estimate
for the actual sum of arbitrary independent planar laws. Truncated moments
are computed from those laws and then bounded below by concentration deficits.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CircularLaw

def totalSymmetrizedLaw {ι : Type*} [Fintype ι] (μ : ι → Measure ℂ) : Measure ℂ :=
  ∑ i, symmetrizedLaw (μ i)

instance totalSymmetrizedLaw_finite {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] :
    IsFiniteMeasure (totalSymmetrizedLaw μ) := by
  unfold totalSymmetrizedLaw
  infer_instance

theorem totalSymmetrizedLaw_cosineAverage {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (t : ℂ) :
    cosineAverage (totalSymmetrizedLaw μ) t = sumCharDefect μ t := by
  rw [cosineAverage, totalSymmetrizedLaw,
    integral_finset_sum_measure (fun i _ => integrable_inner_cos_defect (symmetrizedLaw (μ i)) t)]
  simp only [sumCharDefect, ← charFun_sq_defect_integral]

theorem totalSymmetrizedLaw_truncatedMoment {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) :
    (∫ v, truncatedNormSq r₀ v ∂totalSymmetrizedLaw μ) =
      ∑ i, truncatedSymmetrizedMoment (μ i) r₀ := by
  rw [totalSymmetrizedLaw,
    integral_finset_sum_measure (fun i _ => truncatedNormSq_integrable (symmetrizedLaw (μ i)) hr₀)]
  rfl

theorem product_sum_small_ball_le_truncated_moment {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (hA : 0 < ∑ i, truncatedSymmetrizedMoment (μ i) r₀) (z : ℂ) :
    (productSumLaw μ).real (Metric.closedBall z r) ≤
      (24 * Real.exp 1 / Real.pi) * r /
        Real.sqrt (∑ i, truncatedSymmetrizedMoment (μ i) r₀) := by
  have hrPos : 0 < r := hr₀.trans_le hr
  have hInt := truncated_gaussian_mixture_integral_le (totalSymmetrizedLaw μ) hr₀ hr
    (by rwa [totalSymmetrizedLaw_truncatedMoment μ hr₀.le])
  simp_rw [totalSymmetrizedLaw_cosineAverage, totalSymmetrizedLaw_truncatedMoment μ hr₀.le] at hInt
  have h := (gaussian_product_sum_small_ball μ hrPos z).trans
    (mul_le_mul_of_nonneg_left hInt (by positivity : 0 ≤ Real.exp 1 * (r ^ 2 / (4 * Real.pi))))
  convert h using 1
  field_simp
  ring

def sumConcentrationDeficit {ι : Type*} [Fintype ι] (μ : ι → Measure ℂ) (r₀ : ℝ) : ℝ :=
  ∑ i, (1 - planarConcentration (μ i) r₀)

theorem sumConcentrationDeficit_nonneg {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (r₀ : ℝ) :
    0 ≤ sumConcentrationDeficit μ r₀ :=
  Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (planarConcentration_le_one (μ i) r₀))

theorem product_sum_esseen_small_ball {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (hD : 0 < sumConcentrationDeficit μ r₀) (z : ℂ) :
    (productSumLaw μ).real (Metric.closedBall z r) ≤
      (24 * Real.exp 1 / Real.pi) * (r / r₀) /
        Real.sqrt (sumConcentrationDeficit μ r₀) := by
  have hrPos : 0 < r := hr₀.trans_le hr
  let A := ∑ i, truncatedSymmetrizedMoment (μ i) r₀
  have hLower : r₀ ^ 2 * sumConcentrationDeficit μ r₀ ≤ A :=
    sum_concentration_deficits_le_truncated_symmetrized_moments μ hr₀.le
  have hPos : 0 < A := lt_of_lt_of_le (mul_pos (sq_pos_of_pos hr₀) hD) hLower
  have hSqrt : r₀ * Real.sqrt (sumConcentrationDeficit μ r₀) ≤ Real.sqrt A := by
    have h := Real.sqrt_le_sqrt hLower
    rwa [Real.sqrt_mul (sq_nonneg r₀), Real.sqrt_sq hr₀.le] at h
  have h := (product_sum_small_ball_le_truncated_moment μ hr₀ hr hPos z).trans
    (div_le_div_of_nonneg_left (by positivity : 0 ≤ (24 * Real.exp 1 / Real.pi) * r)
      (by positivity : 0 < r₀ * Real.sqrt (sumConcentrationDeficit μ r₀)) hSqrt)
  convert h using 1
  ring

theorem product_sum_esseen_concentration {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r) :
    levyConcentration (productSumLaw μ) id r ≤
      ENNReal.ofReal ((24 * Real.exp 1 / Real.pi) * (r / r₀) ^ 2) /
        ENNReal.ofReal (Real.sqrt (sumConcentrationDeficit μ r₀)) := by
  have hrPos : 0 < r := hr₀.trans_le hr
  have hC : 0 < 24 * Real.exp 1 / Real.pi := by positivity
  have hRatio : 1 ≤ r / r₀ := (one_le_div hr₀).mpr hr
  rcases (sumConcentrationDeficit_nonneg μ r₀).eq_or_lt with hD | hD
  · rw [← hD, Real.sqrt_zero, ENNReal.ofReal_zero,
      ENNReal.div_zero (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))]
    exact le_top
  · rw [← ENNReal.ofReal_div_of_pos (Real.sqrt_pos.mpr hD)]
    apply iSup_le
    intro z
    apply (ENNReal.le_ofReal_iff_toReal_le (by finiteness) (by positivity)).mpr
    have h := product_sum_esseen_small_ball μ hr₀ hr hD z
    have hPower : r / r₀ ≤ (r / r₀) ^ 2 := by nlinarith
    have hBound := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPower hC.le)
      (Real.sqrt_nonneg (sumConcentrationDeficit μ r₀))
    simpa only [Metric.closedBall, dist_eq_norm, id_eq, measureReal_def] using h.trans hBound

theorem independent_sum_esseen_concentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r) :
    levyConcentration μ (fun ω => ∑ i, X i ω) r ≤
      ENNReal.ofReal ((24 * Real.exp 1 / Real.pi) * (r / r₀) ^ 2) /
        ENNReal.ofReal (Real.sqrt (sumConcentrationDeficit (fun i => μ.map (X i)) r₀)) := by
  haveI : ∀ i, IsProbabilityMeasure (μ.map (X i)) := fun i =>
    Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have h := product_sum_esseen_concentration (fun i => μ.map (X i)) hr₀ hr
  apply iSup_le
  intro z
  have hBall := (le_iSup (fun z : ℂ => productSumLaw (fun i => μ.map (X i))
    {x | ‖id x - z‖ ≤ r}) z).trans h
  rw [productSumLaw_eq_independent_sum μ X hX hInd,
    Measure.map_apply (Finset.measurable_sum _ (fun i _ => hX i))
      (by simpa only [Metric.closedBall, dist_eq_norm, id_eq] using
        (measurableSet_closedBall : MeasurableSet (Metric.closedBall z r)))] at hBall
  exact hBall

def IndependentPlanarEsseenLemma : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (m : ℕ), 1 ≤ m → ∀ (X : Fin m → Ω → ℂ),
    (∀ i, Measurable (X i)) → iIndepFun X μ → ∀ (r₀ r : ℝ),
    0 < r₀ → r₀ ≤ r →
      levyConcentration μ (fun ω => ∑ i, X i ω) r ≤
        ENNReal.ofReal (C * (r / r₀) ^ 2) /
          ENNReal.ofReal (Real.sqrt (sumConcentrationDeficit (fun i => μ.map (X i)) r₀))

theorem independent_planar_esseen_lemma : IndependentPlanarEsseenLemma := by
  refine ⟨24 * Real.exp 1 / Real.pi, by positivity, ?_⟩
  intro Ω _ μ hμ m _ X hX hInd r₀ r hr₀ hr
  letI := hμ
  exact independent_sum_esseen_concentration μ X hX hInd hr₀ hr

end CircularLaw
