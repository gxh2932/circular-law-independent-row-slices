import CircularLaw.ComplexFiniteApproximation
import CircularLaw.GaussianTwoEventLimit

/-!
# Convex concentration for arbitrary bounded independent complex coordinates

Finite disk approximations preserve independence. Their uniform two-event
bounds pass through almost-sure limits, including closed thresholds and
atoms. The resulting median bound has constants `4` and `1/256`.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace CircularLaw

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

theorem convex_product_two_events (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    {K : ℝ} (hK : 0 < K) (hBound : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ K)
    {F : EuclideanSpace ℂ (Fin n) → ℝ} (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F)
    (s : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | F (complexCoordinateVector X ω) ≤ s} *
      μ.real {ω | s + t * K ≤ F (complexCoordinateVector X ω)} ≤ Real.exp (-t ^ 2 / 256) := by
  let f := fun ω => F (complexCoordinateVector X ω)
  let fseq := fun q ω => F (complexCoordinateVector
    (fun i v => boundedComplexApprox K hK.le q (X i v)) ω)
  have hf : Measurable f := hLip.continuous.measurable.comp (complexCoordinateVector_measurable hX)
  have hseq (q : ℕ) : Measurable (fseq q) := hLip.continuous.measurable.comp
    (complexCoordinateVector_measurable (fun i => (boundedComplexApprox K hK.le q).measurable.comp (hX i)))
  have hLimit : ∀ᵐ ω ∂μ, Tendsto (fun q => fseq q ω) atTop (𝓝 (f ω)) :=
    (boundedComplexApprox_vector_tendsto_ae μ X K hK.le hBound).mono
      (fun ω h => hLip.continuous.continuousAt.tendsto.comp h)
  have hApprox (q : ℕ) (s t : ℝ) (ht : 0 ≤ t) :
      μ.real {ω | fseq q ω ≤ s} * μ.real {ω | s + t * K ≤ fseq q ω} ≤ Real.exp (-t ^ 2 / 256) := by
    have h := talagrand_finite_independent_two_events μ
      (fun i ω => boundedComplexApproxLabel K hK.le q (X i ω))
      (fun i => (boundedComplexApproxLabel_measurable K hK.le q).comp (hX i))
      (boundedComplexApproxLabel_independent hInd K hK.le q)
      (fun z : BoundedComplexAlphabet K hK.le q => (z : ℂ)) hK
      (boundedComplexAlphabet_norm_le K hK.le q) hF hLip s ht
    simpa only [fseq, complexCoordinateVector, boundedComplexApproxLabel_coe] using h
  exact gaussian_closed_two_events_of_ae_limit μ hf hseq hLimit hK hApprox s ht

theorem gaussian_median_tail_of_two_events (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {K : ℝ}
    (hTwoEvents : ∀ s t : ℝ, 0 < t →
      μ.real {ω | f ω ≤ s} * μ.real {ω | s + t * K ≤ f ω} ≤ Real.exp (-t ^ 2 / 256))
    (m : ℝ) (hMedian : IsRealLawMedian μ f m) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t * K ≤ |f ω - m|} ≤ 4 * Real.exp (-t ^ 2 / 256) := by
  have hHigh : μ.real {ω | m + t * K ≤ f ω} ≤ 2 * Real.exp (-t ^ 2 / 256) := by
    have h := hTwoEvents m t ht
    nlinarith [mul_le_mul_of_nonneg_right hMedian.1
      (show 0 ≤ μ.real {ω | m + t * K ≤ f ω} from measureReal_nonneg)]
  have hLow : μ.real {ω | f ω ≤ m - t * K} ≤ 2 * Real.exp (-t ^ 2 / 256) := by
    have h := hTwoEvents (m - t * K) t ht
    simp only [sub_add_cancel] at h
    nlinarith [mul_le_mul_of_nonneg_left hMedian.2
      (show 0 ≤ μ.real {ω | f ω ≤ m - t * K} from measureReal_nonneg)]
  have hCover : {ω | t * K ≤ |f ω - m|} ⊆
      {ω | f ω ≤ m - t * K} ∪ {ω | m + t * K ≤ f ω} := by
    intro ω hω
    change t * K ≤ |f ω - m| at hω
    by_cases hSign : 0 ≤ f ω - m
    · right
      change m + t * K ≤ f ω
      rw [abs_of_nonneg hSign] at hω
      linarith
    · left
      change f ω ≤ m - t * K
      rw [abs_of_nonpos (le_of_not_ge hSign)] at hω
      linarith
  exact (measureReal_mono hCover).trans
    ((measureReal_union_le _ _).trans (by linarith))

theorem convex_product_median_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    {K : ℝ} (hK : 0 < K) (hBound : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ K)
    {F : EuclideanSpace ℂ (Fin n) → ℝ} (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F)
    (m : ℝ) (hMedian : IsRealLawMedian μ (fun ω => F (complexCoordinateVector X ω)) m)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t * K ≤ |F (complexCoordinateVector X ω) - m|} ≤ 4 * Real.exp (-t ^ 2 / 256) :=
  gaussian_median_tail_of_two_events μ (fun s _t ht => convex_product_two_events μ X hX hInd hK hBound hF hLip s ht)
    m hMedian ht

end CircularLaw
