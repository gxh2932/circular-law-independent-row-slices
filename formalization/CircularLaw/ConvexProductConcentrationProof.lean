import CircularLaw.GaussianMedianMean

/-!
# Complete manuscript convex product concentration theorem

Both centers have a common absolute pair of constants. The proof includes
the Talagrand finite product argument, approximation for general complex
laws, and integration and recentering, with no imported concentration
result assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace CircularLaw

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

theorem convex_product_mean_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    {K : ℝ} (hK : 0 < K) (hBound : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ K)
    {F : EuclideanSpace ℂ (Fin n) → ℝ} (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F)
    (m : ℝ) (hMedian : IsRealLawMedian μ (fun ω => F (complexCoordinateVector X ω)) m)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t * K ≤ |F (complexCoordinateVector X ω) -
      (∫ v, F (complexCoordinateVector X v) ∂μ)|} ≤
      (4 * Real.exp 16) * Real.exp (-(1 / 1024) * t ^ 2) :=
  gaussian_mean_tail_of_median_tail μ
    (hLip.continuous.measurable.comp (complexCoordinateVector_measurable hX)) hK m
    (fun _t ht => convex_product_median_tail μ X hX hInd hK hBound hF hLip m hMedian ht) ht

theorem convex_product_concentration_lemma : ConvexProductConcentrationLemma := by
  refine ⟨1 / 1024, 4 * Real.exp 16, by norm_num, by positivity, ?_⟩
  intro Ω _ μ hμ n X hX hInd K hK hBound F hF hLip m hMedian t ht
  letI := hμ
  refine ⟨?_, convex_product_mean_tail μ X hX hInd hK hBound hF hLip m hMedian ht⟩
  have h := convex_product_median_tail μ X hX hInd hK hBound hF hLip m hMedian ht
  apply h.trans
  have hExponent : -t ^ 2 / 256 ≤ -(1 / 1024) * t ^ 2 := by nlinarith [sq_nonneg t]
  have hExp := Real.exp_le_exp.mpr hExponent
  have hConst : 1 ≤ Real.exp (16 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  nlinarith [Real.exp_pos (-(1 / 1024) * t ^ 2)]

end CircularLaw
