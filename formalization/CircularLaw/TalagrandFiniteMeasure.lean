import CircularLaw.ConvexProductConcentration
import CircularLaw.BernoulliSliceConditioning

/-!
# The finite Talagrand theorem under actual product measures

Singleton masses supply the coordinate weights. Both the product
expectation and every event mass agree exactly with the measure-theoretic
law, so the checked median tail applies to genuine finite product laws.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CircularLaw

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}

omit [Fintype α] [MeasurableSingletonClass α] in
theorem finiteProductMeasure_singleton_real (ν : Fin n → Measure α) [∀ i, IsProbabilityMeasure (ν i)]
    (x : Fin n → α) :
    (Measure.pi ν).real {x} = finiteProductWeight (fun i a => (ν i).real {a}) x := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

theorem finiteProductMeasure_integral (ν : Fin n → Measure α) [∀ i, IsProbabilityMeasure (ν i)]
    (f : (Fin n → α) → ℝ) :
    (∫ x, f x ∂Measure.pi ν) = finiteProductExpectation (fun i a => (ν i).real {a}) f := by
  rw [integral_fintype f .of_finite]
  simp only [finiteProductMeasure_singleton_real, smul_eq_mul, finiteProductExpectation]

theorem finiteProductMeasure_event_real (ν : Fin n → Measure α) [∀ i, IsProbabilityMeasure (ν i)]
    (A : Set (Fin n → α)) :
    (Measure.pi ν).real A = finiteProductEventMass (fun i a => (ν i).real {a}) A := by
  have h := finiteMeasure_event_real (Measure.pi ν) (fun x => x ∈ A)
  simpa only [Set.setOf_mem_eq, finiteProductEventMass, finiteProductExpectation,
    finiteProductMeasure_singleton_real, mul_ite, mul_one, mul_zero] using h

theorem finiteMeasure_singleton_weights_normalized (ν : Measure α) [IsProbabilityMeasure ν] :
    ∑ a, ν.real {a} = 1 := by
  rw [sum_measureReal_singleton Finset.univ, Finset.coe_univ, probReal_univ]

theorem talagrand_finite_product_measure_moment (ν : Fin n → Measure α) [∀ i, IsProbabilityMeasure (ν i)]
    (A : Set (Fin n → α)) (hA : 0 < (Measure.pi ν).real A) :
    (∫ x, Real.exp (talagrandConvexDistance A x ^ 2 / 64) ∂Measure.pi ν) ≤
      1 / (Measure.pi ν).real A := by
  rw [finiteProductMeasure_integral, finiteProductMeasure_event_real]
  exact talagrand_finite_product_moment (fun _ _ => measureReal_nonneg)
    (fun i => finiteMeasure_singleton_weights_normalized (ν i)) A
      (by simpa only [finiteProductMeasure_event_real] using hA)

theorem talagrand_finite_product_measure_median_tail (ν : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (ν i)] (e : α → ℂ) {K : ℝ} (hK : 0 < K)
    (hBound : ∀ a, ‖e a‖ ≤ K) {F : EuclideanSpace ℂ (Fin n) → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F) (m : ℝ)
    (hMedian : IsRealLawMedian (Measure.pi ν)
      (fun x => F (WithLp.toLp 2 (talagrandCoordinateMap e x))) m)
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi ν).real {x | t * K ≤ |F (WithLp.toLp 2 (talagrandCoordinateMap e x)) - m|} ≤
      4 * Real.exp (-t ^ 2 / 256) := by
  rw [finiteProductMeasure_event_real]
  apply talagrand_finite_convex_median_tail (fun _ _ => measureReal_nonneg)
    (fun i => finiteMeasure_singleton_weights_normalized (ν i)) e hK hBound hF hLip m
  · simpa only [IsRealLawMedian, finiteProductMeasure_event_real] using hMedian.1
  · simpa only [IsRealLawMedian, finiteProductMeasure_event_real] using hMedian.2
  · exact ht

theorem talagrand_finite_product_measure_two_events (ν : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (ν i)] (e : α → ℂ) {K : ℝ} (hK : 0 < K)
    (hBound : ∀ a, ‖e a‖ ≤ K) {F : EuclideanSpace ℂ (Fin n) → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F) (s : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi ν).real {x | F (WithLp.toLp 2 (talagrandCoordinateMap e x)) ≤ s} *
      (Measure.pi ν).real {x | s + t * K ≤ F (WithLp.toLp 2 (talagrandCoordinateMap e x))} ≤
        Real.exp (-t ^ 2 / 256) := by
  simp only [finiteProductMeasure_event_real]
  exact talagrand_finite_convex_two_events (fun _ _ => measureReal_nonneg)
    (fun i => finiteMeasure_singleton_weights_normalized (ν i)) e hK hBound hF hLip s ht

end CircularLaw
