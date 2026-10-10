import CircularLaw.TalagrandFiniteMeasure

/-!
# Finite independent coordinates on arbitrary probability spaces

Independence supplies the exact joint product law. The finite Talagrand
bounds therefore apply to finite-valued measurable variables on any
probability space, with no product-law correspondence assumed.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory

namespace CircularLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {n : ℕ}

theorem finite_independent_joint_event_real (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → α) (hY : ∀ i, Measurable (Y i)) (hInd : iIndepFun Y μ)
    (A : Set (Fin n → α)) :
    (Measure.pi (fun i => μ.map (Y i))).real A = μ.real {ω | (fun i => Y i ω) ∈ A} := by
  have hJoint := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY i).aemeasurable)).mp hInd
  rw [← hJoint, map_measureReal_apply (measurable_pi_lambda _ hY) (Set.to_countable A).measurableSet]
  rfl

theorem talagrand_finite_independent_two_events (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → α) (hY : ∀ i, Measurable (Y i)) (hInd : iIndepFun Y μ)
    (e : α → ℂ) {K : ℝ} (hK : 0 < K) (hBound : ∀ a, ‖e a‖ ≤ K)
    {F : EuclideanSpace ℂ (Fin n) → ℝ} (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F)
    (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | F (WithLp.toLp 2 (fun i => e (Y i ω))) ≤ s} *
      μ.real {ω | s + t * K ≤ F (WithLp.toLp 2 (fun i => e (Y i ω)))} ≤
        Real.exp (-t ^ 2 / 256) := by
  haveI : ∀ i, IsProbabilityMeasure (μ.map (Y i)) := fun i =>
    Measure.isProbabilityMeasure_map (hY i).aemeasurable
  have h := talagrand_finite_product_measure_two_events (fun i => μ.map (Y i)) e hK hBound hF hLip s ht
  simpa only [finite_independent_joint_event_real μ Y hY hInd, talagrandCoordinateMap] using h

theorem talagrand_finite_independent_median_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → α) (hY : ∀ i, Measurable (Y i)) (hInd : iIndepFun Y μ)
    (e : α → ℂ) {K : ℝ} (hK : 0 < K) (hBound : ∀ a, ‖e a‖ ≤ K)
    {F : EuclideanSpace ℂ (Fin n) → ℝ} (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F)
    (m : ℝ) (hMedian : IsRealLawMedian μ (fun ω => F (WithLp.toLp 2 (fun i => e (Y i ω)))) m)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t * K ≤ |F (WithLp.toLp 2 (fun i => e (Y i ω))) - m|} ≤
      4 * Real.exp (-t ^ 2 / 256) := by
  haveI : ∀ i, IsProbabilityMeasure (μ.map (Y i)) := fun i =>
    Measure.isProbabilityMeasure_map (hY i).aemeasurable
  have hMedianPi : IsRealLawMedian (Measure.pi (fun i => μ.map (Y i)))
      (fun x => F (WithLp.toLp 2 (talagrandCoordinateMap e x))) m := by
    simpa only [IsRealLawMedian, finite_independent_joint_event_real μ Y hY hInd,
      talagrandCoordinateMap] using hMedian
  have h := talagrand_finite_product_measure_median_tail (fun i => μ.map (Y i))
    e hK hBound hF hLip m hMedianPi ht
  simpa only [finite_independent_joint_event_real μ Y hY hInd, talagrandCoordinateMap] using h

end CircularLaw
