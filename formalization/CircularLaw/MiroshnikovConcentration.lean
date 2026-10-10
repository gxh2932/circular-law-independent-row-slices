import CircularLaw.CubeMiroshnikov

/-!
# The planar Miroshnikov concentration estimate

This proves the full estimate used as Proposition 2.3 in LLTTY19: arbitrary
independent planar random variables, half-mass concentration at the base
radius, and the maximum single-summand concentration at exactly `sqrt(2)*r`.
The cube proof handles small maximum concentration; Esseen handles the
remaining case. Both branches concern the actual sum law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CircularLaw

theorem product_sum_miroshnikov_small_ball {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (hm : 1 ≤ Fintype.card ι) {r₀ r α : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (hHalf : ∀ i, planarConcentration (μ i) r₀ ≤ 1 / 2)
    (hBound : ∀ i, planarConcentration (μ i) (Real.sqrt 2 * r) ≤ α) (z : ℂ) :
    (productSumLaw μ).real (Metric.closedBall z r) ≤
      miroshnikovConstant * (r / r₀) * α / Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hrPos : 0 < r := hr₀.trans_le hr
  have hαNonneg : 0 ≤ α := (planarConcentration_nonneg
    (μ (Classical.arbitrary ι)) _).trans (hBound _)
  have hRatio : 1 ≤ r / r₀ := (one_le_div hr₀).mpr hr
  have hC : 0 ≤ miroshnikovConstant := by linarith [miroshnikovConstant_ge_two]
  by_cases hSmall : α < 1 / 2
  · have h := cube_sum_miroshnikov μ hm hrPos hSmall (fun i =>
      (cubeConcentration_le_planarConcentration (μ i) hrPos.le).trans (hBound i))
    have hBall := ((measureReal_mono (closedBall_subset_planarCube z r)).trans
      (probability_planarCube_le_concentration (productSumLaw μ) r z)).trans h
    apply hBall.trans
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg (Fintype.card ι : ℝ))
    have h := mul_le_mul_of_nonneg_right hRatio (mul_nonneg hC hαNonneg)
    convert h using 1 <;> ring
  · have hαHalf : 1 / 2 ≤ α := le_of_not_gt hSmall
    have hCE : 0 < 24 * Real.exp 1 / Real.pi := by positivity
    have hC4 : 4 * (24 * Real.exp 1 / Real.pi) ≤ miroshnikovConstant := by
      unfold miroshnikovConstant miroshnikovStepConstant
      linarith
    have hCoefficient : 2 * (24 * Real.exp 1 / Real.pi) ≤ miroshnikovConstant * α := by
      have h := mul_le_mul_of_nonneg_left hαHalf hC
      nlinarith
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCoefficient (by linarith : 0 ≤ r / r₀))
      (Real.sqrt_nonneg (Fintype.card ι : ℝ))
    exact (half_deficit_product_sum_small_ball μ hm hr₀ hr hHalf z).trans (by
      convert h using 1
      ring)

def maxPlanarConcentration {ι : Type*} [Fintype ι] (μ : ι → Measure ℂ) (r : ℝ) : ℝ :=
  ⨆ i, planarConcentration (μ i) r

theorem planarConcentration_le_max {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (r : ℝ) (i : ι) :
    planarConcentration (μ i) r ≤ maxPlanarConcentration μ r := by
  unfold maxPlanarConcentration
  have hBdd : BddAbove (Set.range (fun j => planarConcentration (μ j) r)) :=
    ⟨1, fun _ ⟨j, hj⟩ => hj ▸ planarConcentration_le_one (μ j) r⟩
  exact le_ciSup hBdd i

theorem maxPlanarConcentration_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (r : ℝ) :
    0 ≤ maxPlanarConcentration μ r :=
  (planarConcentration_nonneg (μ (Classical.arbitrary ι)) r).trans
    (planarConcentration_le_max μ r _)

theorem product_sum_miroshnikov_concentration {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (hm : 1 ≤ Fintype.card ι) {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (hHalf : ∀ i, planarConcentration (μ i) r₀ ≤ 1 / 2) :
    levyConcentration (productSumLaw μ) id r ≤ ENNReal.ofReal
      (miroshnikovConstant * (r / r₀) / Real.sqrt (Fintype.card ι : ℝ) *
        maxPlanarConcentration μ (Real.sqrt 2 * r)) := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hC : 0 ≤ miroshnikovConstant := by linarith [miroshnikovConstant_ge_two]
  have hMax := maxPlanarConcentration_nonneg μ (Real.sqrt 2 * r)
  have hrPos : 0 < r := hr₀.trans_le hr
  apply iSup_le
  intro z
  apply (ENNReal.le_ofReal_iff_toReal_le (by finiteness) (by
    positivity : 0 ≤ miroshnikovConstant * (r / r₀) / Real.sqrt (Fintype.card ι : ℝ) *
      maxPlanarConcentration μ (Real.sqrt 2 * r))).mpr
  have h := product_sum_miroshnikov_small_ball μ hm hr₀ hr hHalf
    (planarConcentration_le_max μ (Real.sqrt 2 * r)) z
  simpa only [Metric.closedBall, dist_eq_norm, id_eq, measureReal_def, div_mul_eq_mul_div]
    using h

theorem independent_sum_miroshnikov_concentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hm : 1 ≤ Fintype.card ι) {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (hHalf : ∀ i, levyConcentration μ (X i) r₀ ≤ ENNReal.ofReal (1 / 2)) :
    levyConcentration μ (fun ω => ∑ i, X i ω) r ≤ ENNReal.ofReal
      (miroshnikovConstant * (r / r₀) / Real.sqrt (Fintype.card ι : ℝ) *
        maxPlanarConcentration (fun i => μ.map (X i)) (Real.sqrt 2 * r)) := by
  haveI : ∀ i, IsProbabilityMeasure (μ.map (X i)) := fun i =>
    Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have hHalfMap : ∀ i, planarConcentration (μ.map (X i)) r₀ ≤ 1 / 2 := by
    intro i
    apply planarConcentration_le_of_bounds _ _ _ (by norm_num)
    intro z
    have h := (le_iSup (fun z : ℂ => μ {ω | ‖X i ω - z‖ ≤ r₀}) z).trans (hHalf i)
    rw [measureReal_def, Measure.map_apply (hX i) measurableSet_closedBall]
    simpa only [Metric.closedBall, dist_eq_norm, Set.preimage_setOf_eq,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  have h := product_sum_miroshnikov_concentration (fun i => μ.map (X i)) hm hr₀ hr hHalfMap
  apply iSup_le
  intro z
  have hBall := (le_iSup (fun z : ℂ => productSumLaw (fun i => μ.map (X i))
    {x | ‖id x - z‖ ≤ r}) z).trans h
  rw [productSumLaw_eq_independent_sum μ X hX hInd,
    Measure.map_apply (Finset.measurable_sum _ (fun i _ => hX i))
      (by simpa only [Metric.closedBall, dist_eq_norm, id_eq] using
        (measurableSet_closedBall : MeasurableSet (Metric.closedBall z r)))] at hBall
  exact hBall

def IndependentPlanarMiroshnikovLemma : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (m : ℕ), 1 ≤ m → ∀ (X : Fin m → Ω → ℂ),
    (∀ i, Measurable (X i)) → iIndepFun X μ → ∀ (r₀ r : ℝ),
    0 < r₀ → r₀ ≤ r →
    (∀ i, levyConcentration μ (X i) r₀ ≤ ENNReal.ofReal (1 / 2)) →
      levyConcentration μ (fun ω => ∑ i, X i ω) r ≤ ENNReal.ofReal
        (C * (r / r₀) / Real.sqrt (m : ℝ) *
          maxPlanarConcentration (fun i => μ.map (X i)) (Real.sqrt 2 * r))

theorem independent_planar_miroshnikov_lemma : IndependentPlanarMiroshnikovLemma := by
  refine ⟨miroshnikovConstant, by linarith [miroshnikovConstant_ge_two], ?_⟩
  intro Ω _ μ hμ m hm X hX hInd r₀ r hr₀ hr hHalf
  letI := hμ
  simpa only [Fintype.card_fin] using
    independent_sum_miroshnikov_concentration μ X hX hInd (by simpa using hm) hr₀ hr hHalf

end CircularLaw
