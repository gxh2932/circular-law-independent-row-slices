import CircularLaw.SeparatedLaw

/-!
# Concentration of an independent separated planar sum

Uniform disk smoothing and the bounded-density sum theorem prove the
discrete concentration estimate of LLTTY19 Proposition 2.5. The proof
uses second moments in place of the source's Hoeffding step, with a
larger universal constant. No sum-concentration estimate is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CircularLaw

theorem discrete_smoothing_arithmetic {m : ℕ} (hm : 1 ≤ m)
    {δ u t : ℝ} (hδ : 0 < δ) (hu : 0 < u) :
    (4 / 3 : ℝ) * ((200 * (u / ((δ / 3) ^ 2 * Real.pi)) / (m : ℝ)) *
        ((t + 2 * Real.sqrt (m : ℝ) * (δ / 3)) ^ 2 * Real.pi)) ≤
      10000 * max (u * t ^ 2 / ((m : ℝ) * δ ^ 2)) u := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hs := Real.sq_sqrt hmR.le
  have hCross : (t + 2 * Real.sqrt (m : ℝ) * (δ / 3)) ^ 2 ≤
      2 * t ^ 2 + 8 * (m : ℝ) * (δ / 3) ^ 2 := by
    nlinarith [sq_nonneg (t - 2 * Real.sqrt (m : ℝ) * (δ / 3))]
  have hCoeff : 0 ≤ (4 / 3 : ℝ) * (200 * (u / ((δ / 3) ^ 2 * Real.pi)) / (m : ℝ)) := by
    positivity
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hCross Real.pi_pos.le) hCoeff
  have hEq : (4 / 3 : ℝ) * (200 * (u / ((δ / 3) ^ 2 * Real.pi)) / (m : ℝ)) *
      ((2 * t ^ 2 + 8 * (m : ℝ) * (δ / 3) ^ 2) * Real.pi) =
        4800 * (u * t ^ 2 / ((m : ℝ) * δ ^ 2)) + (6400 / 3 : ℝ) * u := by
    field_simp
    ring
  rw [hEq] at h
  have h1 := le_max_left (u * t ^ 2 / ((m : ℝ) * δ ^ 2)) u
  have h2 := le_max_right (u * t ^ 2 / ((m : ℝ) * δ ^ 2)) u
  have hMax : 0 ≤ max (u * t ^ 2 / ((m : ℝ) * δ ^ 2)) u := hu.le.trans h2
  nlinarith

theorem separated_planar_sum_small_ball {m : ℕ} (hm : 1 ≤ m)
    (μ : Fin m → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {δ u t : ℝ} (hδ : 0 < δ) (hu : 0 < u) (ht : 0 ≤ t)
    (hLaw : ∀ i, SeparatedPlanarLaw (μ i) δ u) (z : ℂ) :
    productSumLaw μ (Metric.closedBall z t) ≤
      ENNReal.ofReal (10000 * max (u * t ^ 2 / ((m : ℝ) * δ ^ 2)) u) := by
  have hBall : ∀ i z, μ i (Metric.closedBall z (δ / 3)) ≤ ENNReal.ofReal u :=
    fun i z => separated_planar_law_small_ball (hLaw i) (by linarith) z
  exact (planarDisk_smoothed_sum_small_ball μ hm (by positivity : 0 < δ / 3) hu ht hBall z).trans
    (ENNReal.ofReal_le_ofReal (discrete_smoothing_arithmetic hm hδ hu))

theorem separated_planar_independent_sum_small_ball {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    (X : Fin m → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    {δ u t : ℝ} (hδ : 0 < δ) (hu : 0 < u) (ht : 0 ≤ t)
    (hLaw : ∀ i, SeparatedPlanarLaw (μ.map (X i)) δ u) (z : ℂ) :
    μ {ω | ‖(∑ i, X i ω) - z‖ ≤ t} ≤
      ENNReal.ofReal (10000 * max (u * t ^ 2 / ((m : ℝ) * δ ^ 2)) u) := by
  haveI : ∀ i, IsProbabilityMeasure (μ.map (X i)) := fun i =>
    Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have hJoint := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mp hInd
  have hSum : productSumLaw (fun i => μ.map (X i)) = μ.map (fun ω => ∑ i, X i ω) := by
    rw [productSumLaw, ← hJoint, Measure.map_map measurable_finite_sum
      (measurable_pi_lambda _ hX)]
    rfl
  have h := separated_planar_sum_small_ball hm (fun i => μ.map (X i)) hδ hu ht hLaw z
  rw [hSum, Measure.map_apply (Finset.measurable_sum _ (fun i _ => hX i))
    measurableSet_closedBall] at h
  simpa only [Set.preimage, Metric.mem_closedBall, dist_eq_norm] using h

theorem separated_planar_independent_sum_concentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    (X : Fin m → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    {δ u t : ℝ} (hδ : 0 < δ) (hu : 0 < u) (ht : 0 ≤ t)
    (hLaw : ∀ i, SeparatedPlanarLaw (μ.map (X i)) δ u) :
    levyConcentration μ (fun ω => ∑ i, X i ω) t ≤
      ENNReal.ofReal (10000 * max (u * t ^ 2 / ((m : ℝ) * δ ^ 2)) u) := by
  apply iSup_le
  intro z
  exact separated_planar_independent_sum_small_ball μ hm X hX hInd hδ hu ht hLaw z

def IndependentPlanarDiscreteLemma : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (m : ℕ), 1 ≤ m → ∀ (X : Fin m → Ω → ℂ),
    (∀ i, Measurable (X i)) → iIndepFun X μ → ∀ (δ u t : ℝ),
    0 < δ → 0 < u → 0 ≤ t → (∀ i, SeparatedPlanarLaw (μ.map (X i)) δ u) →
      levyConcentration μ (fun ω => ∑ i, X i ω) t ≤
        ENNReal.ofReal (C * max (u * t ^ 2 / ((m : ℝ) * δ ^ 2)) u)

theorem independent_planar_discrete_lemma : IndependentPlanarDiscreteLemma := by
  refine ⟨10000, by norm_num, ?_⟩
  intro Ω _ μ hμ m hm X hX hInd δ u t hδ hu ht hLaw
  letI := hμ
  exact separated_planar_independent_sum_concentration μ hm X hX hInd hδ hu ht hLaw

end CircularLaw
