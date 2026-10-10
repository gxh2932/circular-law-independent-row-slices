import CircularLaw.PlanarSumDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Scaling the planar sum-density bound

The unit-density theorem applies to laws dominated by any positive
multiple of area after a real dilation. The dilation, product law,
inverse dilation, and area factors are checked explicitly.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace CircularLaw

theorem planar_volume_map_smul {a : ℝ} (ha : a ≠ 0) :
    volume.map (fun x : ℂ => a • x) = ENNReal.ofReal ((a ^ 2)⁻¹) • volume := by
  simpa only [Complex.finrank_real_complex, abs_inv, abs_of_nonneg (sq_nonneg a)] using
    Measure.map_addHaar_smul (volume : Measure ℂ) ha

theorem productSumLaw_map_smul {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (a : ℝ) :
    productSumLaw (fun i => (μ i).map (fun x => a • x)) =
      (productSumLaw μ).map (fun x => a • x) := by
  have hCoord : Measurable (fun x : ι → ℂ => fun i => a • x i) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply i).const_smul a)
  rw [productSumLaw, ← Measure.pi_map_pi
    (fun _ => (measurable_const_smul a).aemeasurable),
    Measure.map_map measurable_finite_sum hCoord,
    productSumLaw, Measure.map_map (measurable_const_smul a) measurable_finite_sum]
  congr 1
  funext x
  exact (Finset.smul_sum ..).symm

theorem probability_scaled_area_map_le_volume (μ : Measure ℂ) {B : ℝ} (hB : 0 < B)
    (hμ : μ ≤ ENNReal.ofReal B • volume) :
    μ.map (fun x : ℂ => Real.sqrt B • x) ≤ volume := by
  have ha : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  have h := Measure.map_mono hμ (measurable_const_smul (Real.sqrt B))
  rw [Measure.map_smul, planar_volume_map_smul ha, smul_smul,
    Real.sq_sqrt hB.le, ← ENNReal.ofReal_mul hB.le] at h
  simpa only [mul_inv_cancel₀ hB.ne', ENNReal.ofReal_one, one_smul] using h

theorem probability_sum_le_unit_scaled_area {m : ℕ} (hm : 1 ≤ m)
    (μ : Fin m → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i ≤ volume) :
    productSumLaw μ ≤ ENNReal.ofReal (200 / (m : ℝ)) • volume := by
  let p := fun i => areaDensity (μ i)
  have hp : ∀ i, UnitBoundedDensity (p i) := fun i => areaDensity_unit_bounded _ (hμ i)
  obtain ⟨q, _, hqLaw, hqBound⟩ := bounded_density_sum hm p hp
  have hLaw : productSumLaw (fun i => densityLaw (p i)) = productSumLaw μ := by
    congr 1
    funext i
    exact densityLaw_areaDensity _ (hμ i)
  rw [hLaw] at hqLaw
  rw [← hqLaw]
  exact densityLaw_le_scaled_volume (ae_of_all _ hqBound)

/-- Bounded densities at any positive scale: no density or Fourier
representation of the independent sum is assumed. -/
theorem probability_sum_le_scaled_area {m : ℕ} (hm : 1 ≤ m)
    (μ : Fin m → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {B : ℝ} (hB : 0 < B) (hμ : ∀ i, μ i ≤ ENNReal.ofReal B • volume) :
    productSumLaw μ ≤ ENNReal.ofReal (200 * B / (m : ℝ)) • volume := by
  let a := Real.sqrt B
  have ha : a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  let ν := fun i => (μ i).map (fun x : ℂ => a • x)
  haveI : ∀ i, IsProbabilityMeasure (ν i) := fun _ =>
    Measure.isProbabilityMeasure_map (measurable_const_smul a).aemeasurable
  have hν : ∀ i, ν i ≤ volume := fun i => probability_scaled_area_map_le_volume _ hB (hμ i)
  have hSum := probability_sum_le_unit_scaled_area hm ν hν
  have h := Measure.map_mono hSum (measurable_const_smul a⁻¹)
  have hBack : (productSumLaw ν).map (fun x : ℂ => a⁻¹ • x) = productSumLaw μ := by
    rw [productSumLaw_map_smul, Measure.map_map (measurable_const_smul a⁻¹)
      (measurable_const_smul a)]
    have hId : (fun x : ℂ => a⁻¹ • x) ∘ (fun x => a • x) = id := by
      funext x
      simp only [Function.comp_apply, smul_smul, inv_mul_cancel₀ ha, one_smul, id_eq]
    rw [hId, Measure.map_id]
  rw [hBack, Measure.map_smul, planar_volume_map_smul (inv_ne_zero ha), smul_smul,
    inv_pow, inv_inv, Real.sq_sqrt hB.le, ← ENNReal.ofReal_mul
      (by positivity : (0 : ℝ) ≤ 200 / (m : ℝ))] at h
  convert h using 1
  congr 2
  dsimp [a]
  ring

theorem probability_sum_closedBall_le {m : ℕ} (hm : 1 ≤ m)
    (μ : Fin m → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {B r : ℝ} (hB : 0 < B) (hμ : ∀ i, μ i ≤ ENNReal.ofReal B • volume)
    (hr : 0 ≤ r) (z : ℂ) :
    productSumLaw μ (Metric.closedBall z r) ≤
      ENNReal.ofReal ((200 * B / (m : ℝ)) * (r ^ 2 * Real.pi)) := by
  have h := probability_sum_le_scaled_area hm μ hB hμ (Metric.closedBall z r)
  rw [Measure.smul_apply, smul_eq_mul, Complex.volume_closedBall] at h
  have hpi : ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  convert h using 1
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 200 * B / (m : ℝ)),
    ENNReal.ofReal_mul (sq_nonneg r), ENNReal.ofReal_pow hr, hpi]

end CircularLaw
