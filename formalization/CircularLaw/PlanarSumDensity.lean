import CircularLaw.FourierProduct
import CircularLaw.FourierInversion
import CircularLaw.SumLaw
import Mathlib.Probability.Independence.Basic

/-!
# The density bound for an independent planar sum

This proves the bounded-density conclusion of LLTTY19 Proposition 2.4,
with absolute constant 200. The sum law is a product-law pushforward, and
its density is obtained from Radon--Nikodym and almost-everywhere Fourier
inversion. No assumed density of the sum or assumed Fourier identity is used.
-/

noncomputable section
open MeasureTheory FourierTransform ProbabilityTheory
open scoped FourierTransform BigOperators ENNReal

namespace CircularLaw

theorem bounded_density_sum_area_bound {m : ℕ} (hm : 1 ≤ m)
    (p : Fin m → ℂ → ℝ) (hp : ∀ i, UnitBoundedDensity (p i)) :
    ∀ᵐ x ∂volume, areaDensity (productSumLaw (fun i => densityLaw (p i))) x ≤
      200 / (m : ℝ) := by
  haveI : ∀ i, IsProbabilityMeasure (densityLaw (p i)) := fun i => densityLaw_probability (hp i)
  let μ := productSumLaw (fun i => densityLaw (p i))
  have hμ : μ ≤ volume := productSumLaw_le_volume _ (by omega)
    (fun i => densityLaw_le_volume (hp i))
  have hq : UnitBoundedDensity (areaDensity μ) := areaDensity_unit_bounded μ hμ
  by_cases hm2 : 2 ≤ m
  · have hFourier (t : ℂ) : 𝓕 (fun x => (areaDensity μ x : ℂ)) t =
        ∏ i, 𝓕 (fun x => (p i x : ℂ)) t := by
      rw [← densityLaw_charFun_fourier hq, densityLaw_areaDensity μ hμ,
        charFun_productSumLaw]
      apply Finset.prod_congr rfl
      intro i _
      exact densityLaw_charFun_fourier (hp i) t
    have hProd := bounded_density_fourier_product_integrable p hp (by simpa using hm2)
    have hF : Integrable (𝓕 (fun x => (areaDensity μ x : ℂ))) volume := by
      apply (integrable_norm_iff
        (continuous_pointwise_fourier (f := fun x => (areaDensity μ x : ℂ))
          hq.integrable.ofReal).aestronglyMeasurable).mp
      simpa only [hFourier, norm_prod] using hProd
    have h := bounded_density_le_fourier_integral hq hF
    have hB := bounded_density_fourier_product_bound p hp (by simpa using hm2)
    simp only [hFourier, norm_prod] at h
    filter_upwards [h] with x hx
    exact hx.trans (by simpa using hB)
  · have hm1 : m = 1 := by omega
    filter_upwards [hq.le_one] with x hx
    exact hx.trans (by simp only [hm1, Nat.cast_one, div_one]; norm_num)

/-- The actual independent sum has a probability density bounded
everywhere by `200/m`. Clipping changes only a null set. -/
theorem bounded_density_sum {m : ℕ} (hm : 1 ≤ m)
    (p : Fin m → ℂ → ℝ) (hp : ∀ i, UnitBoundedDensity (p i)) :
    ∃ q : ℂ → ℝ, UnitBoundedDensity q ∧
      densityLaw q = productSumLaw (fun i => densityLaw (p i)) ∧
      ∀ x, q x ≤ 200 / (m : ℝ) := by
  haveI : ∀ i, IsProbabilityMeasure (densityLaw (p i)) := fun i => densityLaw_probability (hp i)
  let μ := productSumLaw (fun i => densityLaw (p i))
  let q := areaDensity μ
  have hμ : μ ≤ volume := productSumLaw_le_volume _ (by omega)
    (fun i => densityLaw_le_volume (hp i))
  have hq : UnitBoundedDensity q := areaDensity_unit_bounded μ hμ
  let r : ℂ → ℝ := fun x => min (200 / (m : ℝ)) (q x)
  have heq : r =ᵐ[volume] q := by
    filter_upwards [bounded_density_sum_area_bound hm p hp] with x hx
    exact min_eq_right hx
  refine ⟨r, ?_, ?_, fun x => min_le_left _ _⟩
  · constructor
    · exact hq.integrable.congr heq.symm
    · filter_upwards [heq, hq.nonneg] with x hx hy
      rw [hx]
      exact hy
    · filter_upwards [heq, hq.le_one] with x hx hy
      rw [hx]
      exact hy
    · exact (integral_congr_ae heq).trans hq.mass
  · calc
      densityLaw r = densityLaw q := withDensity_congr_ae (heq.fun_comp ENNReal.ofReal)
      _ = μ := densityLaw_areaDensity μ hμ

/-- The product-law theorem applies to independent summands on any
probability space. Independence supplies the joint product law. -/
theorem bounded_density_independent_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    (X : Fin m → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (p : Fin m → ℂ → ℝ) (hp : ∀ i, UnitBoundedDensity (p i))
    (hLaw : ∀ i, μ.map (X i) = densityLaw (p i)) :
    ∃ q : ℂ → ℝ, UnitBoundedDensity q ∧
      densityLaw q = μ.map (fun ω => ∑ i, X i ω) ∧ ∀ x, q x ≤ 200 / (m : ℝ) := by
  have hJoint : μ.map (fun ω i => X i ω) = Measure.pi (fun i => densityLaw (p i)) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mp hInd]
    simp_rw [hLaw]
  have hJointMeas : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ hX
  have hSum : productSumLaw (fun i => densityLaw (p i)) =
      μ.map (fun ω => ∑ i, X i ω) := by
    rw [productSumLaw, ← hJoint, Measure.map_map measurable_finite_sum hJointMeas]
    rfl
  obtain ⟨q, hq, hqLaw, hqBound⟩ := bounded_density_sum hm p hp
  exact ⟨q, hq, hqLaw.trans hSum, hqBound⟩

theorem bounded_density_independent_sum_small_ball {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    (X : Fin m → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (p : Fin m → ℂ → ℝ) (hp : ∀ i, UnitBoundedDensity (p i))
    (hLaw : ∀ i, μ.map (X i) = densityLaw (p i)) {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    μ {ω | ‖(∑ i, X i ω) - z‖ ≤ r} ≤
      ENNReal.ofReal ((200 / (m : ℝ)) * (r ^ 2 * Real.pi)) := by
  obtain ⟨q, _, hqLaw, hqBound⟩ := bounded_density_independent_sum μ hm X hX hInd p hp hLaw
  have h := densityLaw_closedBall_le (by positivity : (0 : ℝ) ≤ 200 / (m : ℝ)) hr
    (ae_of_all _ hqBound) z
  rw [hqLaw, Measure.map_apply (Finset.measurable_sum _ (fun i _ => hX i))
    measurableSet_closedBall] at h
  simpa only [Set.preimage, Metric.mem_closedBall, dist_eq_norm] using h

theorem bounded_density_independent_sum_concentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    (X : Fin m → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (p : Fin m → ℂ → ℝ) (hp : ∀ i, UnitBoundedDensity (p i))
    (hLaw : ∀ i, μ.map (X i) = densityLaw (p i)) {r : ℝ} (hr : 0 ≤ r) :
    levyConcentration μ (fun ω => ∑ i, X i ω) r ≤
      ENNReal.ofReal ((200 / (m : ℝ)) * (r ^ 2 * Real.pi)) := by
  apply iSup_le
  intro z
  exact bounded_density_independent_sum_small_ball μ hm X hX hInd p hp hLaw hr z

def PlanarSumDensityLemma : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (p : Fin m → ℂ → ℝ),
    (∀ i, UnitBoundedDensity (p i)) →
    ∃ q : ℂ → ℝ, UnitBoundedDensity q ∧
      densityLaw q = productSumLaw (fun i => densityLaw (p i)) ∧ ∀ x, q x ≤ C / (m : ℝ)

theorem planar_sum_density_lemma : PlanarSumDensityLemma := by
  refine ⟨200, by norm_num, ?_⟩
  intro m hm p hp
  exact bounded_density_sum hm p hp

def IndependentPlanarDensityLemma : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (m : ℕ), 1 ≤ m → ∀ (X : Fin m → Ω → ℂ),
    (∀ i, Measurable (X i)) → iIndepFun X μ → ∀ (p : Fin m → ℂ → ℝ),
    (∀ i, UnitBoundedDensity (p i)) → (∀ i, μ.map (X i) = densityLaw (p i)) →
    ∃ q : ℂ → ℝ, UnitBoundedDensity q ∧
      densityLaw q = μ.map (fun ω => ∑ i, X i ω) ∧ ∀ x, q x ≤ C / (m : ℝ)

theorem independent_planar_density_lemma : IndependentPlanarDensityLemma := by
  refine ⟨200, by norm_num, ?_⟩
  intro Ω _ μ hμ m hm X hX hInd p hp hLaw
  letI := hμ
  exact bounded_density_independent_sum μ hm X hX hInd p hp hLaw

end CircularLaw
