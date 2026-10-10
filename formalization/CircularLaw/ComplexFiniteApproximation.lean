import CircularLaw.TalagrandFiniteIndependence
import Mathlib.MeasureTheory.Function.SimpleFuncDense

/-!
# Measurable finite approximations of bounded complex coordinates

A common finite alphabet approximates the complex disk. Every approximant
stays in that disk, coordinatewise composition preserves independence,
and the Euclidean vectors converge almost surely under the actual bound.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace CircularLaw

def boundedComplexApprox (K : ℝ) (hK : 0 ≤ K) (q : ℕ) : SimpleFunc ℂ ℂ :=
  SimpleFunc.approxOn id measurable_id (Metric.closedBall 0 K) 0 (by simp [hK]) q

abbrev BoundedComplexAlphabet (K : ℝ) (hK : 0 ≤ K) (q : ℕ) :=
  {z : ℂ // z ∈ (boundedComplexApprox K hK q).range}

def boundedComplexApproxLabel (K : ℝ) (hK : 0 ≤ K) (q : ℕ) (z : ℂ) : BoundedComplexAlphabet K hK q :=
  ⟨boundedComplexApprox K hK q z, SimpleFunc.mem_range_self _ _⟩

@[simp] theorem boundedComplexApproxLabel_coe (K : ℝ) (hK : 0 ≤ K) (q : ℕ) (z : ℂ) :
    (boundedComplexApproxLabel K hK q z : ℂ) = boundedComplexApprox K hK q z := rfl

theorem boundedComplexApproxLabel_measurable (K : ℝ) (hK : 0 ≤ K) (q : ℕ) :
    Measurable (boundedComplexApproxLabel K hK q) := (boundedComplexApprox K hK q).measurable.subtype_mk

theorem boundedComplexApprox_norm_le (K : ℝ) (hK : 0 ≤ K) (q : ℕ) (z : ℂ) :
    ‖boundedComplexApprox K hK q z‖ ≤ K := by
  have h := SimpleFunc.approxOn_mem measurable_id
    (show (0 : ℂ) ∈ Metric.closedBall 0 K by simp [hK]) q z
  simpa only [boundedComplexApprox, Metric.mem_closedBall, dist_zero_right, id_eq] using h

theorem boundedComplexAlphabet_norm_le (K : ℝ) (hK : 0 ≤ K) (q : ℕ)
    (z : BoundedComplexAlphabet K hK q) : ‖(z : ℂ)‖ ≤ K := by
  obtain ⟨w, hw⟩ := SimpleFunc.mem_range.mp z.property
  rw [← hw]
  exact boundedComplexApprox_norm_le K hK q w

theorem boundedComplexApprox_tendsto (K : ℝ) (hK : 0 ≤ K) {z : ℂ} (hz : ‖z‖ ≤ K) :
    Tendsto (fun q => boundedComplexApprox K hK q z) atTop (𝓝 z) := by
  apply SimpleFunc.tendsto_approxOn measurable_id
    (show (0 : ℂ) ∈ Metric.closedBall 0 K by simp [hK])
  apply subset_closure
  simpa only [Metric.mem_closedBall, dist_zero_right, id_eq] using hz

theorem boundedComplexApproxLabel_independent {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} {X : Fin n → Ω → ℂ} (hInd : iIndepFun X μ)
    (K : ℝ) (hK : 0 ≤ K) (q : ℕ) :
    iIndepFun (fun i ω => boundedComplexApproxLabel K hK q (X i ω)) μ :=
  hInd.comp (fun _ => boundedComplexApproxLabel K hK q)
    (fun _ => boundedComplexApproxLabel_measurable K hK q)

theorem complexCoordinateVector_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {X : Fin n → Ω → ℂ} (hX : ∀ i, Measurable (X i)) : Measurable (complexCoordinateVector X) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).measurable.comp (measurable_pi_lambda _ hX)

theorem boundedComplexApprox_vector_tendsto_ae {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ K) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun q => complexCoordinateVector (fun i v => boundedComplexApprox K hK q (X i v)) ω)
      atTop (𝓝 (complexCoordinateVector X ω)) := by
  filter_upwards [ae_all_iff.mpr hBound] with ω hω
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).continuousAt.tendsto.comp
  exact tendsto_pi_nhds.mpr (fun i => boundedComplexApprox_tendsto K hK (hω i))

end CircularLaw
