import CircularLaw.VaryingProbabilityConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Mean-square convergence on varying probability spaces

Markov's inequality bounds the actual deviation event by the centered
square integral divided by the squared tolerance. A vanishing square
integral therefore implies convergence in probability without requiring
a common sample space.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem mean_square_deviation_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (a : ℝ)
    (hInt : Integrable (fun x => (f x - a) ^ 2) μ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {x | ε < |f x - a|} ≤ (∫ x, (f x - a) ^ 2 ∂μ) / ε ^ 2 := by
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun x => sq_nonneg (f x - a))) hInt (ε ^ 2)
  have hSubset : {x | ε < |f x - a|} ⊆ {x | ε ^ 2 ≤ (f x - a) ^ 2} := by
    intro x hx
    change ε < |f x - a| at hx
    change ε ^ 2 ≤ (f x - a) ^ 2
    simpa only [sq_abs] using (sq_le_sq₀ hε.le (abs_nonneg _)).mpr hx.le
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hSubset)
    (sq_nonneg ε)).trans hMark

theorem varying_probability_of_mean_square {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (f : ∀ n, Ω n → ℝ) (a : ℝ)
    (hInt : ∀ n, Integrable (fun x => (f n x - a) ^ 2) (μ n))
    (hLimit : Tendsto (fun n => ∫ x, (f n x - a) ^ 2 ∂μ n) atTop (𝓝 0)) :
    VaryingConvergesInProbability μ f a := by
  intro ε hε
  have hUpper := hLimit.div_const (ε ^ 2)
  simp only [zero_div] at hUpper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun _ => measureReal_nonneg))
    (Eventually.of_forall (fun n => mean_square_deviation_bound (μ n) (f n) a (hInt n) hε))

end CircularLaw
