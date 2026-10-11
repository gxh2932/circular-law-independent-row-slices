import CircularLaw.FiniteFiberTower
import Mathlib.Probability.Moments.SubGaussian

/-!
# Hoeffding's exponential bound on literal finite fibres

Bounded, mean-zero fibre variables use the actual uniform fibre measure.
The resulting exponential bound can be multiplied by any nonnegative
past-dependent weight before averaging over the original finite law.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CircularLaw

theorem finite_fiber_exp_bound {Ω α : Type*} [Fintype Ω] (s : Ω → α)
    (X : Ω → ℝ) (x : Ω) {K : ℝ} (hK : 0 ≤ K)
    (hBound : ∀ y, s y = s x → X y ∈ Set.Icc (-K) K)
    (hMean : finiteFiberMean s X (s x) = 0) (t : ℝ) :
    finiteFiberMean s (fun y => Real.exp (t * X y)) (s x) ≤
      Real.exp (K ^ 2 * t ^ 2 / 2) := by
  haveI := finiteFiberMean_reference_nonempty s x
  letI : MeasurableSpace {y // s y = s x} := ⊤
  haveI : MeasurableSingletonClass {y // s y = s x} := ⟨fun _ => trivial⟩
  let μ := finiteUniformMeasure {y // s y = s x}
  have hSG := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := μ) (X := fun y : {y // s y = s x} => X y.val)
    (measurable_of_countable _).aemeasurable
    (ae_of_all μ (fun y => hBound y.val y.property))
    (by rw [integral_finiteUniformMeasure]; exact hMean)
  have h := hSG.mgf_le t
  rw [mgf, integral_finiteUniformMeasure] at h
  have hCoeff : (((‖K - -K‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = K ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm]
    rw [Real.norm_of_nonneg (by linarith : 0 ≤ K - -K)]
    ring
  simpa only [hCoeff] using h

theorem finiteMean_weighted_exp_bound {Ω α : Type*} [Fintype Ω] [Fintype α]
    (s : Ω → α) (X : Ω → ℝ) (w : α → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hWeight : ∀ a, 0 ≤ w a) (hBound : ∀ x, X x ∈ Set.Icc (-K) K)
    (hMean : ∀ x, finiteFiberMean s X (s x) = 0) (t : ℝ) :
    finiteMean (fun x => w (s x) * Real.exp (t * X x)) ≤
      Real.exp (K ^ 2 * t ^ 2 / 2) * finiteMean (fun x => w (s x)) := by
  rw [← finiteMean_fiberMean_weighted s (fun x => Real.exp (t * X x)) w]
  calc
    _ ≤ finiteMean (fun x => w (s x) * Real.exp (K ^ 2 * t ^ 2 / 2)) := by
      apply finiteMean_mono
      intro x
      exact mul_le_mul_of_nonneg_left
        (finite_fiber_exp_bound s X x hK (fun y _ => hBound y) (hMean x) t) (hWeight (s x))
    _ = _ := by rw [finiteMean_mul_const, mul_comm]

end CircularLaw
