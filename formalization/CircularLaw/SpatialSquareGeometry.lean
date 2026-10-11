import CircularLaw.VaryingProbabilityConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# Deterministic spatial control from a square integral

A small-amplitude region and Young's inequality bound the absolute
integral by its square integral and the measure of the large-amplitude
region. All spatial measures here are finite.
-/

noncomputable section
open Classical MeasureTheory Set

namespace CircularLaw

theorem integrable_of_integrable_square {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (f : X → ℝ) (hf : Measurable f)
    (hSq : Integrable (fun x => (f x) ^ 2) ν) : Integrable f ν := by
  have hBound : Integrable (fun x => (1 : ℝ) + (f x) ^ 2) ν :=
    (integrable_const 1).add hSq
  apply hBound.mono' hf.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f x| - 1), sq_abs (f x), abs_nonneg (f x)]

theorem absolute_young_square_bound (a : ℝ) {c : ℝ} (hc : 0 < c) :
    |a| ≤ c * a ^ 2 + 1 / (4 * c) := by
  have hcN : c ≠ 0 := hc.ne'
  have hMul : (c * a ^ 2 + 1 / (4 * c)) * (4 * c) = 4 * c ^ 2 * a ^ 2 + 1 := by
    field_simp
  have hProduct : |a| * (4 * c) ≤ (c * a ^ 2 + 1 / (4 * c)) * (4 * c) := by
    rw [hMul]
    nlinarith [sq_nonneg (2 * c * |a| - 1), sq_abs a]
  nlinarith

theorem spatial_absolute_integral_split_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (f : X → ℝ) (hf : Measurable f)
    (hSq : Integrable (fun x => (f x) ^ 2) ν) {η c : ℝ} (hη : 0 ≤ η) (hc : 0 < c) :
    (∫ x, |f x| ∂ν) ≤ η * ν.real univ + c * (∫ x, (f x) ^ 2 ∂ν) +
      (1 / (4 * c)) * ν.real {x | η < |f x|} := by
  let B : Set X := {x | η < |f x|}
  have hAbs : Measurable (fun x => |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hB : MeasurableSet B := measurableSet_lt measurable_const hAbs
  have hIndicator : Integrable (B.indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_const 1).indicator hB
  have hInt := integrable_of_integrable_square ν f hf hSq
  have hRhs : Integrable
      (fun x => η + c * (f x) ^ 2 + (1 / (4 * c)) * B.indicator (fun _ => (1 : ℝ)) x) ν :=
    ((integrable_const η).add (hSq.const_mul c)).add (hIndicator.const_mul _)
  have hMono : (∫ x, |f x| ∂ν) ≤ ∫ x, η + c * (f x) ^ 2 +
      (1 / (4 * c)) * B.indicator (fun _ => (1 : ℝ)) x ∂ν := by
    apply integral_mono hInt.abs hRhs
    intro x
    change |f x| ≤ η + c * (f x) ^ 2 + (1 / (4 * c)) * B.indicator (fun _ => (1 : ℝ)) x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have h := absolute_young_square_bound (f x) hc
      linarith
    · rw [Set.indicator_of_notMem hx]
      have hSmall : |f x| ≤ η := le_of_not_gt hx
      have hNonneg := mul_nonneg hc.le (sq_nonneg (f x))
      linarith
  have hFirst : Integrable (fun x => η + c * (f x) ^ 2) ν :=
    (integrable_const η).add (hSq.const_mul c)
  rw [integral_add hFirst (hIndicator.const_mul _),
    integral_add (integrable_const η) (hSq.const_mul c), integral_const,
    integral_const_mul, integral_const_mul, integral_indicator hB, setIntegral_const] at hMono
  simp only [smul_eq_mul, mul_one] at hMono
  dsimp only [B] at hMono
  nlinarith

end CircularLaw
