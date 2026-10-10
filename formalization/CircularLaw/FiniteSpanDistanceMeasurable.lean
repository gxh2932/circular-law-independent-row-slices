import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Measurability of distances to continuously varying finite row spans

The actual distance to the span is the infimum of the norms of all finite
linear-combination residuals. Each residual is continuous when the point
and every row vary continuously. The infimum is upper semicontinuous and
therefore measurable, even when the row rank changes.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def finiteSpanDistance {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (v : E) (rows : ι → E) : ℝ :=
  Metric.infDist v (Submodule.span ℂ (Set.range rows) : Set E)

theorem finite_span_distance_nonneg {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (v : E) (rows : ι → E) : 0 ≤ finiteSpanDistance v rows :=
  Metric.infDist_nonneg

theorem finite_span_distance_eq_coefficients {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (v : E) (rows : ι → E) :
    finiteSpanDistance v rows = ⨅ c : ι → ℂ, ‖v - ∑ i, c i • rows i‖ := by
  have hImage : (fun y => dist v y) '' (Submodule.span ℂ (Set.range rows) : Set E) =
      Set.range (fun c : ι → ℂ => ‖v - ∑ i, c i • rows i‖) := by
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
      exact ⟨c, (dist_eq_norm _ _).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨∑ i, c i • rows i, (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨c, rfl⟩,
        dist_eq_norm _ _⟩
  have hGLB := Metric.isGLB_infDist (x := v)
    (s := (Submodule.span ℂ (Set.range rows) : Set E))
    ⟨0, (Submodule.span ℂ (Set.range rows)).zero_mem⟩
  rw [hImage] at hGLB
  exact hGLB.ciInf_eq.symm

theorem upperSemicontinuous_finite_span_distance {ι E X : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace X]
    (v : X → E) (rows : ι → X → E) (hv : Continuous v) (hRows : ∀ i, Continuous (rows i)) :
    UpperSemicontinuous (fun x => finiteSpanDistance (v x) (fun i => rows i x)) := by
  simp only [finite_span_distance_eq_coefficients]
  apply upperSemicontinuous_ciInf
  · intro x
    exact ⟨0, by rintro _ ⟨c, rfl⟩; exact norm_nonneg _⟩
  · intro c
    exact (hv.sub (continuous_finset_sum _ (fun i _ => (hRows i).const_smul (c i)))).norm.upperSemicontinuous

theorem measurable_finite_span_distance {ι E X : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (v : X → E) (rows : ι → X → E) (hv : Continuous v) (hRows : ∀ i, Continuous (rows i)) :
    Measurable (fun x => finiteSpanDistance (v x) (fun i => rows i x)) :=
  (upperSemicontinuous_finite_span_distance v rows hv hRows).measurable

end CircularLaw
