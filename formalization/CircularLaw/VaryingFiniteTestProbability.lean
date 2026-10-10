import CircularLaw.VaryingProbabilityConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Simultaneous convergence for a fixed finite family on varying probability spaces -/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology

namespace CircularLaw

theorem varying_finite_test_exceedance_tendsto_zero {Ω : ℕ → Type*} {ι : Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : Finset ι) (f : ι → ∀ n, Ω n → ℝ)
    (hF : ∀ i ∈ s, VaryingConvergesInProbability μ (f i) 0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real {ω | ∃ i ∈ s, ε < |f i n ω|}) atTop (𝓝 0) := by
  have hSum : Tendsto (fun n => ∑ i ∈ s, (μ n).real {ω | ε < |f i n ω|}) atTop (𝓝 0) := by
    simpa only [sub_zero, Finset.sum_const_zero] using
      tendsto_finset_sum s (fun i hi => hF i hi ε hε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  apply Eventually.of_forall
  intro n
  have hUnion : {ω : Ω n | ∃ i ∈ s, ε < |f i n ω|} =
      ⋃ i ∈ s, {ω : Ω n | ε < |f i n ω|} := by ext; simp
  rw [hUnion]
  exact measureReal_biUnion_finset_le s _

end CircularLaw
