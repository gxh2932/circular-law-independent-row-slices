import CircularLaw.VaryingMomentSamples
import CircularLaw.MeasureModel
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A compactly supported probability measure with the actual limiting moments

Simultaneous good samples give finite probability laws on `[0,R]`. Compactness
of probability measures on this interval supplies a weakly convergent
subsequence. Every power is a bounded continuous test on the interval, so
the resulting measure has all the prescribed limiting moments.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

def compactEmpiricalProbability {n : ℕ} (hn : 0 < n) {R : ℝ}
    (s : Fin n → Set.Icc (0 : ℝ) R) : ProbabilityMeasure (Set.Icc (0 : ℝ) R) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ProbabilityMeasure.map (⟨finiteUniformMeasure (Fin n), inferInstance⟩ : ProbabilityMeasure (Fin n))
    (measurable_of_countable s).aemeasurable

theorem compact_empirical_probability_integral {n : ℕ} (hn : 0 < n) {R : ℝ}
    (s : Fin n → Set.Icc (0 : ℝ) R) (f : C(Set.Icc (0 : ℝ) R, ℝ)) :
    (∫ t, f t ∂(compactEmpiricalProbability hn s : Measure (Set.Icc (0 : ℝ) R))) =
      finiteMean (fun j => f (s j)) := by
  change (∫ t, f t ∂(finiteUniformMeasure (Fin n)).map s) = _
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable s)
    f.continuous.measurable.stronglyMeasurable, integral_finiteUniformMeasure]

def intervalPower (R : ℝ) (m : ℕ) : C(Set.Icc (0 : ℝ) R, ℝ) :=
  ⟨fun t => (t : ℝ) ^ m, continuous_subtype_val.pow m⟩

theorem supported_probability_measure_of_varying_moments {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ)
    (a : ℕ → ℝ) (R : ℝ) (hNonneg : ∀ n x j, 0 ≤ s n x j)
    (hBad : Tendsto (fun n => (μ n).real {x | ∃ j, R < s n x j}) atTop (𝓝 0))
    (hMom : ∀ m, VaryingConvergesInProbability μ
      (fun n x => finiteMean (fun j => s n x j ^ m)) (a m)) :
    ∃ ν : ProbabilityMeasure (Set.Icc (0 : ℝ) R),
      ∀ m, (∫ t, (t : ℝ) ^ m ∂(ν : Measure (Set.Icc (0 : ℝ) R))) = a m := by
  obtain ⟨N, x, hn, hBound, hError⟩ := varying_good_moment_samples μ s a R hBad hMom
  let t (k : ℕ) (j : Fin (N k)) : Set.Icc (0 : ℝ) R :=
    ⟨s (N k) (x k) j, hNonneg _ _ _, hBound k j⟩
  let νs (k : ℕ) := compactEmpiricalProbability (hn k) (t k)
  obtain ⟨ν, φ, hφ, hLimit⟩ := CompactSpace.tendsto_subseq νs
  refine ⟨ν, fun m => ?_⟩
  have hMomSeq : Tendsto (fun k => ∫ t, (t : ℝ) ^ m
      ∂(νs k : Measure (Set.Icc (0 : ℝ) R))) atTop (𝓝 (a m)) := by
    change Tendsto (fun k => ∫ t, intervalPower R m t
      ∂(νs k : Measure (Set.Icc (0 : ℝ) R))) atTop (𝓝 (a m))
    simp only [νs, compact_empirical_probability_integral]
    change Tendsto (fun k => finiteMean (fun j => s (N k) (x k) j ^ m)) atTop (𝓝 (a m))
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [eventually_ge_atTop m,
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)] with k hk he
    simpa only [Real.dist_eq] using (hError k m hk).trans_lt he
  have hWeak := (ProbabilityMeasure.continuous_integral_continuousMap (intervalPower R m)).tendsto ν
  exact tendsto_nhds_unique (hWeak.comp hLimit) (hMomSeq.comp hφ.tendsto_atTop)

end CircularLaw
