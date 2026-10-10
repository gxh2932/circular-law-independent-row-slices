import CircularLaw.ConvexProductConcentration
import Mathlib.Data.Finset.Max

/-!
# A median for every real function on a finite probability space

The least attained value whose lower cumulative mass is at least one
half also has upper mass at least one half. Zero-mass outcomes are
allowed, so the result includes degenerate Bernoulli parameters.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem finite_law_median_exists {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) :
    ∃ m : ℝ, IsRealLawMedian μ f m := by
  let S := Finset.univ.image f
  have hS : S.Nonempty := Finset.univ_nonempty.image f
  let T := S.filter (fun m => 1 / 2 ≤ μ.real {ω | f ω ≤ m})
  have hT : T.Nonempty := by
    refine ⟨S.max' hS, Finset.mem_filter.mpr ⟨Finset.max'_mem S hS, ?_⟩⟩
    have hEvent : {ω | f ω ≤ S.max' hS} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      exact Finset.le_max' S (f ω) (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩)
    rw [hEvent, probReal_univ]
    norm_num
  let m := T.min' hT
  have hm : m ∈ T := Finset.min'_mem T hT
  refine ⟨m, (Finset.mem_filter.mp hm).2, ?_⟩
  by_contra hUpper
  have hPartition : μ.real {ω | f ω < m} + μ.real {ω | m ≤ f ω} = 1 := by
    simpa only [Set.compl_setOf, not_lt, probReal_univ] using
      measureReal_add_measureReal_compl (μ := μ) ((Set.toFinite {ω | f ω < m}).measurableSet)
  have hLow : 1 / 2 < μ.real {ω | f ω < m} := by linarith
  obtain ⟨ω₀, hω₀⟩ := nonempty_of_measureReal_ne_zero (ne_of_gt (lt_trans (by norm_num) hLow))
  let B := S.filter (fun b => b < m)
  have hB : B.Nonempty := by
    refine ⟨f ω₀, Finset.mem_filter.mpr ⟨?_, hω₀⟩⟩
    exact Finset.mem_image.mpr ⟨ω₀, Finset.mem_univ _, rfl⟩
  let b := B.max' hB
  have hbMem : b ∈ B := Finset.max'_mem B hB
  have hbLt : b < m := (Finset.mem_filter.mp hbMem).2
  have hCover : {ω | f ω < m} ⊆ {ω | f ω ≤ b} := by
    intro ω hω
    exact Finset.le_max' B (f ω) (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩, hω⟩)
  have hbMass : 1 / 2 ≤ μ.real {ω | f ω ≤ b} :=
    hLow.le.trans (measureReal_mono hCover)
  have hbT : b ∈ T := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hbMem).1, hbMass⟩
  exact (not_lt_of_ge (Finset.min'_le T b hbT)) hbLt

end CircularLaw
