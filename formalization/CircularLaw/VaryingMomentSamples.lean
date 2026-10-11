import CircularLaw.VaryingProbabilityPolynomial
import CircularLaw.VaryingFiniteTestProbability

/-!
# Actual finite samples approaching every limiting moment

A vanishing upper-bound failure probability and convergence of every
empirical moment give samples within a fixed compact interval whose first
`k+1` moments all have error at most `1/(k+1)`. The finite union has
probability less than one, so a simultaneous good sample exists.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem varying_good_moment_samples {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ)
    (a : ℕ → ℝ) (R : ℝ)
    (hBad : Tendsto (fun n => (μ n).real {x | ∃ j, R < s n x j}) atTop (𝓝 0))
    (hMom : ∀ m, VaryingConvergesInProbability μ
      (fun n x => finiteMean (fun j => s n x j ^ m)) (a m)) :
    ∃ (N : ℕ → ℕ) (x : ∀ k, Ω (N k)),
      (∀ k, 0 < N k) ∧ (∀ k j, s (N k) (x k) j ≤ R) ∧
      ∀ k m, m ≤ k →
        |finiteMean (fun j => s (N k) (x k) j ^ m) - a m| ≤ 1 / ((k : ℝ) + 1) := by
  have hStage (k : ℕ) : ∃ (n : ℕ) (x : Ω n), 0 < n ∧
      (∀ j, s n x j ≤ R) ∧ ∀ m, m ≤ k →
        |finiteMean (fun j => s n x j ^ m) - a m| ≤ 1 / ((k : ℝ) + 1) := by
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    let B (n : ℕ) : Set (Ω n) := {x | ∃ j, R < s n x j}
    let E (n : ℕ) : Set (Ω n) := {x | ∃ m ∈ Finset.range (k + 1),
      ε < |finiteMean (fun j => s n x j ^ m) - a m|}
    have hCentered (m : ℕ) : VaryingConvergesInProbability μ
        (fun n x => finiteMean (fun j => s n x j ^ m) - a m) 0 := by
      simpa only [sub_self] using varying_probability_sub μ (hMom m) (varying_probability_const μ (a m))
    have hE : Tendsto (fun n => (μ n).real (E n)) atTop (𝓝 0) := by
      simpa only [sub_zero] using varying_finite_test_exceedance_tendsto_zero μ
        (Finset.range (k + 1))
        (fun m n x => finiteMean (fun j => s n x j ^ m) - a m)
        (fun m _ => hCentered m) hε
    have hSum : Tendsto (fun n => (μ n).real (B n) + (μ n).real (E n)) atTop (𝓝 0) := by
      simpa only [add_zero] using hBad.add hE
    obtain ⟨n, hn, hSmall⟩ := ((eventually_gt_atTop 0).and
      (hSum.eventually (gt_mem_nhds zero_lt_one))).exists
    have hExists : ∃ x : Ω n, x ∉ B n ∪ E n := by
      by_contra h
      have hAll : B n ∪ E n = Set.univ := Set.eq_univ_iff_forall.mpr (by
        intro x
        by_contra hx
        exact h ⟨x, hx⟩)
      have hUnion := measureReal_union_le (μ := μ n) (B n) (E n)
      rw [hAll, probReal_univ] at hUnion
      linarith
    obtain ⟨x, hx⟩ := hExists
    have hxB : x ∉ B n := fun h => hx (Or.inl h)
    have hxE : x ∉ E n := fun h => hx (Or.inr h)
    refine ⟨n, x, hn, fun j => le_of_not_gt (fun hj => hxB ⟨j, hj⟩), ?_⟩
    intro m hm
    exact le_of_not_gt (fun h => hxE ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm), h⟩)
  choose N x hn hBound hError using hStage
  exact ⟨N, x, hn, hBound, hError⟩

end CircularLaw
