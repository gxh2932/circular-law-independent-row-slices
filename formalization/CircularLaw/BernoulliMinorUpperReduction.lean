import CircularLaw.BernoulliCommonMinorLogPrefix

/-!
# The actual Bernoulli full logarithmic limit from the remaining upper estimate

Both literal prefix limits and every limiting Gaussian input are supplied
by checked proofs. The sole probability input is the fixed-fraction
full-to-minor upper estimate, with a vanishing deterministic error and
explicit singular samples. This module keeps that input explicit; BernoulliGreedyMinorUpperLimit supplies it.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem bernoulli_full_log_convergence_of_minor_upper (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    (e : ℝ → ℝ) {epsilon0 : ℝ} (hEpsilon0 : 0 < epsilon0)
    (hE : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hUpper : ∀ epsilon, (hPos : 0 < epsilon) → epsilon ≤ epsilon0 →
      ∀ delta : ℝ, 0 < delta → Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
          bernoulliMinorLogPrefixAt d z epsilon hPos.le n x + e epsilon + delta <
            squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)}) atTop (𝓝 0)) :
    EmpiricalLogConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (bernoulliSingularArray d z) (gaussianShiftedSingularLimit z) := by
  let P := fun k epsilon n => epsilon ≤ epsilon0 → ∀ hNonneg : 0 ≤ epsilon,
    (sparseBernoulliMatrixLaw n (d n)).real
      {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
        bernoulliMinorLogPrefixAt d z epsilon hNonneg n x + e epsilon + diagonalAccuracy k <
          squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)} < diagonalAccuracy k
  have hP : ∀ k epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ᶠ n in atTop, P k epsilon n := by
    intro k epsilon hPos _
    by_cases hSmall : epsilon ≤ epsilon0
    · filter_upwards [(hUpper epsilon hPos hSmall (diagonalAccuracy k) (diagonalAccuracy_pos k)).eventually
        (gt_mem_nhds (diagonalAccuracy_pos k))] with n hn
      intro _ _
      exact hn
    · exact Eventually.of_forall (fun _ h => False.elim (hSmall h))
  obtain ⟨K, q, _, hQ, hRange, hT1, hMinor, _, hCurrent⟩ :=
    bernoulli_common_minor_log_prefix_with_constraints d z hDegree hSparse P hP
  let epsilon := fun n => logarithmicStageFraction 48 K (q n)
  have hNonneg : ∀ n, 0 ≤ epsilon n := fun n => (hRange n).1.le
  have hEpsilon : Tendsto epsilon atTop (𝓝 0) := (logarithmicStageFraction_tendsto 48 K).comp hQ
  have hStage : Tendsto epsilon atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hEpsilon, Eventually.of_forall (fun n => (hRange n).1)⟩
  have hAccuracy := diagonalAccuracy_tendsto.comp hQ
  have hError : Tendsto (fun n => e (epsilon n) + diagonalAccuracy (q n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, add_zero] using (hE.comp hStage).add hAccuracy
  have hBounds : ∀ᶠ n in atTop, (sparseBernoulliMatrixLaw n (d n)).real
      {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
        bernoulliMinorLogPrefix d z epsilon hNonneg n x + e (epsilon n) + diagonalAccuracy (q n) <
          squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)} ≤ diagonalAccuracy (q n) := by
    filter_upwards [hCurrent, hEpsilon.eventually (gt_mem_nhds hEpsilon0)] with n hn he
    exact (hn he.le (hNonneg n)).le
  have hUpperSlow : ∀ delta : ℝ, 0 < delta → Tendsto (fun n =>
      (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
          bernoulliMinorLogPrefix d z epsilon hNonneg n x + delta <
            squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)}) atTop (𝓝 0) := by
    intro delta hDelta
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAccuracy
      (Eventually.of_forall (fun _ => measureReal_nonneg))
    filter_upwards [hBounds, hError.eventually (gt_mem_nhds hDelta)] with n hn he
    apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n (d n)) ?_).trans hn
    intro x hx
    rcases hx with hZero | hUpperFail
    · exact Or.inl hZero
    · exact Or.inr (by linarith)
  have hCircular : -(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit z) =
      circularPaperPotential z := by rw [gaussian_shifted_log_integral_eq_circular]; rfl
  rw [← hCircular] at hT1 hMinor
  exact bernoulli_full_log_convergence_of_prefix_squeeze d z (gaussianShiftedSingularLimit z)
    epsilon hNonneg hEpsilon hT1 hMinor hUpperSlow

end CircularLaw
