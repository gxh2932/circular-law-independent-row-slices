import CircularLaw.BernoulliLogSqueeze

/-!
# A single slow choice assembling the full Bernoulli logarithmic limit

The actual T1 proof, actual minor-prefix fixed-fraction limits and the
full-to-minor upper estimates are enforced by one selector. The latter
two inputs and Bernoulli weak-law transfer remain mathematical
obligations. Limiting-law mass and support bounds are reusable arguments;
for the actual Gaussian law these bounds are proved separately. The fixed fractions
need only lie in one positive neighborhood of zero.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem bernoulli_full_log_convergence_of_fixed_fraction_inputs (d : ℕ → ℕ) (z : ℂ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν)
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    (R : ℝ) (hSupport : ν {x : ℝ≥0 | R < (x : ℝ)} = 0)
    (a e : ℝ → ℝ) {epsilon0 : ℝ} (hEpsilon0 : 0 < epsilon0)
    (hMinor : ∀ epsilon, (hPos : 0 < epsilon) → epsilon ≤ epsilon0 →
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (bernoulliMinorLogPrefixAt d z epsilon hPos.le) (a epsilon))
    (hA : Tendsto a (𝓝[>] (0 : ℝ))
      (𝓝 (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν))))
    (hE : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hUpper : ∀ epsilon, (hPos : 0 < epsilon) → epsilon ≤ epsilon0 →
      ∀ delta : ℝ, 0 < delta → Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
          bernoulliMinorLogPrefixAt d z epsilon hPos.le n x + e epsilon + delta <
            squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)}) atTop (𝓝 0)) :
    EmpiricalLogConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (bernoulliSingularArray d z) ν := by
  let P := fun k epsilon n => epsilon ≤ epsilon0 → ∀ hNonneg : 0 ≤ epsilon,
    (sparseBernoulliMatrixLaw n (d n)).real {x | diagonalAccuracy k <
      |bernoulliMinorLogPrefixAt d z epsilon hNonneg n x - a epsilon|} < diagonalAccuracy k ∧
    (sparseBernoulliMatrixLaw n (d n)).real
      {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
        bernoulliMinorLogPrefixAt d z epsilon hNonneg n x + e epsilon + diagonalAccuracy k <
          squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)} < diagonalAccuracy k
  have hP : ∀ k epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ᶠ n in atTop, P k epsilon n := by
    intro k epsilon hPos _
    by_cases hSmall : epsilon ≤ epsilon0
    · filter_upwards [
        (hMinor epsilon hPos hSmall (diagonalAccuracy k) (diagonalAccuracy_pos k)).eventually
          (gt_mem_nhds (diagonalAccuracy_pos k)),
        (hUpper epsilon hPos hSmall (diagonalAccuracy k) (diagonalAccuracy_pos k)).eventually
          (gt_mem_nhds (diagonalAccuracy_pos k))] with n hm hu
      intro _ hNonneg
      exact ⟨hm, hu⟩
    · exact Eventually.of_forall (fun _ h => False.elim (hSmall h))
  obtain ⟨K, q, _, hQ, hRange, _, hEpsilon, hT1, _, hCurrent⟩ :=
    bernoulli_slow_prefix_log_convergence_with_constraints d z hd hsparse ν hWeak hC hMass
      R hSupport P hP
  let epsilon := fun n => logarithmicStageFraction C K (q n)
  have hNonneg : ∀ n, 0 ≤ epsilon n := fun n => (hRange n).1.le
  have hStage : Tendsto (logarithmicStageFraction C K) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨logarithmicStageFraction_tendsto C K,
      Eventually.of_forall (fun k => logarithmicStageFraction_pos hC K k)⟩
  have hAccuracy := diagonalAccuracy_tendsto.comp hQ
  have hBounds : ∀ᶠ n in atTop,
      (sparseBernoulliMatrixLaw n (d n)).real {x | diagonalAccuracy (q n) <
        |bernoulliMinorLogPrefix d z epsilon hNonneg n x - a (epsilon n)|} ≤ diagonalAccuracy (q n) ∧
      (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
          bernoulliMinorLogPrefix d z epsilon hNonneg n x + e (epsilon n) + diagonalAccuracy (q n) <
            squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)} ≤ diagonalAccuracy (q n) := by
    filter_upwards [hCurrent, hEpsilon.eventually (gt_mem_nhds hEpsilon0)] with n hn hSmall
    have h := hn hSmall.le (hNonneg n)
    exact ⟨h.1.le, h.2.le⟩
  have hMinorSlow := varying_probability_of_slow_stage_limits
    (fun n => sparseBernoulliMatrixLaw n (d n))
    (fun k n x => bernoulliMinorLogPrefixAt d z (logarithmicStageFraction C K k)
      (logarithmicStageFraction_pos hC K k).le n x)
    (fun k => a (logarithmicStageFraction C K k)) q _ hQ (hA.comp hStage)
    (hBounds.mono (fun _ h => h.1))
  have hError : Tendsto (fun n => e (epsilon n) + diagonalAccuracy (q n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, add_zero] using
      (hE.comp (hStage.comp hQ)).add hAccuracy
  have hUpperSlow : ∀ delta : ℝ, 0 < delta → Tendsto (fun n =>
      (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
          bernoulliMinorLogPrefix d z epsilon hNonneg n x + delta <
            squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)}) atTop (𝓝 0) := by
    intro delta hDelta
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAccuracy
      (Eventually.of_forall (fun _ => measureReal_nonneg))
    filter_upwards [hBounds, hError.eventually (gt_mem_nhds hDelta)] with n hn he
    apply le_trans (measureReal_mono (μ := sparseBernoulliMatrixLaw n (d n)) ?_) hn.2
    intro x hx
    rcases hx with hZero | hUpperFail
    · exact Or.inl hZero
    · exact Or.inr (by linarith)
  exact bernoulli_full_log_convergence_of_prefix_squeeze d z ν epsilon hNonneg
    hEpsilon hT1 hMinorSlow hUpperSlow

end CircularLaw
