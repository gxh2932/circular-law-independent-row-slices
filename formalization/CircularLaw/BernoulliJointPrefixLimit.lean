import CircularLaw.BernoulliSlowPrefixLimit
import CircularLaw.SlowProbabilityLimits

/-!
# The actual Bernoulli T1 limit and an auxiliary limit with one slow choice

The auxiliary variable may be the corrected upper comparison once its
fixed-fraction limits have been established. Its convergence is an
explicit hypothesis; this theorem supplies the common slow choice and
the passage from fixed-fraction limits to the joint probability limits.
No actual minor or Gaussian weak-convergence result is assumed as an axiom.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem bernoulli_slow_prefix_joint_log_convergence (d : ℕ → ℕ) (z : ℂ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν)
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    (R : ℝ) (hSupport : ν {x : ℝ≥0 | R < (x : ℝ)} = 0)
    (g : ℝ → ∀ n, BernoulliSquareSample n → ℝ) (a : ℝ → ℝ)
    (hAux : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (g epsilon) (a epsilon))
    (hA : Tendsto a (𝓝[>] (0 : ℝ))
      (𝓝 (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν)))) :
    ∃ (K : ℕ) (q : ℕ → ℕ), Monotone q ∧ Tendsto q atTop atTop ∧
      (∀ n, 0 < logarithmicStageFraction C K (q n) ∧ logarithmicStageFraction C K (q n) ≤ 1) ∧
      Antitone (fun n => logarithmicStageFraction C K (q n)) ∧
      Tendsto (fun n => logarithmicStageFraction C K (q n)) atTop (𝓝 0) ∧
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (fun n x => squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
          (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n))))
        (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν)) ∧
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (fun n x => g (logarithmicStageFraction C K (q n)) n x)
        (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν)) ∧
      Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalPrefixHasZero (bernoulliSingularArray d z n x)
          (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n)))}) atTop (𝓝 0) := by
  let P := fun k epsilon n => (sparseBernoulliMatrixLaw n (d n)).real
    {x | diagonalAccuracy k < |g epsilon n x - a epsilon|} ≤ diagonalAccuracy k
  have hP : ∀ k epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ᶠ n in atTop, P k epsilon n := by
    intro k epsilon hPos hOne
    exact ((hAux epsilon hPos hOne (diagonalAccuracy k) (diagonalAccuracy_pos k)).eventually
      (gt_mem_nhds (diagonalAccuracy_pos k))).mono (fun _ h => h.le)
  obtain ⟨K, q, hMono, hQ, hRange, hAnti, hEpsilon, hLog, hZero, hCurrent⟩ :=
    bernoulli_slow_prefix_log_convergence_with_constraints d z hd hsparse ν hWeak hC hMass
      R hSupport P hP
  refine ⟨K, q, hMono, hQ, hRange, hAnti, hEpsilon, hLog, ?_, hZero⟩
  have hStage : Tendsto (logarithmicStageFraction C K) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨logarithmicStageFraction_tendsto C K,
      Eventually.of_forall (fun k => logarithmicStageFraction_pos hC K k)⟩
  exact varying_probability_of_slow_stage_limits (fun n => sparseBernoulliMatrixLaw n (d n))
    (fun k n x => g (logarithmicStageFraction C K k) n x)
    (fun k => a (logarithmicStageFraction C K k)) q _ hQ (hA.comp hStage) hCurrent

end CircularLaw
