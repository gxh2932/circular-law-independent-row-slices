import CircularLaw.RoundedLogPrefixConvergence
import CircularLaw.BernoulliPrefixConvergence
import CircularLaw.SmallValueLogIntegrability

/-!
# Full Bernoulli T1 convergence from the remaining Gaussian inputs

The actual Bernoulli law, literal manuscript prefix, tight second moment
and finite limiting logarithmic integral are supplied by checked proofs.
A positive decreasing fraction is chosen sufficiently slowly, and the
full signed prefix potential converges, with retained zeros having
vanishing probability. Bernoulli weak convergence and limiting-law mass
and support bounds remain explicit arguments in this reusable theorem.
The actual Gaussian mass and support bounds are proved separately and
discharged in `BernoulliGaussianPrefix.lean`.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem bernoulli_slow_prefix_log_convergence_with_constraints (d : ℕ → ℕ) (z : ℂ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν)
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    (R : ℝ) (hSupport : ν {x : ℝ≥0 | R < (x : ℝ)} = 0)
    (P : ℕ → ℝ → ℕ → Prop)
    (hP : ∀ k epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ᶠ n in atTop, P k epsilon n) :
    ∃ (K : ℕ) (q : ℕ → ℕ), Monotone q ∧ Tendsto q atTop atTop ∧
      (∀ n, 0 < logarithmicStageFraction C K (q n) ∧ logarithmicStageFraction C K (q n) ≤ 1) ∧
      Antitone (fun n => logarithmicStageFraction C K (q n)) ∧
      Tendsto (fun n => logarithmicStageFraction C K (q n)) atTop (𝓝 0) ∧
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (fun n x => squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
          (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n))))
        (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν)) ∧
      Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalPrefixHasZero (bernoulliSingularArray d z n x)
          (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n)))}) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, P (q n) (logarithmicStageFraction C K (q n)) n := by
  obtain ⟨K, hK⟩ := exists_logarithmic_stage_offset C
  have hν := finite_logarithmic_integral_of_mass_and_support ν hC hMass R hSupport
  obtain ⟨q, hMono, hQ, hLog, hZero, hConstraint⟩ :=
    exists_slow_rounded_log_prefix_convergence_with_constraints
    (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν hWeak
    (bernoulliSingularArray_antitone d z) hν
      (bernoulliSingularArray_second_moment_bounded d z hd hsparse) hC hMass hK
      (fun k n => P k (logarithmicStageFraction C K k) n)
      (fun k => hP k _ (logarithmicStageFraction_pos hC K k)
        (logarithmicStageFraction_le_one hC hK k))
  refine ⟨K, q, hMono, hQ, (fun n => ⟨logarithmicStageFraction_pos hC K (q n),
    logarithmicStageFraction_le_one hC hK (q n)⟩), ?_, ?_, ?_, hZero, hConstraint⟩
  · intro m n hmn
    exact logarithmicStageFraction_antitone hC.le K (hMono hmn)
  · exact (logarithmicStageFraction_tendsto C K).comp hQ
  · have hMean (n : ℕ) (x : BernoulliSquareSample n) :
        roundedLogPotentialPrefixMean (bernoulliSingularArray d z n x)
          (logarithmicStageFraction C K (q n)) (logarithmicStageFraction_pos hC K (q n)).le =
        squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
          (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n))) :=
      bernoulli_prefix_negative_log_eq_square_prefix d z x
        (bernoulli_squeeze_prefix_le (logarithmicStageFraction_pos hC K (q n)).le)
    have hFun := funext (fun n => funext (hMean n))
    rw [hFun] at hLog
    exact hLog

theorem bernoulli_slow_prefix_log_convergence (d : ℕ → ℕ) (z : ℂ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν)
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    (R : ℝ) (hSupport : ν {x : ℝ≥0 | R < (x : ℝ)} = 0) :
    ∃ (K : ℕ) (q : ℕ → ℕ),
      (∀ n, 0 < logarithmicStageFraction C K (q n) ∧ logarithmicStageFraction C K (q n) ≤ 1) ∧
      Antitone (fun n => logarithmicStageFraction C K (q n)) ∧
      Tendsto (fun n => logarithmicStageFraction C K (q n)) atTop (𝓝 0) ∧
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (fun n x => squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
          (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n))))
        (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν)) ∧
      Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalPrefixHasZero (bernoulliSingularArray d z n x)
          (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n)))}) atTop (𝓝 0) := by
  obtain ⟨K, q, _, _, hRange, hAnti, hEpsilon, hLog, hZero, _⟩ :=
    bernoulli_slow_prefix_log_convergence_with_constraints d z hd hsparse ν hWeak hC hMass
      R hSupport (fun _ _ _ => True) (fun _ _ _ _ => Eventually.of_forall (fun _ => trivial))
  exact ⟨K, q, hRange, hAnti, hEpsilon, hLog, hZero⟩

end CircularLaw
