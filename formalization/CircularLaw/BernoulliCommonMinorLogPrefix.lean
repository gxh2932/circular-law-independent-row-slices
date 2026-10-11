import CircularLaw.BernoulliMinorLogStageBounds
import CircularLaw.BernoulliGaussianCircularPrefix

/-!
# A common slow fraction for the actual full and minor logarithmic prefixes

The actual minor weak law, retained-value probabilities, moment bound and
uniform limiting-law clipping errors supply every minor premise. One
selector enforces these bounds together with the actual full-matrix T1
proof and any additional eventual constraints. Both literal manuscript
prefixes converge to the circular potential with the ambient denominator.
The full-to-minor upper comparison remains a separate input.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem bernoulli_common_minor_log_prefix_with_constraints (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    (P : ℕ → ℝ → ℕ → Prop)
    (hP : ∀ k epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ᶠ n in atTop, P k epsilon n) :
    ∃ (K : ℕ) (q : ℕ → ℕ), Monotone q ∧ Tendsto q atTop atTop ∧
      (∀ n, 0 < logarithmicStageFraction 48 K (q n) ∧ logarithmicStageFraction 48 K (q n) ≤ 1) ∧
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (fun n x => squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
          (bernoulliSqueezePrefixLength n (logarithmicStageFraction 48 K (q n)))) (circularPaperPotential z) ∧
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (fun n x => bernoulliMinorLogPrefixAt d z (logarithmicStageFraction 48 K (q n))
          (logarithmicStageFraction_pos (by norm_num : (0 : ℝ) < 48) K (q n)).le n x)
        (circularPaperPotential z) ∧
      Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real {x |
        empiricalPrefixHasZero (minorLogStageArray d z K (q n) n x)
          (bernoulliSqueezePrefixLength n (logarithmicStageFraction 48 K (q n)))}) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, P (q n) (logarithmicStageFraction 48 K (q n)) n := by
  obtain ⟨K, hK⟩ := exists_logarithmic_stage_offset (48 : ℝ)
  let Q := fun k n =>
    (logarithmicStageFraction 48 K k ≤ 1 / 2 → MinorLogStageReady d z K k n) ∧
      P k (logarithmicStageFraction 48 K k) n
  have hQEventual (k : ℕ) : ∀ᶠ n in atTop, Q k n := by
    have hMinor : ∀ᶠ n in atTop,
        logarithmicStageFraction 48 K k ≤ 1 / 2 → MinorLogStageReady d z K k n := by
      by_cases hHalf : logarithmicStageFraction 48 K k ≤ 1 / 2
      · exact (bernoulli_minor_log_stage_ready_eventually d z hDegree hSparse K k hHalf).mono
          (fun _ hn _ => hn)
      · exact Eventually.of_forall (fun _ h => False.elim (hHalf h))
    exact hMinor.and (hP k _ (logarithmicStageFraction_pos (by norm_num) K k)
      (logarithmicStageFraction_le_one (by norm_num) hK k))
  obtain ⟨q, hMono, hQ, hT1, _, hCurrent⟩ :=
    exists_slow_rounded_log_prefix_convergence_with_constraints
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z)
      (gaussianShiftedSingularLimit z) (bernoulli_shifted_weak_convergence d hDegree hSparse z)
      (bernoulliSingularArray_antitone d z) (gaussian_shifted_limit_finite_logarithmic_integral z)
      (bernoulliSingularArray_second_moment_bounded d z hDegree hSparse)
      (by norm_num : (0 : ℝ) < 48) (fun _ ht => gaussian_shifted_limit_small_mass z ht)
      hK Q hQEventual
  have hRange (n : ℕ) : 0 < logarithmicStageFraction 48 K (q n) ∧
      logarithmicStageFraction 48 K (q n) ≤ 1 :=
    ⟨logarithmicStageFraction_pos (by norm_num : (0 : ℝ) < 48) K (q n),
      logarithmicStageFraction_le_one (by norm_num : (0 : ℝ) < 48) hK (q n)⟩
  have hReady : ∀ᶠ n in atTop, MinorLogStageReady d z K (q n) n := by
    filter_upwards [hCurrent,
      hQ.eventually ((logarithmicStageFraction_tendsto 48 K).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))] with n hn hh
    exact hn.1 hh.le
  have hStageBound : ∀ᶠ n in atTop, (sparseBernoulliMatrixLaw n (d n)).real {x |
      minorLogStageTolerance K z (q n) < |bernoulliMinorLogPrefixAt d z
        (logarithmicStageFraction 48 K (q n)) (hRange n).1.le n x - minorLogStageLimit K z (q n)|} ≤
      4 * diagonalAccuracy (q n) := by
    filter_upwards [hReady,
      hQ.eventually ((logarithmicStageFraction_tendsto 48 K).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))),
      hQ.eventually (minor_log_stage_positive_cutoff_tendsto.eventually (eventually_ge_atTop
        (Real.log (128 + ‖z‖))))] with n hn hh ht
    exact bernoulli_minor_log_stage_deviation_probability_bound d z K (q n) n hh.le ht hn
  have hMinor : VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => bernoulliMinorLogPrefixAt d z (logarithmicStageFraction 48 K (q n))
        (hRange n).1.le n x) (circularPaperPotential z) := by
    have hTolerance := ((minor_log_stage_tolerance_tendsto K z).comp hQ).add
      ((((minor_log_stage_limit_tendsto K z).comp hQ).sub_const (circularPaperPotential z)).abs)
    simp only [sub_self, abs_zero, add_zero] at hTolerance
    have hAccuracy := (diagonalAccuracy_tendsto.comp hQ).const_mul 4
    simp only [mul_zero] at hAccuracy
    apply varying_probability_of_vanishing_tolerances
      (fun n => sparseBernoulliMatrixLaw n (d n)) hTolerance hAccuracy
    filter_upwards [hStageBound] with n hn
    apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n (d n)) ?_).trans hn
    intro x hx
    have hTriangle := abs_sub_le
      (bernoulliMinorLogPrefixAt d z (logarithmicStageFraction 48 K (q n)) (hRange n).1.le n x)
      (minorLogStageLimit K z (q n)) (circularPaperPotential z)
    change minorLogStageTolerance K z (q n) +
      |minorLogStageLimit K z (q n) - circularPaperPotential z| <
      |bernoulliMinorLogPrefixAt d z (logarithmicStageFraction 48 K (q n)) (hRange n).1.le n x -
        circularPaperPotential z| at hx
    change minorLogStageTolerance K z (q n) <
      |bernoulliMinorLogPrefixAt d z (logarithmicStageFraction 48 K (q n)) (hRange n).1.le n x -
        minorLogStageLimit K z (q n)|
    linarith
  have hZero : Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real {x |
      empiricalPrefixHasZero (minorLogStageArray d z K (q n) n x)
        (bernoulliSqueezePrefixLength n (logarithmicStageFraction 48 K (q n)))}) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (diagonalAccuracy_tendsto.comp hQ) (Eventually.of_forall (fun _ => measureReal_nonneg))
    filter_upwards [hReady] with n hn
    apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n (d n)) ?_).trans hn.2.2.2.1.le
    intro x hx
    exact empirical_prefix_zero_subset_small _ (Real.exp_pos _) hx
  have hFun : (fun n x => roundedLogPotentialPrefixMean (bernoulliSingularArray d z n x)
      (logarithmicStageFraction 48 K (q n)) (hRange n).1.le) =
      (fun n x => squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
        (bernoulliSqueezePrefixLength n (logarithmicStageFraction 48 K (q n)))) := by
    funext n x
    exact bernoulli_prefix_negative_log_eq_square_prefix d z x
      (bernoulli_squeeze_prefix_le (hRange n).1.le)
  rw [hFun] at hT1
  rw [gaussian_shifted_log_integral_eq_circular] at hT1
  exact ⟨K, q, hMono, hQ, hRange, hT1, hMinor, hZero, hCurrent.mono (fun _ h => h.2)⟩

theorem bernoulli_common_minor_log_prefix_convergence (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) :
    ∃ (epsilon : ℕ → ℝ) (hNonneg : ∀ n, 0 ≤ epsilon n),
      (∀ n, 0 < epsilon n ∧ epsilon n ≤ 1) ∧
      Antitone epsilon ∧ Tendsto epsilon atTop (𝓝 0) ∧
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (fun n x => squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
          (bernoulliSqueezePrefixLength n (epsilon n))) (circularPaperPotential z) ∧
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (bernoulliMinorLogPrefix d z epsilon hNonneg)
        (circularPaperPotential z) := by
  obtain ⟨K, q, hMono, hQ, hRange, hT1, hMinor, _, _⟩ :=
    bernoulli_common_minor_log_prefix_with_constraints d z hDegree hSparse
      (fun _ _ _ => True) (fun _ _ _ _ => Eventually.of_forall (fun _ => trivial))
  refine ⟨fun n => logarithmicStageFraction 48 K (q n), fun n => (hRange n).1.le,
    hRange, ?_, ?_, hT1, hMinor⟩
  · intro m n hmn
    exact logarithmicStageFraction_antitone (by norm_num : (0 : ℝ) ≤ 48) K (hMono hmn)
  · exact (logarithmicStageFraction_tendsto 48 K).comp hQ

end CircularLaw
