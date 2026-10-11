import CircularLaw.BernoulliSlowPrefixLimit
import CircularLaw.VaryingProbabilitySqueeze
import CircularLaw.SlowProbabilityLimits

/-!
# Assembling the actual Bernoulli full logarithmic limit from the squeeze

Both literal prefixes retain the manuscript's integer floors. The lower
comparison and normalization limit are supplied by checked proofs. The
minor-prefix convergence and the full-to-minor upper failure probabilities
are explicit remaining inputs. Singular samples are included in those
failure events and are proved to have vanishing probability.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology BigOperators

namespace CircularLaw

def bernoulliMinorLogPrefixAt (d : ℕ → ℕ) (z : ℂ) (epsilon : ℝ)
    (hNonneg : 0 ≤ epsilon) : ∀ n, BernoulliSquareSample n → ℝ :=
  fun n x => squareMinorNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
    (bernoulli_squeeze_lengths_le hNonneg).2 (bernoulliSqueezePrefixLength n epsilon)

def bernoulliMinorLogPrefix (d : ℕ → ℕ) (z : ℂ) (epsilon : ℕ → ℝ)
    (hNonneg : ∀ n, 0 ≤ epsilon n) : ∀ n, BernoulliSquareSample n → ℝ :=
  fun n x => bernoulliMinorLogPrefixAt d z (epsilon n) (hNonneg n) n x

theorem bernoulli_full_negative_log_eq_empirical (d : ℕ → ℕ) (z : ℂ) (n : ℕ)
    (x : BernoulliSquareSample n) :
    squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x) =
      -empiricalNonnegativeMean (bernoulliSingularArray d z n x)
        (fun t => Real.log (t : ℝ)) := by
  simp only [squareNegativeLogMean, empiricalNonnegativeMean, finiteMean,
    Fintype.card_fin, bernoulliSingularArray, squareSingularValuesNNReal, NNReal.coe_mk, neg_div]

theorem bernoulli_full_log_convergence_of_prefix_squeeze (d : ℕ → ℕ) (z : ℂ)
    (ν : Measure ℝ≥0) (epsilon : ℕ → ℝ) (hNonneg : ∀ n, 0 ≤ epsilon n)
    (hEpsilon : Tendsto epsilon atTop (𝓝 0))
    (hT1 : VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
        (bernoulliSqueezePrefixLength n (epsilon n)))
      (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν)))
    (hMinor : VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (bernoulliMinorLogPrefix d z epsilon hNonneg)
      (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν)))
    (hUpper : ∀ delta : ℝ, 0 < delta → Tendsto (fun n =>
      (sparseBernoulliMatrixLaw n (d n)).real {x |
        empiricalHasZero (bernoulliSingularArray d z n x) ∨
        bernoulliMinorLogPrefix d z epsilon hNonneg n x + delta <
          squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)}) atTop (𝓝 0)) :
    EmpiricalLogConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (bernoulliSingularArray d z) ν := by
  have hLower := varying_probability_mul_deterministic
    (fun n => sparseBernoulliMatrixLaw n (d n)) hT1
    (bernoulli_squeeze_normalizing_factor_tendsto hEpsilon)
  simp only [one_mul] at hLower
  have hSqueeze : ∀ delta : ℝ, 0 < delta → Tendsto (fun n =>
      (sparseBernoulliMatrixLaw n (d n)).real {x |
        empiricalHasZero (bernoulliSingularArray d z n x) ∨
        squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x) <
          ((n : ℝ) / bernoulliSqueezePrefixLength n (epsilon n)) *
            squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
              (bernoulliSqueezePrefixLength n (epsilon n)) - delta ∨
        bernoulliMinorLogPrefix d z epsilon hNonneg n x + delta <
          squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)}) atTop (𝓝 0) := by
    intro delta hDelta
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hUpper delta hDelta)
      (Eventually.of_forall (fun _ => measureReal_nonneg))
    filter_upwards [bernoulli_squeeze_prefix_eventually_positive hEpsilon] with n hn
    refine measureReal_mono (μ := sparseBernoulliMatrixLaw n (d n))
      (fun x hx => ?_) (by finiteness)
    rcases hx with hZero | hLowerFail | hUpperFail
    · exact Or.inl hZero
    · by_cases hZero : empiricalHasZero (bernoulliSingularArray d z n x)
      · exact Or.inl hZero
      · have hPos : ∀ j, 0 < orderedSquareSingularValues
            (normalizedShiftedBernoulliMatrix (d n) z x) j := by
          intro j
          have hsj : 0 < bernoulliSingularArray d z n x j :=
            lt_of_le_of_ne (zero_le _) (fun h => hZero ⟨j, h.symm⟩)
          change 0 < (bernoulliSingularArray d z n x j : ℝ)
          exact_mod_cast hsj
        have hBound := square_full_negative_log_ge_prefix
          (normalizedShiftedBernoulliMatrix (d n) z x) hPos hn
          (bernoulli_squeeze_prefix_le (hNonneg n))
        exact False.elim (by linarith)
    · exact Or.inr hUpperFail
  obtain ⟨hMean, hZero⟩ := varying_probability_of_asymptotic_squeeze
    (fun n => sparseBernoulliMatrixLaw n (d n))
    (fun n x => squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x))
    (fun n x => ((n : ℝ) / bernoulliSqueezePrefixLength n (epsilon n)) *
      squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
        (bernoulliSqueezePrefixLength n (epsilon n)))
    (bernoulliMinorLogPrefix d z epsilon hNonneg)
    (fun n => {x | empiricalHasZero (bernoulliSingularArray d z n x)})
    (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν)) hLower hMinor hSqueeze
  have hReal := varying_probability_neg (fun n => sparseBernoulliMatrixLaw n (d n)) hMean
  simp only [bernoulli_full_negative_log_eq_empirical, neg_neg] at hReal
  exact empirical_log_convergence_of_real_and_zero_probability
    (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν hReal hZero

end CircularLaw
