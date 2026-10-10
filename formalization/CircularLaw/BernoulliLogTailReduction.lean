import CircularLaw.BernoulliSecondMoment
import CircularLaw.NegativeLogUniformIntegrability

/-!
# Applying the checked logarithmic-tail lemma to the actual Bernoulli matrix

The matrix law, singular-value array and tight second moment are supplied
by checked proofs. Weak convergence and full logarithmic convergence to
the Gaussian limit are explicit remaining hypotheses of this reduction;
these theorems do not assert that those inputs have been proved.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace CircularLaw

def bernoulliSingularArray (d : ℕ → ℕ) (z : ℂ) :
    ∀ n, BernoulliSquareSample n → Fin n → ℝ≥0 :=
  fun n x => squareSingularValuesNNReal (normalizedShiftedBernoulliMatrix (d n) z x)

theorem bernoulliSingularArray_measurable (d : ℕ → ℕ) (z : ℂ) (n : ℕ) (j : Fin n) :
    Measurable (fun x : BernoulliSquareSample n => bernoulliSingularArray d z n x j) :=
  measurable_of_countable _

theorem bernoulliSingularArray_antitone (d : ℕ → ℕ) (z : ℂ) (n : ℕ)
    (x : BernoulliSquareSample n) : Antitone (bernoulliSingularArray d z n x) := by
  intro i j hij
  exact orderedSquareSingularValues_antitone _ hij

theorem bernoulliSingularArray_second_moment_bounded (d : ℕ → ℕ) (z : ℂ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d) :
    VaryingBoundedInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => empiricalNonnegativeMean (bernoulliSingularArray d z n x)
        (fun t => (t : ℝ) ^ 2)) := by
  have hMean (n : ℕ) (x : BernoulliSquareSample n) :
      bernoulliSingularSecondMoment (d n) z x =
        empiricalNonnegativeMean (bernoulliSingularArray d z n x) (fun t => (t : ℝ) ^ 2) :=
    empiricalNonnegativeMeasure_integral _ _
  have hFun := funext (fun n => funext (hMean n))
  rw [← hFun]
  exact bernoulli_second_moment_bounded_in_probability d z hd hsparse

theorem bernoulli_negative_log_UI_of_convergence (d : ℕ → ℕ) (z : ℂ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d) (ν : Measure ℝ≥0)
    (hν : FiniteLogarithmicIntegral ν)
    (hWeak : EmpiricalWeakConvergenceInProbability
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν)
    (hLog : EmpiricalLogConvergenceInProbability
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℝ => limsup (fun n =>
      (sparseBernoulliMatrixLaw n (d n)).real {x | ENNReal.ofReal ε <
        ∫⁻ t, extendedNegativeLogTail T t ∂bernoulliSingularMeasure (d n) z x}) atTop)
      atTop (𝓝 0) :=
  negative_log_tail_measure_limsup (fun n => sparseBernoulliMatrixLaw n (d n))
    (bernoulliSingularArray d z) ν hWeak hLog hν
    (bernoulliSingularArray_second_moment_bounded d z hd hsparse) hε

theorem bernoulli_bottom_log_tail_of_convergence (d : ℕ → ℕ) (z : ℂ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d) (ν : Measure ℝ≥0)
    (hν : FiniteLogarithmicIntegral ν)
    (hWeak : EmpiricalWeakConvergenceInProbability
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν)
    (hLog : EmpiricalLogConvergenceInProbability
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν)
    (r : ℕ → ℕ) (hr : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real {x | ENNReal.ofReal ε <
      empiricalExtendedBottomNegativeLog (bernoulliSingularArray d z n x) (r n)})
      atTop (𝓝 0) :=
  bottom_negative_log_extended_convergence (fun n => sparseBernoulliMatrixLaw n (d n))
    (bernoulliSingularArray d z) ν hWeak hLog hν
    (bernoulliSingularArray_second_moment_bounded d z hd hsparse) r hr hε

end CircularLaw
