import CircularLaw.BernoulliGreedyMinorUpperLimit
import CircularLaw.BernoulliLogTailReduction

/-!
# The full manuscript Bernoulli hermitization interface

Under d tending to infinity and d/n tending to zero, every fixed nonzero
shift has the actual Gaussian weak singular limit, full extended logarithmic
convergence and second moment bounded in probability. The full-log bad
event includes all singular samples, even though real log is totalized.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

def BernoulliHermitizationTheorem : Prop :=
  ∀ d : ℕ → ℕ, Tendsto d atTop atTop → SparseDegrees d → ∀ z : ℂ, z ≠ 0 →
    EmpiricalWeakConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (bernoulliSingularArray d z) (gaussianShiftedSingularLimit z) ∧
    EmpiricalLogConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (bernoulliSingularArray d z) (gaussianShiftedSingularLimit z) ∧
    VaryingBoundedInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => bernoulliSingularSecondMoment (d n) z x)

theorem bernoulli_hermitization_theorem : BernoulliHermitizationTheorem := by
  intro d hDegree hSparse z hz
  exact ⟨bernoulli_shifted_weak_convergence d hDegree hSparse z,
    bernoulli_shifted_full_log_convergence d z hDegree hSparse hz,
    bernoulli_second_moment_bounded_in_probability d z hDegree hSparse⟩

theorem bernoulli_full_negative_log_converges_circular (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (hz : z ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
        ε < |squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x) -
          circularPaperPotential z|}) atTop (𝓝 0) := by
  simpa only [bernoulli_full_negative_log_eq_empirical, circularPaperPotential,
    neg_sub_neg, abs_sub_comm, gaussian_shifted_log_integral_eq_circular] using
    bernoulli_shifted_full_log_convergence d z hDegree hSparse hz ε hε

theorem bernoulli_full_negative_log_convergence_real (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (hz : z ≠ 0) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x))
      (circularPaperPotential z) := by
  intro ε hε
  exact varying_probability_event_of_subset (fun n => sparseBernoulliMatrixLaw n (d n))
    (fun _ _ h => Or.inr h) (bernoulli_full_negative_log_converges_circular d z hDegree hSparse hz hε)

end CircularLaw
