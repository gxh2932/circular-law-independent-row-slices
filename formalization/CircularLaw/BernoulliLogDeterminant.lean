import CircularLaw.BernoulliLogSqueeze
import CircularLaw.SquareSingularDeterminant

/-!
# From the actual Bernoulli singular-value logarithms to its determinant

Full empirical logarithmic convergence implies convergence of the
normalized logarithmic determinant and vanishing singular probability.
The value assigned on singular samples is irrelevant to the finite limit.
The required empirical logarithmic convergence remains an explicit input.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem bernoulli_empirical_zero_iff_det_zero (d : ℕ → ℕ) (z : ℂ) (n : ℕ)
    (x : BernoulliSquareSample n) :
    empiricalHasZero (bernoulliSingularArray d z n x) ↔
      (normalizedShiftedBernoulliMatrix (d n) z x).det = 0 :=
  square_singular_has_zero_iff_det_zero _

theorem bernoulli_log_det_eq_empirical_log (d : ℕ → ℕ) (z : ℂ) (n : ℕ)
    (x : BernoulliSquareSample n) (hDet : (normalizedShiftedBernoulliMatrix (d n) z x).det ≠ 0) :
    Real.log ‖(normalizedShiftedBernoulliMatrix (d n) z x).det‖ / n =
      empiricalNonnegativeMean (bernoulliSingularArray d z n x)
        (fun t => Real.log (t : ℝ)) := by
  have h := square_negative_log_mean_eq_log_det (normalizedShiftedBernoulliMatrix (d n) z x) hDet
  rw [bernoulli_full_negative_log_eq_empirical] at h
  linarith

theorem bernoulli_log_determinant_convergence_of_full_log (d : ℕ → ℕ) (z : ℂ)
    (ν : Measure ℝ≥0)
    (hLog : EmpiricalLogConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (bernoulliSingularArray d z) ν) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => Real.log ‖(normalizedShiftedBernoulliMatrix (d n) z x).det‖ / n)
      (∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) ∧
      Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
        {x | (normalizedShiftedBernoulliMatrix (d n) z x).det = 0}) atTop (𝓝 0) := by
  have hZero := empirical_zero_probability_tendsto (fun n => sparseBernoulliMatrixLaw n (d n))
    (bernoulliSingularArray d z) ν hLog
  constructor
  · apply varying_probability_of_agreement_outside_bad_event
      (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n => {x | empiricalHasZero (bernoulliSingularArray d z n x)})
      (empirical_log_convergence_real (fun n => sparseBernoulliMatrixLaw n (d n))
        (bernoulliSingularArray d z) ν hLog) hZero
    apply Eventually.of_forall
    intro n x hx
    exact bernoulli_log_det_eq_empirical_log d z n x
      ((bernoulli_empirical_zero_iff_det_zero d z n x).not.mp hx)
  · simpa only [bernoulli_empirical_zero_iff_det_zero] using hZero

end CircularLaw
