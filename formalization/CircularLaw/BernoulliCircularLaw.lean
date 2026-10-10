import CircularLaw.BernoulliHermitizationTheorem
import CircularLaw.CircularHermitization

/-!
# The actual sparse Bernoulli circular law

The checked full logarithmic limit holds at every fixed nonzero shift,
hence almost everywhere in the plane. Energy bounded in probability and
direct hermitization give the full bounded-Lipschitz eigenvalue conclusion.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace CircularLaw

theorem bernoulli_log_determinant_converges_circular (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (hz : z ≠ 0) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => normalizedLogDeterminant (degreeNormalizedBernoulliMatrix (d n) x) z)
      (circularLogPotential z) := by
  simpa only [normalizedLogDeterminant, degreeNormalizedBernoulliMatrix,
    normalizedShiftedBernoulliMatrix, gaussian_shifted_log_integral_eq_circular] using
    (bernoulli_log_determinant_convergence_of_full_log d z (gaussianShiftedSingularLimit z)
      (bernoulli_shifted_full_log_convergence d z hDegree hSparse hz)).1

theorem sparse_bernoulli_circular_law (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      {x | ENNReal.ofReal ε < boundedLipschitzDistance
        (empiricalSpectralMeasure (degreeNormalizedBernoulliMatrix (d n) x)) circularMeasure})
      atTop (𝓝 0) := by
  apply matrix_circular_hermitization (fun n => sparseBernoulliMatrixLaw n (d n))
    (fun n x => degreeNormalizedBernoulliMatrix (d n) x)
  · intro n
    exact measurable_of_countable _
  · exact degree_normalized_bernoulli_energy_bounded_in_probability d hDegree hSparse
  · filter_upwards [Measure.ae_ne (volume : Measure ℂ) 0] with z hz
    exact bernoulli_log_determinant_converges_circular d z hDegree hSparse hz

end CircularLaw
