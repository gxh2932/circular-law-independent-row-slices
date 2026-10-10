import CircularLaw.BernoulliCenteredWeakLimit
import CircularLaw.InterlacedEmpiricalWeakTransfer

/-!
# The actual sparse Bernoulli weak singular law at every complex shift

The checked centered moments and Gaussian count identification give the
centered weak law. The actual rank-one mean supplies both one-index
interlacings. The compact Gaussian support and bounded continuous mean
comparison restore that mean, proving the actual uncentered law without
assuming its higher-moment convergence. This discharges the sparse weak
transfer input used by the Bernoulli hermitization development.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem bernoulli_shifted_weak_convergence (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (z : ℂ) :
    EmpiricalWeakConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => squareSingularValuesNNReal (normalizedShiftedBernoulliMatrix (d n) z x))
      (gaussianShiftedSingularLimit z) := by
  apply empirical_weak_convergence_of_one_index_interlacing
    (fun n => sparseBernoulliMatrixLaw n (d n)) _
    (fun n x => squareSingularValuesNNReal (normalizedCenteredBernoulliMatrix (d n) x - z • 1))
    (gaussianShiftedSingularLimit z) (128 + ‖z‖) (by positivity)
    (gaussian_shifted_limit_support z)
  · intro n x
    exact orderedSquareSingularValues_antitone _
  · intro n x
    exact orderedSquareSingularValues_antitone _
  · intro n x i j h
    exact (bernoulli_centering_singular_values_interlace (d n) z x i j h).1
  · intro n x i j h
    exact (bernoulli_centering_singular_values_interlace (d n) z x i j h).2
  · exact bernoulli_centered_shifted_weak_convergence d hDegree hSparse z

end CircularLaw
