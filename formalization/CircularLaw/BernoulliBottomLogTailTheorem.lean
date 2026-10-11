import CircularLaw.BernoulliHermitizationTheorem

/-!
# The actual Bernoulli bottom logarithmic tail

The full hermitization interface and the checked finite logarithmic Gaussian
integral supply every hypothesis of the negative-log uniform-integrability
and bottom-tail deductions. Zero singular values retain infinite negative log.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace CircularLaw

def BernoulliBottomLogTailTheorem : Prop :=
  ∀ d : ℕ → ℕ, Tendsto d atTop atTop → SparseDegrees d → ∀ z : ℂ, z ≠ 0 →
    ∀ r : ℕ → ℕ, Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
        {x | ENNReal.ofReal ε < empiricalExtendedBottomNegativeLog (bernoulliSingularArray d z n x) (r n)})
        atTop (𝓝 0)

theorem bernoulli_bottom_log_tail_theorem : BernoulliBottomLogTailTheorem := by
  intro d hDegree hSparse z hz r hr ε hε
  exact bernoulli_bottom_log_tail_of_convergence d z hDegree hSparse (gaussianShiftedSingularLimit z)
    (gaussian_shifted_limit_finite_logarithmic_integral z)
    (bernoulli_shifted_weak_convergence d hDegree hSparse z)
    (bernoulli_shifted_full_log_convergence d z hDegree hSparse hz) r hr hε

theorem bernoulli_negative_log_uniform_integrability (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (hz : z ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℝ => limsup (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      {x | ENNReal.ofReal ε < ∫⁻ t, extendedNegativeLogTail T t
        ∂bernoulliSingularMeasure (d n) z x}) atTop) atTop (𝓝 0) := by
  exact bernoulli_negative_log_UI_of_convergence d z hDegree hSparse (gaussianShiftedSingularLimit z)
    (gaussian_shifted_limit_finite_logarithmic_integral z)
    (bernoulli_shifted_weak_convergence d hDegree hSparse z)
    (bernoulli_shifted_full_log_convergence d z hDegree hSparse hz) hε

end CircularLaw
