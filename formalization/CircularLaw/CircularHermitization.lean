import CircularLaw.BLCircularConvergence

/-!
# Direct hermitization for the full circular-law conclusion

The target measure and its potential are the actual uniform unit-disk
area measure. Almost-everywhere shifted-log-determinant convergence and
energy bounded in probability imply full bounded-Lipschitz convergence
of the ESD. The paper's negative potential convention is also supported.
The matrix model's logarithmic convergence remains a required input;
this theorem does not assume an ESD convergence or comparator theorem.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace CircularLaw

theorem matrix_circular_hermitization {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n))
    (hEnergy : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z) (circularLogPotential z)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω)) circularMeasure})
        atTop (𝓝 0) := by
  intro ε hε
  apply bounded_lipschitz_circular_convergence_of_compact_C2_tests μ A hEnergy _ hε
  intro φ hφ hSupport
  exact circular_compact_C2_test_convergence μ A hA hEnergy hLog φ hφ hSupport

theorem matrix_circular_hermitization_paper_sign {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n))
    (hEnergy : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => -normalizedLogDeterminant (A n ω) z) (circularPaperPotential z)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω)) circularMeasure})
        atTop (𝓝 0) := by
  apply matrix_circular_hermitization μ A hA hEnergy
  filter_upwards [hLog] with z hz
  simpa only [VaryingConvergesInProbability, circularPaperPotential,
    neg_sub_neg, abs_sub_comm] using hz

end CircularLaw
