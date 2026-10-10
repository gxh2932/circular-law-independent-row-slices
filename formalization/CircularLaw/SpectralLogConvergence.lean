import CircularLaw.SpectralLogPotential
import CircularLaw.BernoulliLogDeterminant

/-!
# Transfer of actual singular logarithms to ESD logarithmic potentials

Finite extended neighborhoods include every singular sample in the bad
event. The singular-log convergence hypotheses remain explicit; no
Gaussian or Bernoulli limiting law is assumed as an axiom.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem extended_spectral_log_potential_outside_interval {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (a ε : ℝ) :
    ¬((a - ε : ℝ) ≤ extendedSpectralLogPotential A z ∧
      extendedSpectralLogPotential A z ≤ (a + ε : ℝ)) ↔
      (A - z • 1).det = 0 ∨ ε < |spectralLogPotential A z - a| := by
  unfold extendedSpectralLogPotential
  by_cases hz : z ∈ A.charpoly.roots
  · simp only [hz, if_true]
    have hDet := (shifted_det_zero_iff_characteristic_root A z).mpr hz
    simp only [hDet, true_or, iff_true]
    intro h
    exact (not_le.mpr (EReal.bot_lt_coe (a - ε))) h.1
  · have hDet := (shifted_det_zero_iff_characteristic_root A z).not.mpr hz
    simp only [hz, if_false, hDet, false_or, EReal.coe_le_coe_iff]
    rw [← not_le]
    apply not_congr
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem spectral_log_potential_convergence_of_singular_log {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (ν : Measure ℝ≥0)
    (hLog : EmpiricalLogConvergenceInProbability μ
      (fun n ω => squareSingularValuesNNReal (A n ω - z • 1)) ν) :
    VaryingConvergesInProbability μ (fun n ω => spectralLogPotential (A n ω) z)
      (∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) ∧
      Tendsto (fun n => (μ n).real {ω | (A n ω - z • 1).det = 0}) atTop (𝓝 0) := by
  have hZero := empirical_zero_probability_tendsto μ _ ν hLog
  constructor
  · apply varying_probability_of_agreement_outside_bad_event μ
      (fun n => {ω | empiricalHasZero (squareSingularValuesNNReal (A n ω - z • 1))})
      (empirical_log_convergence_real μ _ ν hLog) hZero
    apply Eventually.of_forall
    intro n ω hω
    have hDet := (square_singular_has_zero_iff_det_zero _).not.mp hω
    rw [spectral_log_potential_eq_log_determinant _ _ hDet]
    exact (shifted_singular_empirical_mean_eq_log_determinant _ _ hDet).symm
  · simpa only [square_singular_has_zero_iff_det_zero] using hZero

theorem spectral_extended_log_potential_convergence_of_singular_log {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (ν : Measure ℝ≥0)
    (hLog : EmpiricalLogConvergenceInProbability μ
      (fun n ω => squareSingularValuesNNReal (A n ω - z • 1)) ν) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω |
      ¬(((∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) - ε : ℝ) ≤
        extendedSpectralLogPotential (A n ω) z ∧
        extendedSpectralLogPotential (A n ω) z ≤
        ((∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) + ε : ℝ))}) atTop (𝓝 0) := by
  intro ε hε
  simpa only [← shifted_singular_extended_log_eq_spectral_potential,
    empiricalExtendedLogIntegral_outside_interval] using hLog ε hε

def degreeNormalizedBernoulliMatrix {n : ℕ} (d : ℕ)
    (x : BernoulliSquareSample n) : Matrix (Fin n) (Fin n) ℂ :=
  (Real.sqrt (d : ℝ) : ℂ)⁻¹ • bernoulliSquareMatrix x

theorem bernoulli_spectral_log_potential_convergence_of_full_log (d : ℕ → ℕ) (z : ℂ)
    (ν : Measure ℝ≥0)
    (hLog : EmpiricalLogConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (bernoulliSingularArray d z) ν) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => spectralLogPotential (degreeNormalizedBernoulliMatrix (d n) x) z)
      (∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) ∧
      Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
        {x | (normalizedShiftedBernoulliMatrix (d n) z x).det = 0}) atTop (𝓝 0) := by
  exact spectral_log_potential_convergence_of_singular_log _
    (fun n x => degreeNormalizedBernoulliMatrix (d n) x) z ν hLog

end CircularLaw
