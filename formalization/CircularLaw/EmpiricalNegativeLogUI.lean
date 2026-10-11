import CircularLaw.EmpiricalNegativeLogConvergence
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Negative logarithmic uniform integrability in probability

For each positive tolerance, a sufficiently large fixed threshold already
makes the empirical tail event tend to zero. This implies the literal
iterated limsup conclusion. Zero entries are included in every finite
threshold event because their negative logarithm is infinite.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

def EmpiricalNegativeLogTailEvent {n : ℕ} (s : Fin n → ℝ≥0) (T ε : ℝ) : Prop :=
  empiricalHasZero s ∨ ε < empiricalNegativeLogTail s T

theorem empirical_negative_log_UI_threshold {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ T : ℝ, T0 ≤ T →
      Tendsto (fun n => (μ n).real {ω | EmpiricalNegativeLogTailEvent (s n ω) T ε}) atTop (𝓝 0) := by
  have hResidual : Tendsto (fun T : ℕ => (∫ t, hermitizationNegativeLog t ∂ν) -
      ∫ t, clippedNegativeLog T t ∂ν) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := ∫ t, hermitizationNegativeLog t ∂ν)).sub
        (clippedNegativeLog_integral_tendsto hν)
  have hSmall : ∀ᶠ T : ℕ in atTop, |(∫ t, hermitizationNegativeLog t ∂ν) -
      ∫ t, clippedNegativeLog T t ∂ν| < ε / 4 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      hResidual.eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < ε / 4))
  obtain ⟨T0, hSmall0, hT0N⟩ := (hSmall.and (eventually_ge_atTop 1)).exists
  have hT0 : 0 < (T0 : ℝ) := by exact_mod_cast (show 0 < T0 by omega)
  refine ⟨2 * (T0 : ℝ), by positivity, ?_⟩
  intro T hT
  have hExcess := (empirical_negative_log_excess_convergence μ s ν hWeak hLog hν hMoment hT0.le)
    (ε / 4) (by linarith)
  have hZero := empirical_zero_probability_tendsto μ s ν hLog
  have hSum := hZero.add hExcess
  simp only [add_zero] at hSum
  have hBound (n : ℕ) :
      (μ n).real {ω | EmpiricalNegativeLogTailEvent (s n ω) T ε} ≤
        (μ n).real {ω | empiricalHasZero (s n ω)} +
        (μ n).real {ω | ε / 4 < |(empiricalNonnegativeMean (s n ω) hermitizationNegativeLog -
          empiricalNonnegativeMean (s n ω) (clippedNegativeLog T0)) -
          ((∫ t, hermitizationNegativeLog t ∂ν) - ∫ t, clippedNegativeLog T0 t ∂ν)|} := by
    apply (measureReal_mono (μ := μ n) (s₂ :=
      {ω | empiricalHasZero (s n ω)} ∪
      {ω | ε / 4 < |(empiricalNonnegativeMean (s n ω) hermitizationNegativeLog -
        empiricalNonnegativeMean (s n ω) (clippedNegativeLog T0)) -
        ((∫ t, hermitizationNegativeLog t ∂ν) - ∫ t, clippedNegativeLog T0 t ∂ν)|}) ?_).trans
      (measureReal_union_le _ _)
    intro ω hω
    change _ ∨ _
    rcases hω with hω | hω
    · exact Or.inl hω
    · by_cases hZeroω : empiricalHasZero (s n ω)
      · exact Or.inl hZeroω
      · right
        by_contra h
        simp only [Set.mem_setOf_eq] at h
        have hErr := le_of_not_gt h
        have hTail := (empirical_negative_log_tail_antitone (s n ω) hT).trans
          (empirical_negative_log_tail_bound (s n ω) hZeroω hT0.le)
        have hResidualLe := le_abs_self ((∫ t, hermitizationNegativeLog t ∂ν) -
          ∫ t, clippedNegativeLog T0 t ∂ν)
        have hDistanceLe := le_abs_self ((empiricalNonnegativeMean (s n ω) hermitizationNegativeLog -
          empiricalNonnegativeMean (s n ω) (clippedNegativeLog T0)) -
          ((∫ t, hermitizationNegativeLog t ∂ν) - ∫ t, clippedNegativeLog T0 t ∂ν))
        linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg)) (Eventually.of_forall hBound)

theorem empirical_negative_log_UI_limsup {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℝ => limsup (fun n => (μ n).real
      {ω | EmpiricalNegativeLogTailEvent (s n ω) T ε}) atTop) atTop (𝓝 0) := by
  obtain ⟨T0, _, hT0⟩ := empirical_negative_log_UI_threshold μ s ν hWeak hLog hν hMoment hε
  have hEq : (fun T : ℝ => limsup (fun n => (μ n).real
      {ω | EmpiricalNegativeLogTailEvent (s n ω) T ε}) atTop) =ᶠ[atTop] (fun _ => 0) :=
    (eventually_ge_atTop T0).mono (fun T hT => (hT0 T hT).limsup_eq)
  exact (tendsto_congr' hEq).mpr tendsto_const_nhds

end CircularLaw
