import CircularLaw.BottomLogGeometry

/-!
# Vanishing bottom logarithmic sums for `r=o(n)`

The deterministic threshold part tends to zero. The checked uniform
integrability supplies a fixed threshold for the remaining tail. The
extended bottom sum includes infinity precisely when a selected value is zero.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

theorem empirical_bottom_log_convergence {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)))
    (r : ℕ → ℕ) (hr : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real {ω | EmpiricalBottomLogTailEvent (s n ω) (r n) ε}) atTop (𝓝 0) := by
  obtain ⟨T, hT, hTail⟩ := empirical_negative_log_UI_threshold μ s ν hWeak hLog hν hMoment
    (show 0 < ε / 2 by linarith)
  have hTailT := hTail T le_rfl
  have hTr : Tendsto (fun n => T * ((r n : ℝ) / n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := T)).mul hr
  have hSmall : ∀ᶠ n in atTop, T * ((r n : ℝ) / n) ≤ ε / 2 :=
    (hTr.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))).mono (fun _ h => h.le)
  have hBound : ∀ᶠ n in atTop,
      (μ n).real {ω | EmpiricalBottomLogTailEvent (s n ω) (r n) ε} ≤
        (μ n).real {ω | EmpiricalNegativeLogTailEvent (s n ω) T (ε / 2)} := by
    filter_upwards [hSmall] with n hn
    apply measureReal_mono (h₂ := by finiteness)
    intro ω hω
    rcases hω with ⟨j, _, hj⟩ | hω
    · exact Or.inl ⟨j, hj⟩
    · right
      have h := empirical_bottom_negative_log_bound (s n ω) (r n) hT.le
      change ε < empiricalBottomNegativeLog (s n ω) (r n) at hω
      linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTailT
    (Eventually.of_forall (fun _ => measureReal_nonneg)) hBound

end CircularLaw
