import CircularLaw.EmpiricalWeakConvergence

/-!
# Positive logarithms converge from weak convergence and tight second moments

The positive truncation error is bounded by the actual second moment
divided by the truncation level. Tightness makes this error small in
probability; weak convergence controls the bounded continuous truncation.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

theorem empirical_positive_log_convergence {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : Integrable (fun t : ℝ≥0 => Real.log (t : ℝ)) ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2))) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) hermitizationPositiveLog)
      (∫ t, hermitizationPositiveLog t ∂ν) := by
  apply varying_probability_of_error_bound μ
  intro ε hε δ hδ
  obtain ⟨M, hM, hTight⟩ := hMoment (δ / 2) (by linarith)
  have hClose : ∀ᶠ T : ℕ in atTop,
      |(∫ t, clippedPositiveLog T t ∂ν) - ∫ t, hermitizationPositiveLog t ∂ν| < ε / 3 := by
    have h := (clippedPositiveLog_integral_tendsto hLog).eventually
      (Metric.ball_mem_nhds _ (by linarith : 0 < ε / 3))
    simpa only [Metric.mem_ball, Real.dist_eq] using h
  have hBig : ∀ᶠ T : ℕ in atTop, 3 * M / ε < (T : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun T : ℕ => (T : ℝ)) atTop atTop).eventually
      (eventually_gt_atTop _)
  obtain ⟨T, hCloseT, hBigT, hTN⟩ := (hClose.and (hBig.and (eventually_ge_atTop 1))).exists
  have hT : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hScale : (1 / (T : ℝ)) * M ≤ ε / 3 := by
    have h := (div_lt_iff₀ hε).mp hBigT
    calc
      _ = M / (T : ℝ) := by ring
      _ ≤ ε / 3 := (div_le_iff₀ hT).mpr (by nlinarith)
  have hClip := (empirical_weak_clipped_positive hWeak hT.le) (ε / 3) (by linarith)
  have hClipSmall : ∀ᶠ n in atTop,
      (μ n).real {ω | ε / 3 < |empiricalNonnegativeMean (s n ω) (clippedPositiveLog T) -
        ∫ t, clippedPositiveLog T t ∂ν|} < δ / 2 :=
    hClip.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 2))
  filter_upwards [hTight, hClipSmall] with n hnMoment hnClip
  have hSubset :
      {ω | ε < |empiricalNonnegativeMean (s n ω) hermitizationPositiveLog -
        ∫ t, hermitizationPositiveLog t ∂ν|} ⊆
      {ω | M < |empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)|} ∪
      {ω | ε / 3 < |empiricalNonnegativeMean (s n ω) (clippedPositiveLog T) -
        ∫ t, clippedPositiveLog T t ∂ν|} := by
    intro ω hω
    change _ ∨ _
    by_contra h
    simp only [Set.mem_setOf_eq] at h
    push_neg at h
    have hMomentLe : empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2) ≤ M :=
      (le_abs_self _).trans h.1
    obtain ⟨hExcess0, hExcess⟩ := empirical_positive_log_excess_bounds (s n ω) hT
    have hError := hExcess.trans ((mul_le_mul_of_nonneg_left hMomentLe (by positivity)).trans hScale)
    have hAbs1 := abs_sub_le (empiricalNonnegativeMean (s n ω) hermitizationPositiveLog)
      (empiricalNonnegativeMean (s n ω) (clippedPositiveLog T)) (∫ t, hermitizationPositiveLog t ∂ν)
    rw [abs_of_nonneg hExcess0] at hAbs1
    have hAbs2 := abs_sub_le (empiricalNonnegativeMean (s n ω) (clippedPositiveLog T))
      (∫ t, clippedPositiveLog T t ∂ν) (∫ t, hermitizationPositiveLog t ∂ν)
    change ε < |empiricalNonnegativeMean (s n ω) hermitizationPositiveLog -
      ∫ t, hermitizationPositiveLog t ∂ν| at hω
    linarith
  have hP := (measureReal_mono (μ := μ n) hSubset).trans (measureReal_union_le _ _)
  exact hP.trans_lt (by linarith)

end CircularLaw
