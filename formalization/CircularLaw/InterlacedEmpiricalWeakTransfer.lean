import CircularLaw.InterlacedContinuousMeanComparison
import CircularLaw.GaussianWeakLimitSupport

/-!
# Actual weak convergence transfers across one-index interlacing

A compact weak limit makes a continuous upper-tail cutoff converge to
zero. The deterministic clipped comparison bounds every bounded
continuous test error by a chosen tolerance, a dimension loss and that
same tail fraction. Both interlacings therefore transfer the actual
weak convergence, even if one array has an exceptional large top value.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem upper_support_cutoff_integral_zero_of_support (R : ℝ) (ν : Measure ℝ≥0)
    (hSupport : ν {t : ℝ≥0 | R < (t : ℝ)} = 0) :
    (∫ t, upperSupportCutoff R t ∂ν) = 0 := by
  have hAe : ∀ᵐ t : ℝ≥0 ∂ν, (t : ℝ) ≤ R := by
    rw [ae_iff]
    simpa only [not_le] using hSupport
  have hZero : (fun t => upperSupportCutoff R t) =ᵐ[ν] (fun _ => (0 : ℝ)) :=
    hAe.mono (fun _ h => upper_support_cutoff_zero h)
  rw [integral_congr_ae hZero, integral_zero]

theorem finite_upper_tail_fraction_le_cutoff {n : ℕ} (b : Fin n → ℝ≥0) (R : ℝ) :
    finiteMean (fun i => if R + 1 ≤ (b i : ℝ) then (1 : ℝ) else 0) ≤
      empiricalNonnegativeMean b (upperSupportCutoff R) := by
  apply finiteMean_mono
  intro i
  by_cases h : R + 1 ≤ (b i : ℝ)
  · rw [if_pos h, upperSupportCutoff, max_eq_right (by linarith), min_eq_left (by linarith)]
  · rw [if_neg h]
    exact (upper_support_cutoff_bounds R (b i)).1

theorem indexed_empirical_weak_convergence_of_one_index_interlacing {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (q : ℕ → ℕ) (hQ : Tendsto q atTop atTop)
    (a b : ∀ n, Ω n → Fin (q n) → ℝ≥0)
    (ν : Measure ℝ≥0) (R : ℝ) (hR : 0 ≤ R)
    (hSupport : ν {t : ℝ≥0 | R < (t : ℝ)} = 0)
    (ha : ∀ n x, Antitone (fun i => (a n x i : ℝ)))
    (hb : ∀ n x, Antitone (fun i => (b n x i : ℝ)))
    (hAB : ∀ n x (i j : Fin (q n)), j.val = i.val + 1 → (a n x j : ℝ) ≤ b n x i)
    (hBA : ∀ n x (i j : Fin (q n)), j.val = i.val + 1 → (b n x j : ℝ) ≤ a n x i)
    (hWeak : EmpiricalWeakConvergenceInProbability μ b ν) :
    EmpiricalWeakConvergenceInProbability μ a ν := by
  intro f hf hBound ε hε
  obtain ⟨M, hM⟩ := hBound
  let S : ℝ≥0 := ⟨R + 1, by linarith⟩
  obtain ⟨C, hC, hCompare⟩ := interlaced_bounded_continuous_mean_error_coefficient
    f hf M hM S (by positivity : 0 < ε / 4)
  have hCut : VaryingConvergesInProbability μ
      (fun n x => empiricalNonnegativeMean (b n x) (upperSupportCutoff R)) 0 := by
    have h := hWeak (upperSupportCutoff R) (continuous_upper_support_cutoff R)
      ⟨1, fun t => by
        rw [abs_of_nonneg (upper_support_cutoff_bounds R t).1]
        exact (upper_support_cutoff_bounds R t).2⟩
    rwa [upper_support_cutoff_integral_zero_of_support R ν hSupport] at h
  have hTest := hWeak f hf ⟨M, hM⟩
  let D := 4 * |M| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let δ := ε / (4 * D)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hDδ : D * δ = ε / 4 := by dsimp [δ]; field_simp
  have hSmall : 4 * |M| * δ ≤ ε / 4 := by
    have h := mul_le_mul_of_nonneg_right (show 4 * |M| ≤ D by dsimp [D]; linarith) hδ.le
    rwa [hDδ] at h
  have hDet : Tendsto (fun n : ℕ => C / (q n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hQ)).const_mul C
  have hSum := (hCut δ hδ).add (hTest (ε / 4) (by positivity))
  simp only [add_zero] at hSum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hQ.eventually_gt_atTop 0,
    hDet.eventually (gt_mem_nhds (by positivity : 0 < ε / 4))] with n hn hCn
  apply (measureReal_mono (μ := μ n) (s₂ :=
    {x | δ < |empiricalNonnegativeMean (b n x) (upperSupportCutoff R) - 0|} ∪
      {x | ε / 4 < |empiricalNonnegativeMean (b n x) f - ∫ t, f t ∂ν|}) ?_
    (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  intro x hx
  by_contra h
  have hNot := not_or.mp h
  have hCutLe : |empiricalNonnegativeMean (b n x) (upperSupportCutoff R) - 0| ≤ δ :=
    le_of_not_gt hNot.1
  have hTail : finiteMean (fun i => if R + 1 ≤ (b n x i : ℝ) then (1 : ℝ) else 0) ≤ δ := by
    apply (finite_upper_tail_fraction_le_cutoff (b n x) R).trans
    exact (le_abs_self _).trans (by simpa only [sub_zero] using hCutLe)
  have hTailProduct := (mul_le_mul_of_nonneg_left hTail (by positivity : 0 ≤ 4 * |M|)).trans hSmall
  have hError := hCompare hn (a n x) (b n x) (ha n x) (hb n x) (hAB n x) (hBA n x)
  change |empiricalNonnegativeMean (a n x) f - empiricalNonnegativeMean (b n x) f| ≤
    ε / 4 + C / q n + (4 * |M|) *
      finiteMean (fun i => if R + 1 ≤ (b n x i : ℝ) then (1 : ℝ) else 0) at hError
  have hTestLe : |empiricalNonnegativeMean (b n x) f - ∫ t, f t ∂ν| ≤ ε / 4 :=
    le_of_not_gt hNot.2
  have hT := abs_sub_le (empiricalNonnegativeMean (a n x) f)
    (empiricalNonnegativeMean (b n x) f) (∫ t, f t ∂ν)
  change ε < |empiricalNonnegativeMean (a n x) f - ∫ t, f t ∂ν| at hx
  linarith

theorem empirical_weak_convergence_of_one_index_interlacing {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (a b : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) (R : ℝ) (hR : 0 ≤ R)
    (hSupport : ν {t : ℝ≥0 | R < (t : ℝ)} = 0)
    (ha : ∀ n x, Antitone (fun i => (a n x i : ℝ)))
    (hb : ∀ n x, Antitone (fun i => (b n x i : ℝ)))
    (hAB : ∀ n x (i j : Fin n), j.val = i.val + 1 → (a n x j : ℝ) ≤ b n x i)
    (hBA : ∀ n x (i j : Fin n), j.val = i.val + 1 → (b n x j : ℝ) ≤ a n x i)
    (hWeak : EmpiricalWeakConvergenceInProbability μ b ν) :
    EmpiricalWeakConvergenceInProbability μ a ν :=
  indexed_empirical_weak_convergence_of_one_index_interlacing μ id tendsto_id a b ν R hR
    hSupport ha hb hAB hBA hWeak

end CircularLaw
