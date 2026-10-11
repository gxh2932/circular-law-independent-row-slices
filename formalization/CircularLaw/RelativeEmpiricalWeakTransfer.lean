import CircularLaw.InterlacedEmpiricalWeakTransfer

/-!
# Weak convergence under a vanishing relative pointwise error

The reference arrays have a compact limiting law. A bounded continuous
cutoff controls their upper-tail fraction, and uniform continuity on a
larger compact interval handles relative errors on the remaining values.
No samplewise bound on the largest value is required.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem bounded_continuous_relative_mean_error_coefficient
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (M R : ℝ) (hM : ∀ t, |f t| ≤ M)
    (hR : 0 ≤ R) {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {n : ℕ}, 0 < n → ∀ (a b : Fin n → ℝ≥0) (delta : ℝ),
      0 ≤ delta → delta ≤ 1 → (∀ i, |(a i : ℝ) - b i| ≤ delta * (1 + b i)) →
      |empiricalNonnegativeMean a f - empiricalNonnegativeMean b f| ≤
        epsilon + K * delta + 2 * |M| *
          finiteMean (fun i => if R + 1 ≤ (b i : ℝ) then (1 : ℝ) else 0) := by
  let S : ℝ≥0 := ⟨2 * (R + 1) + 1, by linarith⟩
  obtain ⟨C, hC, hCompare⟩ := continuous_clipped_mean_error_coefficient f hf M hM S hEpsilon
  let K := C * (1 + (R + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro n hn a b delta hDelta hDeltaOne hError
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hPoint (i : Fin n) : |f (a i) - f (b i)| ≤
      epsilon + K * delta + (2 * |M|) * (if R + 1 ≤ (b i : ℝ) then 1 else 0) := by
    by_cases hTail : R + 1 ≤ (b i : ℝ)
    · rw [if_pos hTail, mul_one]
      have hT := abs_sub_le (f (a i)) 0 (f (b i))
      simp only [sub_zero, zero_sub, abs_neg] at hT
      have ha := (hM (a i)).trans (le_abs_self M)
      have hb := (hM (b i)).trans (le_abs_self M)
      nlinarith [mul_nonneg hK hDelta]
    · rw [if_neg hTail, mul_zero, add_zero]
      have hbSmall : (b i : ℝ) < R + 1 := lt_of_not_ge hTail
      have hAB := (abs_le.mp (hError i)).2
      have haR : (a i : ℝ) ≤ S := by
        have hBNonneg := (b i).coe_nonneg
        change (a i : ℝ) ≤ 2 * (R + 1) + 1
        nlinarith
      have hbR : (b i : ℝ) ≤ S := by dsimp [S]; linarith
      have haS : a i ≤ S := by exact_mod_cast haR
      have hbS : b i ≤ S := by exact_mod_cast hbR
      have h := hCompare (by norm_num : 0 < 1) (fun _ : Fin 1 => a i) (fun _ : Fin 1 => b i)
      simp only [finiteMean_const, min_eq_left haS, min_eq_left hbS,
        min_eq_left haR, min_eq_left hbR] at h
      have hBound := mul_le_mul_of_nonneg_left (hError i) hC
      have hMon := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (show 1 + (b i : ℝ) ≤ 1 + (R + 1) by linarith) hDelta) hC
      have hEq : C * (delta * (1 + (R + 1))) = K * delta := by dsimp [K]; ring
      rw [hEq] at hMon
      linarith
  change |finiteMean (fun i => f (a i)) - finiteMean (fun i => f (b i))| ≤ _
  rw [← finiteMean_sub]
  apply (abs_finiteMean_le _).trans
  calc
    _ ≤ finiteMean (fun i => epsilon + K * delta + (2 * |M|) *
        (if R + 1 ≤ (b i : ℝ) then 1 else 0)) := finiteMean_mono hPoint
    _ = _ := by rw [finiteMean_add, finiteMean_const, finiteMean_const_mul]

theorem empirical_weak_convergence_of_relative_pointwise_error {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (q : ℕ → ℕ) (hQ : Tendsto q atTop atTop)
    (a b : ∀ n, Ω n → Fin (q n) → ℝ≥0) (ν : Measure ℝ≥0)
    (R : ℝ) (hR : 0 ≤ R) (hSupport : ν {t : ℝ≥0 | R < (t : ℝ)} = 0)
    (delta : ℕ → ℝ) (hDeltaNonneg : ∀ n, 0 ≤ delta n)
    (hDelta : Tendsto delta atTop (𝓝 0))
    (hError : ∀ᶠ n in atTop, ∀ x i, |(a n x i : ℝ) - b n x i| ≤ delta n * (1 + b n x i))
    (hWeak : EmpiricalWeakConvergenceInProbability μ b ν) :
    EmpiricalWeakConvergenceInProbability μ a ν := by
  intro f hf hBound epsilon hEpsilon
  obtain ⟨M, hM⟩ := hBound
  obtain ⟨K, hK, hCompare⟩ := bounded_continuous_relative_mean_error_coefficient
    f hf M R hM hR (by positivity : 0 < epsilon / 4)
  have hCut : VaryingConvergesInProbability μ
      (fun n x => empiricalNonnegativeMean (b n x) (upperSupportCutoff R)) 0 := by
    have h := hWeak (upperSupportCutoff R) (continuous_upper_support_cutoff R)
      ⟨1, fun t => by
        rw [abs_of_nonneg (upper_support_cutoff_bounds R t).1]
        exact (upper_support_cutoff_bounds R t).2⟩
    rwa [upper_support_cutoff_integral_zero_of_support R ν hSupport] at h
  have hTest := hWeak f hf ⟨M, hM⟩
  let D := 2 * |M| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let eta := epsilon / (4 * D)
  have hEta : 0 < eta := div_pos hEpsilon (by positivity)
  have hDEta : D * eta = epsilon / 4 := by dsimp [eta]; field_simp
  have hSmall : 2 * |M| * eta ≤ epsilon / 4 := by
    have h := mul_le_mul_of_nonneg_right (show 2 * |M| ≤ D by dsimp [D]; linarith) hEta.le
    rwa [hDEta] at h
  have hDet : Tendsto (fun n => K * delta n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hDelta.const_mul K
  have hSum := (hCut eta hEta).add (hTest (epsilon / 4) (by positivity))
  simp only [add_zero] at hSum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hQ.eventually_gt_atTop 0, hError,
    hDelta.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hDet.eventually (gt_mem_nhds (by positivity : 0 < epsilon / 4))] with n hn he hd hKd
  apply (measureReal_mono (μ := μ n) (s₂ :=
    {x | eta < |empiricalNonnegativeMean (b n x) (upperSupportCutoff R) - 0|} ∪
      {x | epsilon / 4 < |empiricalNonnegativeMean (b n x) f - ∫ t, f t ∂ν|}) ?_
    (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  intro x hx
  by_contra h
  have hNot := not_or.mp h
  have hCutLe : |empiricalNonnegativeMean (b n x) (upperSupportCutoff R) - 0| ≤ eta :=
    le_of_not_gt hNot.1
  have hTail : finiteMean (fun i => if R + 1 ≤ (b n x i : ℝ) then (1 : ℝ) else 0) ≤ eta := by
    apply (finite_upper_tail_fraction_le_cutoff (b n x) R).trans
    exact (le_abs_self _).trans (by simpa only [sub_zero] using hCutLe)
  have hTailProduct := (mul_le_mul_of_nonneg_left hTail (by positivity : 0 ≤ 2 * |M|)).trans hSmall
  have hCompareNow := hCompare hn (a n x) (b n x) (delta n) (hDeltaNonneg n) hd.le (he x)
  have hTestLe : |empiricalNonnegativeMean (b n x) f - ∫ t, f t ∂ν| ≤ epsilon / 4 :=
    le_of_not_gt hNot.2
  have hTriangle := abs_sub_le (empiricalNonnegativeMean (a n x) f)
    (empiricalNonnegativeMean (b n x) f) (∫ t, f t ∂ν)
  change epsilon < |empiricalNonnegativeMean (a n x) f - ∫ t, f t ∂ν| at hx
  linarith

end CircularLaw
