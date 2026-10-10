import CircularLaw.WideBarrierExposureCompletion
import CircularLaw.ExposureGoodEventCoupling

/-!
# Good-event coupling at the wider insertion barrier

Killing the height on failure of nested currently measurable good events
preserves the wide-barrier conditional drift. The terminal failure is
at most the good-event failure plus 16*q^(1/8). Both errors may vanish
on varying probability spaces.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem wide_barrier_good_event_completion_bound
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m0) (H : ℕ → Ω → ℕ) (G : ℕ → Set Ω) (T : ℕ)
    (hMeas : ∀ s, s ≤ T → Measurable[F s] (H s))
    (hGoodMeas : ∀ s, s ≤ T → MeasurableSet[F s] (G s))
    (hNested : ∀ s, s < T → G (s + 1) ⊆ G s)
    (hInitial : ∀ x, (H 0 x : ℝ) ≤ (T : ℝ) / 2)
    (hGrowth : ∀ s, s < T → ∀ x, H (s + 1) x ≤ H s x + 2)
    {q : ℝ} (hq : 0 ≤ q)
    (hDrift : ∀ s, s < T → ∀ᵐ x ∂μ,
      x ∈ G s → 2 * ((T - s) / 8) ≤ H s x →
      (μ[({y | H s y - 1 < H (s + 1) y}).indicator (fun _ => (1 : ℝ)) | F s]) x ≤ q) :
    μ.real {x | 0 < H T x} ≤ μ.real (G T)ᶜ + 16 * q ^ (1 / 8 : ℝ) := by
  let K := killedExposureHeight G H
  have hKMeas : ∀ s, s ≤ T → Measurable[F s] (K s) := by
    intro s hs
    exact Measurable.ite (hGoodMeas s hs) (hMeas s hs) measurable_const
  have hKInitial : ∀ x, (K 0 x : ℝ) ≤ (T : ℝ) / 2 := by
    intro x
    by_cases hx : x ∈ G 0
    · simpa only [K, killedExposureHeight, if_pos hx] using hInitial x
    · simp only [K, killedExposureHeight, if_neg hx, Nat.cast_zero]
      positivity
  have hKGrowth : ∀ s, s < T → ∀ x, K (s + 1) x ≤ K s x + 2 := by
    intro s hs x
    by_cases hx : x ∈ G (s + 1)
    · have hxOld := hNested s hs hx
      simpa only [K, killedExposureHeight, if_pos hx, if_pos hxOld] using hGrowth s hs x
    · simp only [K, killedExposureHeight, if_neg hx]
      omega
  have hKDrift : ∀ s, s < T → ∀ᵐ x ∂μ,
      2 * ((T - s) / 8) ≤ K s x →
      (μ[({y | K s y - 1 < K (s + 1) y}).indicator (fun _ => (1 : ℝ)) | F s]) x ≤ q := by
    intro s hs
    let B := {x | H s x - 1 < H (s + 1) x}
    let C := {x | K s x - 1 < K (s + 1) x}
    have hB : MeasurableSet B := measurableSet_lt
      ((Measurable.of_discrete : Measurable (fun n : ℕ => n - 1)).comp
        ((hMeas s (by omega)).mono (F.le s) le_rfl))
      ((hMeas (s + 1) (by omega)).mono (F.le (s + 1)) le_rfl)
    have hC : MeasurableSet C := measurableSet_lt
      ((Measurable.of_discrete : Measurable (fun n : ℕ => n - 1)).comp
        ((hKMeas s (by omega)).mono (F.le s) le_rfl))
      ((hKMeas (s + 1) (by omega)).mono (F.le (s + 1)) le_rfl)
    have hSubset : C ⊆ G s ∩ B := by
      intro x hx
      have hxNew : x ∈ G (s + 1) := by
        by_contra hn
        simp only [C, Set.mem_setOf_eq, K, killedExposureHeight, if_neg hn] at hx
        omega
      have hxOld := hNested s hs hxNew
      refine ⟨hxOld, ?_⟩
      simpa only [C, B, Set.mem_setOf_eq, K, killedExposureHeight, if_pos hxNew, if_pos hxOld] using hx
    have hConditional := conditional_indicator_le_past_times_bad μ (F s) (F.le s)
      (hGoodMeas s (by omega)) hB hC hSubset
    filter_upwards [hConditional, hDrift s hs] with x hx hd hActive
    by_cases hxGood : x ∈ G s
    · simp only [Set.indicator_of_mem hxGood, one_mul] at hx
      apply hx.trans
      apply hd hxGood
      simpa only [K, killedExposureHeight, if_pos hxGood] using hActive
    · simp only [Set.indicator_of_notMem hxGood, zero_mul] at hx
      exact hx.trans hq
  have hCompleted := wide_barrier_exposure_terminal_probability_bound μ F K T hKMeas
    hKInitial hKGrowth hq hKDrift
  have hSubset : {x | 0 < H T x} ⊆ {x | 0 < K T x} ∪ (G T)ᶜ := by
    intro x hx
    by_cases hxGood : x ∈ G T
    · exact Or.inl (by simpa only [Set.mem_setOf_eq, K, killedExposureHeight, if_pos hxGood] using hx)
    · exact Or.inr hxGood
  have hBound := (measureReal_mono (μ := μ) hSubset).trans (measureReal_union_le _ _)
  linarith


theorem varying_wide_barrier_completion_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (F : ∀ n, Filtration ℕ (inferInstance : MeasurableSpace (Ω n)))
    (H : ∀ n, ℕ → Ω n → ℕ) (G : ∀ n, ℕ → Set (Ω n)) (T : ℕ → ℕ)
    (hMeas : ∀ n s, s ≤ T n → Measurable[F n s] (H n s))
    (hGoodMeas : ∀ n s, s ≤ T n → MeasurableSet[F n s] (G n s))
    (hNested : ∀ n s, s < T n → G n (s + 1) ⊆ G n s)
    (hInitial : ∀ n x, (H n 0 x : ℝ) ≤ (T n : ℝ) / 2)
    (hGrowth : ∀ n s, s < T n → ∀ x, H n (s + 1) x ≤ H n s x + 2)
    (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (hDrift : ∀ n s, s < T n → ∀ᵐ x ∂μ n,
      x ∈ G n s → 2 * ((T n - s) / 8) ≤ H n s x →
      ((μ n)[({y | H n s y - 1 < H n (s + 1) y}).indicator (fun _ => (1 : ℝ)) | F n s]) x ≤ q n)
    (hQ : Tendsto q atTop (𝓝 0))
    (hGood : Tendsto (fun n => (μ n).real (G n (T n))ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).real {x | 0 < H n (T n) x}) atTop (𝓝 0) := by
  have hPower : Tendsto (fun n => 16 * q n ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1 / 8 : ℝ) ≠ 0), mul_zero] using
      (hQ.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 8))).const_mul 16
  have hSum : Tendsto (fun n => (μ n).real (G n (T n))ᶜ + 16 * q n ^ (1 / 8 : ℝ))
      atTop (𝓝 0) := by simpa only [add_zero] using hGood.add hPower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  exact Eventually.of_forall (fun n => wide_barrier_good_event_completion_bound
    (μ n) (F n) (H n) (G n) (T n) (hMeas n) (hGoodMeas n) (hNested n)
    (hInitial n) (hGrowth n) (hq n) (hDrift n))

end CircularLaw
