import CircularLaw.ExposureProcessCompletion

/-!
# Killing the exposure height when a required graph condition fails

Good events are measurable in the currently exposed sigma-algebra and
nested in time. Killing the process at their first failure preserves the
local drift bound through conditional expectation. The terminal error is
the sum of the final good-event failure and the drift completion error.
This is the coupling step in SSS25's proof of Lemma 8.1.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem conditional_indicator_le_past_times_bad
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0) {A B C : Set Ω}
    (hA : MeasurableSet[m] A) (hB : @MeasurableSet Ω m0 B)
    (hC : @MeasurableSet Ω m0 C) (hSubset : C ⊆ A ∩ B) :
    ∀ᵐ x ∂μ, (μ[C.indicator (fun _ => (1 : ℝ)) | m]) x ≤
      A.indicator (fun _ => (1 : ℝ)) x * (μ[B.indicator (fun _ => (1 : ℝ)) | m]) x := by
  let a := A.indicator (fun _ => (1 : ℝ))
  let b := B.indicator (fun _ => (1 : ℝ))
  let c := C.indicator (fun _ => (1 : ℝ))
  have hBInt : Integrable b μ := (integrable_const 1).indicator hB
  have hCInt : Integrable c μ := (integrable_const 1).indicator hC
  have hProduct : a * b = A.indicator b := by
    ext x
    by_cases hx : x ∈ A <;> simp [a, hx]
  have hProductInt : Integrable (a * b) μ := hProduct ▸ hBInt.indicator (hm _ hA)
  have hMono : c ≤ᵐ[μ] a * b := by
    apply ae_of_all
    intro x
    by_cases hxc : x ∈ C
    · obtain ⟨hxa, hxb⟩ := hSubset hxc
      simp [a, b, c, hxa, hxb, hxc]
    · by_cases hxa : x ∈ A <;> by_cases hxb : x ∈ B <;> simp [a, b, c, hxa, hxb, hxc]
  have hCompare := condExp_mono (m := m) hCInt hProductInt hMono
  have hPull := condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_const.indicator hA) hProductInt hBInt
  filter_upwards [hCompare, hPull] with x hx hp
  exact hx.trans_eq hp

def killedExposureHeight {Ω : Type*} (G : ℕ → Set Ω) (H : ℕ → Ω → ℕ) :
    ℕ → Ω → ℕ := fun s x => if x ∈ G s then H s x else 0

theorem exposure_process_good_event_completion_bound
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m0) (H : ℕ → Ω → ℕ) (G : ℕ → Set Ω) (T : ℕ)
    (hMeas : ∀ s, s ≤ T → Measurable[F s] (H s))
    (hGoodMeas : ∀ s, s ≤ T → MeasurableSet[F s] (G s))
    (hNested : ∀ s, s < T → G (s + 1) ⊆ G s)
    (hInitial : ∀ x, (H 0 x : ℝ) ≤ (T : ℝ) / 4)
    (hGrowth : ∀ s, s < T → ∀ x, H (s + 1) x ≤ H s x + 2)
    {q : ℝ} (hq : 0 ≤ q)
    (hDrift : ∀ s, s < T → ∀ᵐ x ∂μ,
      x ∈ G s → 2 * ((T - s) / 16) ≤ H s x →
      (μ[({y | H s y - 1 < H (s + 1) y}).indicator (fun _ => (1 : ℝ)) | F s]) x ≤ q) :
    μ.real {x | 0 < H T x} ≤ μ.real (G T)ᶜ + 4 * q ^ (1 / 8 : ℝ) := by
  let K := killedExposureHeight G H
  have hKMeas : ∀ s, s ≤ T → Measurable[F s] (K s) := by
    intro s hs
    exact Measurable.ite (hGoodMeas s hs) (hMeas s hs) measurable_const
  have hKInitial : ∀ x, (K 0 x : ℝ) ≤ (T : ℝ) / 4 := by
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
      2 * ((T - s) / 16) ≤ K s x →
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
  have hCompleted := exposure_process_terminal_height_probability_bound μ F K T hKMeas
    hKInitial hKGrowth hq hKDrift
  have hSubset : {x | 0 < H T x} ⊆ {x | 0 < K T x} ∪ (G T)ᶜ := by
    intro x hx
    by_cases hxGood : x ∈ G T
    · exact Or.inl (by simpa only [Set.mem_setOf_eq, K, killedExposureHeight, if_pos hxGood] using hx)
    · exact Or.inr hxGood
  have hBound := (measureReal_mono (μ := μ) hSubset).trans (measureReal_union_le _ _)
  linarith


theorem varying_exposure_process_completion_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (F : ∀ n, Filtration ℕ (inferInstance : MeasurableSpace (Ω n)))
    (H : ∀ n, ℕ → Ω n → ℕ) (G : ∀ n, ℕ → Set (Ω n)) (T : ℕ → ℕ)
    (hMeas : ∀ n s, s ≤ T n → Measurable[F n s] (H n s))
    (hGoodMeas : ∀ n s, s ≤ T n → MeasurableSet[F n s] (G n s))
    (hNested : ∀ n s, s < T n → G n (s + 1) ⊆ G n s)
    (hInitial : ∀ n x, (H n 0 x : ℝ) ≤ (T n : ℝ) / 4)
    (hGrowth : ∀ n s, s < T n → ∀ x, H n (s + 1) x ≤ H n s x + 2)
    (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (hDrift : ∀ n s, s < T n → ∀ᵐ x ∂μ n,
      x ∈ G n s → 2 * ((T n - s) / 16) ≤ H n s x →
      ((μ n)[({y | H n s y - 1 < H n (s + 1) y}).indicator (fun _ => (1 : ℝ)) | F n s]) x ≤ q n)
    (hQ : Tendsto q atTop (𝓝 0))
    (hGood : Tendsto (fun n => (μ n).real (G n (T n))ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).real {x | 0 < H n (T n) x}) atTop (𝓝 0) := by
  have hPower : Tendsto (fun n => 4 * q n ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1 / 8 : ℝ) ≠ 0), mul_zero] using
      (hQ.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 8))).const_mul 4
  have hSum : Tendsto (fun n => (μ n).real (G n (T n))ᶜ + 4 * q n ^ (1 / 8 : ℝ))
      atTop (𝓝 0) := by simpa only [add_zero] using hGood.add hPower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  exact Eventually.of_forall (fun n => exposure_process_good_event_completion_bound
    (μ n) (F n) (H n) (G n) (T n) (hMeas n) (hGoodMeas n) (hNested n)
    (hInitial n) (hGrowth n) (hq n) (hDrift n))

end CircularLaw
