import CircularLaw.VaryingProbabilityConvergence

/-!
# A probability squeeze with varying sample spaces and explicit bad events

The squeeze includes any singular samples in its failure event. Thus it
proves both the finite probability limit and the disappearance of that
event, rather than silently replacing extended logarithms at zero.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem varying_probability_neg {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    {f : ∀ n, Ω n → ℝ} {a : ℝ} (hf : VaryingConvergesInProbability μ f a) :
    VaryingConvergesInProbability μ (fun n ω => -f n ω) (-a) := by
  intro epsilon hEpsilon
  simpa only [neg_sub_neg, abs_sub_comm] using hf epsilon hEpsilon

theorem varying_probability_mul_deterministic {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {f : ∀ n, Ω n → ℝ} {a b : ℝ}
    {c : ℕ → ℝ} (hf : VaryingConvergesInProbability μ f a)
    (hc : Tendsto c atTop (𝓝 b)) :
    VaryingConvergesInProbability μ (fun n ω => c n * f n ω) (b * a) := by
  intro epsilon hEpsilon
  let M := |b| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hThreshold : 0 < epsilon / (2 * M) := div_pos hEpsilon (by positivity)
  have hCoeff : ∀ᶠ n in atTop, |c n| ≤ M :=
    (hc.abs.eventually (gt_mem_nhds (by dsimp [M]; linarith))).mono (fun _ h => h.le)
  have hBias : Tendsto (fun n => |c n * a - b * a|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using ((hc.mul_const a).sub_const (b * a)).abs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hf (epsilon / (2 * M)) hThreshold)
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hCoeff, hBias.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < epsilon / 2))]
    with n hn hb
  refine measureReal_mono (μ := μ n) (fun ω hω => ?_) (by finiteness)
  change epsilon / (2 * M) < |f n ω - a|
  by_contra h
  have hError : |c n * (f n ω - a)| ≤ epsilon / 2 := by
    rw [abs_mul]
    calc
      _ ≤ M * (epsilon / (2 * M)) := mul_le_mul hn (le_of_not_gt h)
        (abs_nonneg _) hM.le
      _ = epsilon / 2 := by field_simp
  have hTriangle := abs_sub_le (c n * f n ω) (c n * a) (b * a)
  have hEq : c n * f n ω - c n * a = c n * (f n ω - a) := by ring
  rw [hEq] at hTriangle
  change epsilon < |c n * f n ω - b * a| at hω
  linarith

theorem varying_probability_of_agreement_outside_bad_event {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsFiniteMeasure (μ n)] {f g : ∀ n, Ω n → ℝ} {a : ℝ}
    (bad : ∀ n, Set (Ω n)) (hf : VaryingConvergesInProbability μ f a)
    (hBad : Tendsto (fun n => (μ n).real (bad n)) atTop (𝓝 0))
    (hAgree : ∀ᶠ n in atTop, ∀ ω, ω ∉ bad n → g n ω = f n ω) :
    VaryingConvergesInProbability μ g a := by
  intro epsilon hEpsilon
  have hSum := hBad.add (hf epsilon hEpsilon)
  simp only [add_zero] at hSum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hAgree] with n hn
  have hSubset : {ω | epsilon < |g n ω - a|} ⊆
      bad n ∪ {ω | epsilon < |f n ω - a|} := by
    intro ω hω
    by_cases hBadSample : ω ∈ bad n
    · exact Or.inl hBadSample
    · apply Or.inr
      change epsilon < |f n ω - a|
      rw [← hn ω hBadSample]
      exact hω
  exact (measureReal_mono (μ := μ n) hSubset (by finiteness)).trans (measureReal_union_le _ _)

theorem varying_probability_of_asymptotic_squeeze {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (f lower upper : ∀ n, Ω n → ℝ) (bad : ∀ n, Set (Ω n)) (a : ℝ)
    (hLower : VaryingConvergesInProbability μ lower a)
    (hUpper : VaryingConvergesInProbability μ upper a)
    (hSqueeze : ∀ delta : ℝ, 0 < delta → Tendsto (fun n => (μ n).real
      {ω | ω ∈ bad n ∨ f n ω < lower n ω - delta ∨ upper n ω + delta < f n ω})
      atTop (𝓝 0)) :
    VaryingConvergesInProbability μ f a ∧
      Tendsto (fun n => (μ n).real (bad n)) atTop (𝓝 0) := by
  constructor
  · intro epsilon hEpsilon
    have hDelta : 0 < epsilon / 2 := by linarith
    have hSum := ((hSqueeze (epsilon / 2) hDelta).add
      (hLower (epsilon / 2) hDelta)).add (hUpper (epsilon / 2) hDelta)
    simp only [add_zero] at hSum
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
      (Eventually.of_forall (fun _ => measureReal_nonneg))
    apply Eventually.of_forall
    intro n
    let E := {ω | ω ∈ bad n ∨ f n ω < lower n ω - epsilon / 2 ∨
      upper n ω + epsilon / 2 < f n ω}
    let L := {ω | epsilon / 2 < |lower n ω - a|}
    let U := {ω | epsilon / 2 < |upper n ω - a|}
    have hSubset : {ω | epsilon < |f n ω - a|} ⊆ (E ∪ L) ∪ U := by
      intro ω hω
      by_contra h
      have hNot : ω ∉ E ∧ ω ∉ L ∧ ω ∉ U := by
        simpa only [Set.mem_union, not_or, and_assoc] using h
      have hBounds : ¬(ω ∈ bad n) ∧ lower n ω - epsilon / 2 ≤ f n ω ∧
          f n ω ≤ upper n ω + epsilon / 2 := by
        simpa only [E, Set.mem_setOf_eq, not_or, not_lt] using hNot.1
      have hL : |lower n ω - a| ≤ epsilon / 2 := le_of_not_gt hNot.2.1
      have hU : |upper n ω - a| ≤ epsilon / 2 := le_of_not_gt hNot.2.2
      have hAbs : |f n ω - a| ≤ epsilon := abs_le.mpr ⟨by
        have hLeft := (abs_le.mp hL).1
        linarith [hBounds.2.1], by
        have hRight := (abs_le.mp hU).2
        linarith [hBounds.2.2]⟩
      exact (not_lt.mpr hAbs) hω
    exact (measureReal_mono (μ := μ n) hSubset).trans
      ((measureReal_union_le (E ∪ L) U).trans
        (add_le_add (measureReal_union_le E L) le_rfl))
  · exact varying_probability_event_of_subset μ (fun _ _ h => Or.inl h)
      (hSqueeze 1 zero_lt_one)

end CircularLaw
