import CircularLaw.BernoulliSubsetCountLaplace
import CircularLaw.FiniteProductEventUpperTail

/-!
# Poisson and logarithmic discrepancy tails for actual Bernoulli counts

The optimized product-law moment gives a logarithmic tail. A minimum
over the finite bad event converts it to the discrepancy threshold.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal

namespace CircularLaw

theorem bernoulli_subset_count_poisson_upper_tail {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) (hMean : 0 < (S.card : ℝ) * p)
    {t : ℝ} (ht : (S.card : ℝ) * p ≤ t) :
    (bernoulliCubeLaw ι p hp).real {x | t ≤ bernoulliSubsetCount S x} ≤
      Real.exp (t - (S.card : ℝ) * p - t * Real.log (t / ((S.card : ℝ) * p))) := by
  have htPos : 0 < t := hMean.trans_le ht
  have hRatio : 1 ≤ t / ((S.card : ℝ) * p) := (one_le_div hMean).mpr ht
  have hTilt : 0 ≤ Real.log (t / ((S.card : ℝ) * p)) := Real.log_nonneg hRatio
  have h := bernoulli_subset_count_upper_tail p hp S hTilt t
  rw [Real.exp_log (div_pos htPos hMean)] at h
  apply h.trans_eq
  congr 1
  rw [mul_sub, mul_div_cancel₀ t hMean.ne', mul_one]
  ring

theorem bernoulli_subset_count_large_deviation_upper_tail {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) (hMean : 0 < (S.card : ℝ) * p)
    {t : ℝ} (ht : Real.exp 2 * ((S.card : ℝ) * p) ≤ t) :
    (bernoulliCubeLaw ι p hp).real {x | t ≤ bernoulliSubsetCount S x} ≤
      Real.exp (-(t / 2) * Real.log (t / ((S.card : ℝ) * p))) := by
  have hExp : 1 ≤ Real.exp (2 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hScaled := mul_le_mul_of_nonneg_right hExp hMean.le
  have hMeanLe : (S.card : ℝ) * p ≤ t := by linarith only [hScaled, ht]
  have htPos := hMean.trans_le hMeanLe
  have hRatio := (le_div_iff₀ hMean).mpr ht
  have hLog := Real.log_le_log (Real.exp_pos (2 : ℝ)) hRatio
  rw [Real.log_exp] at hLog
  have hLogScaled := mul_le_mul_of_nonneg_left hLog htPos.le
  apply (bernoulli_subset_count_poisson_upper_tail p hp S hMean hMeanLe).trans
  apply Real.exp_le_exp.mpr
  nlinarith only [hLogScaled, hMean.le]

theorem finite_measure_logarithmic_bad_event_bound {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (E : Ω → Prop) (m c : ℝ)
    (hEvent : ∀ x, E x → Real.exp 2 * m ≤ X x ∧ c < X x * Real.log (X x / m))
    (hTail : ∀ t : ℝ, Real.exp 2 * m ≤ t →
      μ.real {x | t ≤ X x} ≤ Real.exp (-(t / 2) * Real.log (t / m))) :
    μ.real {x | E x} ≤ Real.exp (-c / 2) := by
  by_cases hExists : ∃ x, E x
  · let A := (Finset.univ : Finset Ω).filter E
    have hA : A.Nonempty := by
      obtain ⟨x, hx⟩ := hExists
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    obtain ⟨x, hx, hMin⟩ := Finset.exists_min_image A X hA
    have hxEvent := (Finset.mem_filter.mp hx).2
    have hData := hEvent x hxEvent
    have hCover : {y | E y} ⊆ {y | X x ≤ X y} := fun y hy =>
      hMin y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
    apply (measureReal_mono hCover (h₂ := by finiteness)).trans
    apply (hTail (X x) hData.1).trans
    apply Real.exp_le_exp.mpr
    linarith only [hData.2]
  · have hEmpty : {x | E x} = ∅ := by
      exact Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hExists ⟨x, hx⟩)
    rw [hEmpty, measureReal_empty]
    exact Real.exp_nonneg _

theorem bernoulli_subset_count_logarithmic_bad_event {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) (hMean : 0 < (S.card : ℝ) * p) (c : ℝ) :
    (bernoulliCubeLaw ι p hp).real {x |
      Real.exp 2 * ((S.card : ℝ) * p) < bernoulliSubsetCount S x ∧
        c < bernoulliSubsetCount S x * Real.log (bernoulliSubsetCount S x / ((S.card : ℝ) * p))} ≤
          Real.exp (-c / 2) := by
  apply finite_measure_logarithmic_bad_event_bound (bernoulliCubeLaw ι p hp)
    (bernoulliSubsetCount S) _ ((S.card : ℝ) * p) c
  · intro x hx
    exact ⟨hx.1.le, hx.2⟩
  · intro t ht
    exact bernoulli_subset_count_large_deviation_upper_tail p hp S hMean ht

end CircularLaw
