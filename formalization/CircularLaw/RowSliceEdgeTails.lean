import CircularLaw.RowSliceEdgeCounts

/-!
# Poisson and logarithmic tails for actual edge counts

Optimizing the exact edge-count exponential moment gives the usual
Poisson upper tail. Beyond `exp(2)` times the mean, it bounds the
logarithmic discrepancy event. A minimum over the finite bad sample
set supplies its threshold without assuming an analytic inverse.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem rowSliceEdge_upper_laplace_tail {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) {tilt : ℝ} (htilt : 0 ≤ tilt) (t : ℝ) :
    uniformProbability (fun rows : Fin m → RowSlice n d => t ≤ rowSliceEdgeCount S T rows) ≤
      Real.exp (rowSliceEdgeMean d S T * (Real.exp tilt - 1) - tilt * t) := by
  let f := fun rows : Fin m → RowSlice n d => Real.exp (tilt * rowSliceEdgeCount S T rows)
  have hMark := finite_uniform_markov (fun rows : Fin m → RowSlice n d => t ≤ rowSliceEdgeCount S T rows)
    f (a := Real.exp (tilt * t)) (Real.exp_pos _) (fun _ => Real.exp_nonneg _)
    (fun _ hEvent => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hEvent htilt))
  apply hMark.trans
  apply (div_le_div_of_nonneg_right (rowSliceEdge_laplace hn hd S T tilt)
    (Real.exp_nonneg (tilt * t))).trans_eq
  rw [← Real.exp_sub]

theorem rowSliceEdge_poisson_upper_tail {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) (hMean : 0 < rowSliceEdgeMean d S T)
    {t : ℝ} (ht : rowSliceEdgeMean d S T ≤ t) :
    uniformProbability (fun rows : Fin m → RowSlice n d => t ≤ rowSliceEdgeCount S T rows) ≤
      Real.exp (t - rowSliceEdgeMean d S T - t * Real.log (t / rowSliceEdgeMean d S T)) := by
  have htPos : 0 < t := hMean.trans_le ht
  have hRatio : 1 ≤ t / rowSliceEdgeMean d S T := (one_le_div hMean).mpr ht
  have hTilt : 0 ≤ Real.log (t / rowSliceEdgeMean d S T) := Real.log_nonneg hRatio
  have h := rowSliceEdge_upper_laplace_tail hn hd S T hTilt t
  rw [Real.exp_log (div_pos htPos hMean)] at h
  apply h.trans_eq
  congr 1
  field_simp

theorem rowSliceEdge_large_deviation_upper_tail {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) (hMean : 0 < rowSliceEdgeMean d S T)
    {t : ℝ} (ht : Real.exp 2 * rowSliceEdgeMean d S T ≤ t) :
    uniformProbability (fun rows : Fin m → RowSlice n d => t ≤ rowSliceEdgeCount S T rows) ≤
      Real.exp (-(t / 2) * Real.log (t / rowSliceEdgeMean d S T)) := by
  have hExp : 1 ≤ Real.exp (2 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hScaled := mul_le_mul_of_nonneg_right hExp hMean.le
  have hMeanLe : rowSliceEdgeMean d S T ≤ t := by linarith only [hScaled, ht]
  have htPos := hMean.trans_le hMeanLe
  have hRatio := (le_div_iff₀ hMean).mpr ht
  have hLog := Real.log_le_log (Real.exp_pos (2 : ℝ)) hRatio
  rw [Real.log_exp] at hLog
  have hLogScaled := mul_le_mul_of_nonneg_left hLog htPos.le
  apply (rowSliceEdge_poisson_upper_tail hn hd S T hMean hMeanLe).trans
  apply Real.exp_le_exp.mpr
  nlinarith only [hLogScaled, hMean.le]

theorem finite_logarithmic_bad_event_bound {α : Type*} [Fintype α]
    (X : α → ℝ) (event : α → Prop) (mu c : ℝ)
    (hEvent : ∀ x, event x → Real.exp 2 * mu ≤ X x ∧ c < X x * Real.log (X x / mu))
    (hTail : ∀ t : ℝ, Real.exp 2 * mu ≤ t →
      uniformProbability (fun x : α => t ≤ X x) ≤ Real.exp (-(t / 2) * Real.log (t / mu))) :
    uniformProbability event ≤ Real.exp (-c / 2) := by
  by_cases hExists : ∃ x, event x
  · let A := (Finset.univ : Finset α).filter event
    have hA : A.Nonempty := by
      obtain ⟨x, hx⟩ := hExists
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    obtain ⟨x, hx, hMin⟩ := Finset.exists_min_image A X hA
    have hxEvent := (Finset.mem_filter.mp hx).2
    have hData := hEvent x hxEvent
    have hCover : ∀ y : α, event y → X x ≤ X y := fun y hy =>
      hMin y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
    apply (uniformProbability_mono hCover).trans
    apply (hTail (X x) hData.1).trans
    apply Real.exp_le_exp.mpr
    linarith only [hData.2]
  · have hFalse (x : α) : ¬event x := fun hx => hExists ⟨x, hx⟩
    have hZero : uniformProbability event = 0 := by
      rw [← finiteMean_indicator]
      have hPoint : (fun x : α => if event x then (1 : ℝ) else 0) = fun _ => 0 := by
        funext x
        rw [if_neg (hFalse x)]
      rw [hPoint]
      simp only [finiteMean, Finset.sum_const_zero, zero_div]
    rw [hZero]
    exact Real.exp_nonneg _

theorem rowSliceEdge_logarithmic_bad_event {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) (hMean : 0 < rowSliceEdgeMean d S T) (c : ℝ) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      Real.exp 2 * rowSliceEdgeMean d S T < rowSliceEdgeCount S T rows ∧
        c < rowSliceEdgeCount S T rows * Real.log (rowSliceEdgeCount S T rows / rowSliceEdgeMean d S T)) ≤
          Real.exp (-c / 2) := by
  apply finite_logarithmic_bad_event_bound (rowSliceEdgeCount S T) _ (rowSliceEdgeMean d S T) c
  · intro rows hEvent
    exact ⟨hEvent.1.le, hEvent.2⟩
  · intro t ht
    exact rowSliceEdge_large_deviation_upper_tail hn hd S T hMean ht

end CircularLaw
