import CircularLaw.RowSliceEdgeTails

/-!
# Multiplicative lower tails for actual fixed-degree edge counts

The already checked exponential moments hold at negative tilts. Markov's
inequality and a quadratic exponential bound give the full Chernoff
lower tail, without an independence assumption on coordinates in a row.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem real_exp_neg_le_quadratic {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  have hExp := Real.quadratic_le_exp_of_nonneg ht
  have hMinus : 0 ≤ 1 - t + t ^ 2 / 2 := by nlinarith [sq_nonneg (t - 1)]
  have hProduct : (1 - t + t ^ 2 / 2) * (1 + t + t ^ 2 / 2) =
      1 + (t ^ 2) ^ 2 / 4 := by ring
  rw [Real.exp_neg, ← one_div]
  apply (div_le_iff₀ (Real.exp_pos t)).mpr
  calc
    (1 : ℝ) ≤ (1 - t + t ^ 2 / 2) * (1 + t + t ^ 2 / 2) := by
      rw [hProduct]
      nlinarith [sq_nonneg (t ^ 2)]
    _ ≤ (1 - t + t ^ 2 / 2) * Real.exp t := mul_le_mul_of_nonneg_left hExp hMinus

theorem rowSliceEdge_lower_laplace_tail {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) {tilt : ℝ} (htilt : 0 ≤ tilt) (t : ℝ) :
    uniformProbability (fun rows : Fin m → RowSlice n d => rowSliceEdgeCount S T rows ≤ t) ≤
      Real.exp (rowSliceEdgeMean d S T * (Real.exp (-tilt) - 1) + tilt * t) := by
  let f := fun rows : Fin m → RowSlice n d => Real.exp (-tilt * rowSliceEdgeCount S T rows)
  have hMark := finite_uniform_markov
    (fun rows : Fin m → RowSlice n d => rowSliceEdgeCount S T rows ≤ t)
    f (a := Real.exp (-tilt * t)) (Real.exp_pos _) (fun _ => Real.exp_nonneg _)
    (fun _ hEvent => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hEvent (by linarith)))
  apply hMark.trans
  apply (div_le_div_of_nonneg_right (rowSliceEdge_laplace hn hd S T (-tilt))
    (Real.exp_nonneg (-tilt * t))).trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

theorem rowSliceEdge_chernoff_lower_tail {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) {θ : ℝ} (hθ : 0 ≤ θ) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      rowSliceEdgeCount S T rows ≤ (1 - θ) * rowSliceEdgeMean d S T) ≤
        Real.exp (-rowSliceEdgeMean d S T * θ ^ 2 / 2) := by
  have hMean : 0 ≤ rowSliceEdgeMean d S T := by unfold rowSliceEdgeMean; positivity
  apply (rowSliceEdge_lower_laplace_tail hn hd S T hθ _).trans
  apply Real.exp_le_exp.mpr
  have hTaylor := mul_le_mul_of_nonneg_left (real_exp_neg_le_quadratic hθ) hMean
  nlinarith only [hTaylor]

end CircularLaw
