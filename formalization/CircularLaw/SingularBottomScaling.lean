import CircularLaw.RectangularSingularScaling
import CircularLaw.BernoulliBottomLogTailTheorem

/-!
# Bottom negative logarithms under scalar enlargement

Scaling by a scalar of norm at least one can only decrease the real
negative-log bottom sum, including singular matrices. The actual raw
shifted Bernoulli comparator is sqrt(d) times its normalized comparator.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem negative_log_scalar_enlargement_le {c s : ℝ} (hc : 1 ≤ c) (hs : 0 ≤ s) :
    max (-Real.log (c * s)) 0 ≤ max (-Real.log s) 0 := by
  by_cases hsZero : s = 0
  · simp [hsZero]
  · have hsPos : 0 < s := lt_of_le_of_ne hs (Ne.symm hsZero)
    have hScale : s ≤ c * s := by nlinarith [mul_nonneg (show 0 ≤ c - 1 by linarith) hs]
    exact max_le_max (neg_le_neg (Real.log_le_log hsPos hScale)) le_rfl

theorem square_bottom_negative_log_smul_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (hc : 1 ≤ ‖c‖) (r : ℕ) :
    empiricalBottomNegativeLog (squareSingularValuesNNReal (c • A)) r ≤
      empiricalBottomNegativeLog (squareSingularValuesNNReal A) r := by
  unfold empiricalBottomNegativeLog
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro j _
  change max (-Real.log (orderedSquareSingularValues (c • A) j)) 0 ≤
    max (-Real.log (orderedSquareSingularValues A j)) 0
  rw [ordered_square_singular_smul]
  exact negative_log_scalar_enlargement_le hc (orderedSquareSingularValues_nonneg A j)

theorem bernoulli_raw_shift_eq_sqrt_smul {n d : ℕ} (hd : 0 < d) (z : ℂ)
    (x : BernoulliSquareSample n) :
    bernoulliSquareMatrix x - (z * (Real.sqrt (d : ℝ) : ℂ)) • 1 =
      (Real.sqrt (d : ℝ) : ℂ) • normalizedShiftedBernoulliMatrix d z x := by
  have hc : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < d by exact_mod_cast hd)).ne'
  symm
  simp only [normalizedShiftedBernoulliMatrix, smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [mul_comm]

theorem bernoulli_raw_bottom_negative_log_le {n d : ℕ} (hd : 0 < d) (z : ℂ)
    (x : BernoulliSquareSample n) (r : ℕ) :
    empiricalBottomNegativeLog
      (squareSingularValuesNNReal (bernoulliSquareMatrix x - (z * (Real.sqrt (d : ℝ) : ℂ)) • 1)) r ≤
    empiricalBottomNegativeLog (squareSingularValuesNNReal (normalizedShiftedBernoulliMatrix d z x)) r := by
  rw [bernoulli_raw_shift_eq_sqrt_smul hd]
  apply square_bottom_negative_log_smul_le
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    (1 : ℝ) = Real.sqrt 1 := by norm_num
    _ ≤ Real.sqrt d := Real.sqrt_le_sqrt (by exact_mod_cast hd)

theorem bernoulli_raw_bottom_negative_log_converges (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ) (hz : z ≠ 0)
    (r : ℕ → ℕ) (hr : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => empiricalBottomNegativeLog
        (squareSingularValuesNNReal (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1)) (r n)) 0 := by
  intro ε hε
  have hTail := bernoulli_bottom_log_tail_theorem d hDegree hSparse z hz r hr ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTail
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  have hn : 0 < n := lt_of_lt_of_le hd.1 hd.2
  apply measureReal_mono (h₂ := by finiteness)
  intro x hx
  change ENNReal.ofReal ε < empiricalExtendedBottomNegativeLog (bernoulliSingularArray d z n x) (r n)
  rw [empiricalExtendedBottomNegativeLog_event hn _ _ hε]
  apply Or.inr
  have hNonneg : 0 ≤ empiricalBottomNegativeLog
      (squareSingularValuesNNReal (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1)) (r n) := by
    unfold empiricalBottomNegativeLog
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => le_max_right _ _)) (Nat.cast_nonneg n)
  simp only [Set.mem_setOf_eq, sub_zero, abs_of_nonneg hNonneg] at hx
  exact hx.trans_le (bernoulli_raw_bottom_negative_log_le hd.1 z x (r n))

end CircularLaw
