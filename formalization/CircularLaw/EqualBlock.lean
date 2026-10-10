import CircularLaw.EqualBlockOrderedEstimate
import CircularLaw.DegreeRates

/-!
# The manuscript's full equal-block lemma

The target includes both regimes, the literal ordered-coordinate gap,
the exact floor `m0`, the uniform witness event and the shifted Euclidean
row action. Probabilities use the full matrix sample space, with the
retained rows obtained by exact finite marginalization. The surrounding
polylogarithmic degree range discharges the finite floor-scale conditions
for all sufficiently large dimensions.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def retainedShiftedMatrix {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) : Matrix I (Fin n) ℂ :=
  fun i j => rowEntry (rows i.val) j - ζ * (if i.val = j then 1 else 0)

theorem retainedShiftedMatrix_mulVec {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (v : Fin n → ℂ) (i : I) :
    (retainedShiftedMatrix I ζ rows).mulVec v i =
      rowLinearForm (rows i.val) v - ζ * v i.val := by
  change (∑ j, (rowEntry (rows i.val) j - ζ * (if i.val = j then 1 else 0)) * v j) =
    (∑ j, rowEntry (rows i.val) j * v j) - ζ * v i.val
  simp only [sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp

theorem shiftedRowsL2Norm_eq_matrix_action {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (y : Fin n → ℂ) (w : ℂ) :
    shiftedRowsL2Norm (fun i : I => rows i.val) y w ζ (fun i => i.val) =
      ‖(WithLp.toLp 2 ((retainedShiftedMatrix I ζ rows).mulVec (fun j => y j + w)) :
        EuclideanSpace ℂ I)‖ := by
  have hAction : (retainedShiftedMatrix I ζ rows).mulVec (fun j => y j + w) =
      fun i : I => shiftedRowAction (rows i.val) y w ζ i.val := by
    funext i
    exact retainedShiftedMatrix_mulVec I ζ rows (fun j => y j + w) i
  rw [hAction]
  rfl

def equalBlockCommonConstant (cw : ℝ) : ℝ :=
  min (equalBlockNormConstant cw) (equalBlockRateConstant cw)

theorem equalBlockCommonConstant_pos {cw : ℝ} (hcw : 0 < cw) :
    0 < equalBlockCommonConstant cw :=
  lt_min (equalBlockNormConstant_pos hcw) (equalBlockRateConstant_pos hcw)

theorem eventually_equal_block_dimension (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      ∀ d : ℕ, (d : ℝ) ≤ Real.rpow (Real.log n) a → 400 * d ≤ n := by
  have hSmall : ∀ᶠ n : ℕ in atTop,
      Real.rpow (Real.log n) a / n < 1 / 400 :=
    (log_power_div_self_tendsto_zero a).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 400))
  filter_upwards [hSmall, eventually_ge_atTop 2] with n hSmall hn
  refine ⟨hn, ?_⟩
  intro d hd
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hDiv : (d : ℝ) / n < 1 / 400 :=
    (div_le_div_of_nonneg_right hd hnPos.le).trans_lt hSmall
  have h := (div_lt_iff₀ hnPos).mp hDiv
  have hScaled : (400 : ℝ) * d ≤ n := by linarith
  exact_mod_cast hScaled

/-- Full-paper equal-block target. Rank `m1-1` is `u*_{m1}` and the
tail condition `m2 <= j.val` is the manuscript's one-based `j > m2`.
The constants are absolute once the positive witness constant is fixed.
Positive degrees and the polylogarithmic upper bound spell out the
surrounding Section 4 degree context; its logarithmic lower bound is
not needed for this stronger small-ball estimate. -/
def EqualBlockSmallBallLemma : Prop :=
  ∀ cw : ℝ, 0 < cw → ∃ Ceb c : ℝ, 1 ≤ Ceb ∧ 0 < c ∧
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.rpow (Real.log n) (1 + σ) →
      ∀ I : Finset (Fin n), ∀ m1 m2 : ℕ,
        ∀ hm1 : 0 < m1, ∀ hm12 : m1 ≤ m2, ∀ hmTail : m2 ≤ n - m1,
        ∀ y : Fin n → ℂ,
        (∀ j : Fin n, m2 ≤ j.val →
          (2 / 3 : ℝ) + orderedNorm y j < orderedNorm y ⟨m1 - 1, by omega⟩) →
        ∀ w ζ : ℂ,
        (m1 ≤ equalBlockScale n d →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            shiftedRowsL2Norm (fun i : I => rows i.val) y w ζ (fun i => i.val) ≤
              c * Real.sqrt ((d : ℝ) * m1) ∧
            UniformEqualBlockWitness cw m1 (fun i : I => rows i.val)) ≤
              Real.exp (-c * (d : ℝ) * m1)) ∧
        (Ceb * equalBlockScale n d ≤ (m1 : ℝ) →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            shiftedRowsL2Norm (fun i : I => rows i.val) y w ζ (fun i => i.val) ≤
              c * Real.sqrt ((d : ℝ) * equalBlockScale n d) ∧
            UniformEqualBlockWitness cw (equalBlockScale n d) (fun i : I => rows i.val)) ≤
              Real.exp (-c * (d : ℝ) * equalBlockScale n d * Real.log ((d : ℝ) * m1 / n)))

theorem equal_block_small_ball_lemma : EqualBlockSmallBallLemma := by
  intro cw hcw
  refine ⟨equalBlockLargeConstant cw, equalBlockCommonConstant cw,
    equalBlockLargeConstant_ge_one cw, equalBlockCommonConstant_pos hcw, ?_⟩
  intro σ _ _
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_equal_block_dimension (1 + σ))
  refine ⟨N, ?_⟩
  intro n hn d hd hUpper I m1 m2 hm1 hm12 hmTail y hGap w ζ
  have hFit : m2 + m1 ≤ n := by omega
  have hnScale := (hN n hn).2 d hUpper
  have hdn : d ≤ n := by omega
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  have hNorm : equalBlockCommonConstant cw ≤ equalBlockNormConstant cw := min_le_left _ _
  have hRate : equalBlockCommonConstant cw ≤ equalBlockRateConstant cw := min_le_right _ _
  constructor
  · intro _
    rw [uniformProbability_pi_restrict (α := fun _ : Fin n => RowSlice n d) I
      (fun rows : I → RowSlice n d =>
      shiftedRowsL2Norm rows y w ζ (fun i => i.val) ≤
        equalBlockCommonConstant cw * Real.sqrt ((d : ℝ) * m1) ∧
      UniformEqualBlockWitness cw m1 rows)]
    apply (uniformProbability_mono ?_).trans
      ((equal_block_ordered_small hdn hm1 hm12 hFit y hcw hGap w ζ (fun i : I => i.val)).trans ?_)
    · intro rows hEvent
      exact ⟨hEvent.1.trans (mul_le_mul_of_nonneg_right hNorm (Real.sqrt_nonneg _)), hEvent.2⟩
    · apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hRate (by positivity : 0 ≤ (d : ℝ) * m1)
      nlinarith
  · intro hLarge
    rw [uniformProbability_pi_restrict (α := fun _ : Fin n => RowSlice n d) I
      (fun rows : I → RowSlice n d =>
      shiftedRowsL2Norm rows y w ζ (fun i => i.val) ≤
        equalBlockCommonConstant cw * Real.sqrt ((d : ℝ) * equalBlockScale n d) ∧
      UniformEqualBlockWitness cw (equalBlockScale n d) rows)]
    apply (uniformProbability_mono ?_).trans
      ((equal_block_ordered_large (ι := I) hd hnScale
        (by simpa only [Fintype.card_coe, Fintype.card_fin] using Finset.card_le_univ I)
        hm1 hm12 hFit y hcw hLarge hGap w ζ (fun i : I => i.val)).trans ?_)
    · intro rows hEvent
      exact ⟨hEvent.1.trans (mul_le_mul_of_nonneg_right hNorm (Real.sqrt_nonneg _)), hEvent.2⟩
    · apply Real.exp_le_exp.mpr
      have hRatio := equalBlockScale_ratio_lower hd hnScale
        (by linarith [equalBlockLargeConstant_ge_one cw] : 0 ≤ equalBlockLargeConstant cw) hLarge
      have hC := equalBlockLargeConstant_ge_one cw
      have hD := equalBlockCoefficient_ge_two cw
      have hPow : (2 : ℝ) ^ 4 ≤ equalBlockCoefficient cw ^ 4 :=
        pow_le_pow_left₀ (by norm_num) hD 4
      have hR := le_max_right (8 / cw) (equalBlockCoefficient cw ^ 4)
      have hLog : 0 ≤ Real.log ((d : ℝ) * m1 / n) := by
        apply Real.log_nonneg
        unfold equalBlockLargeConstant equalBlockRatioThreshold at hRatio
        nlinarith
      have h := mul_le_mul_of_nonneg_right hRate
        (mul_nonneg (by positivity : 0 ≤ (d : ℝ) * equalBlockScale n d) hLog)
      nlinarith

end CircularLaw
