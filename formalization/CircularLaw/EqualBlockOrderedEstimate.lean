import CircularLaw.EqualBlockConstants

/-!
# Equal-block estimates from the ordered-vector hypothesis

The top/tail blocks are constructed from the actual decreasing-norm
permutation. The uniform witness event implies the selected-block event.
The two estimates use the exact floor scale and common absolute norm and
rate constants determined by the fixed witness constant.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def UniformEqualBlockWitness {n d : ℕ} {ι : Type*} [Fintype ι]
    (cw : ℝ) (s : ℕ) (rows : ι → RowSlice n d) : Prop :=
  ∀ L R : Finset (Fin n), Disjoint L R → L.card = s → R.card = s →
    cw * (d : ℝ) * s ≤ (blockWitnessRows (L ∪ R) rows).card

theorem equal_block_ordered_small {n d m1 m2 : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hdn : d ≤ n)
    (hm1 : 0 < m1) (hm12 : m1 ≤ m2) (hmTail : m2 + m1 ≤ n)
    (y : Fin n → ℂ) {cw : ℝ} (hcw : 0 < cw)
    (hGap : ∀ j : Fin n, m2 ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm y j < orderedNorm y ⟨m1 - 1, by omega⟩)
    (c ζ : ℂ) (index : ι → Fin n) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      shiftedRowsL2Norm rows y c ζ index ≤
        equalBlockNormConstant cw * Real.sqrt ((d : ℝ) * m1) ∧
      UniformEqualBlockWitness cw m1 rows) ≤
      Real.exp (-equalBlockRateConstant cw * (d : ℝ) * m1) := by
  let σ := normOrderPerm y
  have hTop : 1 * m1 ≤ n := by omega
  have hTail : m2 + 1 * m1 ≤ n := by omega
  let L := orderedRankBlock σ 0 (by simpa only [zero_add] using hTop)
  let R := orderedRankBlock σ m2 hTail
  have hDis := orderedRankBlock_union_pairwise σ m2 hTop hTail (by omega)
  have hHalves := orderedRankBlock_top_tail_disjoint σ m2 hTop hTail (by omega)
  have hSize : ∀ q : Fin 1, (L q).card = (R q).card := by
    intro q
    rw [orderedRankBlock_card, orderedRankBlock_card]
  have hLeft : ∀ q : Fin 1, (L q).Nonempty :=
    fun q => orderedRankBlock_nonempty σ 0 _ hm1 q
  have hSep : ∀ q l, l ∈ L q → ∀ j, j ∈ R q → (2 : ℝ) * (1 / 3) < dist (y l) (y j) := by
    intro q l hl j hj
    exact norm_ordered_blocks_separated y m2 ⟨m1 - 1, by omega⟩ hTop hTail
      (by change 1 * m1 ≤ m1 - 1 + 1; omega)
      (by simpa only [show (2 : ℝ) * (1 / 3) = 2 / 3 by ring] using hGap) q l hl j hj
  have hBound := equal_blocks_one_witness_euclidean_half hdn L R hDis
    (fun q => hHalves q q) hSize hLeft y (by norm_num : (0 : ℝ) < 1 / 3)
    (by positivity : 0 ≤ cw * ((d : ℝ) * m1)) hSep c ζ index (0 : Fin 1)
  apply (uniformProbability_mono ?_).trans (hBound.trans ?_)
  · intro rows hEvent
    refine ⟨hEvent.1.trans (equal_block_small_radius hcw (by positivity)), ?_⟩
    have h := hEvent.2 (L 0) (R 0) (hHalves 0 0)
      (orderedRankBlock_card σ 0 _ 0) (orderedRankBlock_card σ m2 hTail 0)
    simpa only [mul_assoc] using h
  · apply Real.exp_le_exp.mpr
    have hRate : equalBlockRateConstant cw ≤ witnessHalfRate * cw := min_le_left _ _
    have h := mul_le_mul_of_nonneg_right hRate (by positivity : 0 ≤ (d : ℝ) * m1)
    nlinarith

theorem equal_block_ordered_large {n d m1 m2 : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hd : 0 < d) (hn : 400 * d ≤ n)
    (hDimension : Fintype.card ι ≤ n)
    (hm1 : 0 < m1) (hm12 : m1 ≤ m2) (hmTail : m2 + m1 ≤ n)
    (y : Fin n → ℂ) {cw : ℝ} (hcw : 0 < cw)
    (hmLarge : equalBlockLargeConstant cw * equalBlockScale n d ≤ (m1 : ℝ))
    (hGap : ∀ j : Fin n, m2 ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm y j < orderedNorm y ⟨m1 - 1, by omega⟩)
    (c ζ : ℂ) (index : ι → Fin n) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      shiftedRowsL2Norm rows y c ζ index ≤
        equalBlockNormConstant cw * Real.sqrt ((d : ℝ) * equalBlockScale n d) ∧
      UniformEqualBlockWitness cw (equalBlockScale n d) rows) ≤
      Real.exp (-equalBlockRateConstant cw * (d : ℝ) * equalBlockScale n d *
        Real.log ((d : ℝ) * m1 / n)) := by
  let s := equalBlockScale n d
  let q := m1 / s
  let σ := normOrderPerm y
  let x := (d : ℝ) * m1 / n
  let B := cw * ((d : ℝ) * s)
  let a := B / (4 * (n : ℝ)) * q
  let p := equalBlockCoefficient cw / Real.sqrt x
  have hs : 0 < s := equalBlockScale_pos hd hn
  have hC := equalBlockLargeConstant_ge_one cw
  have hsm : s ≤ m1 := by
    have hS : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have h := mul_le_mul_of_nonneg_right hC hS
    have hsmReal : (s : ℝ) ≤ m1 := by linarith
    exact_mod_cast hsmReal
  have hq : 0 < q := Nat.div_pos hsm hs
  have hFit : q * s ≤ m1 := Nat.div_mul_le_self _ _
  have hTop : q * s ≤ n := by omega
  have hTail : m2 + q * s ≤ n := by omega
  have hTopTail : q * s ≤ m2 := by omega
  let L := orderedRankBlock σ 0 (by simpa only [zero_add] using hTop)
  let R := orderedRankBlock σ m2 hTail
  have hDis := orderedRankBlock_union_pairwise σ m2 hTop hTail hTopTail
  have hHalves := orderedRankBlock_top_tail_disjoint σ m2 hTop hTail hTopTail
  have hSize : ∀ b : Fin q, (L b).card = (R b).card := by
    intro b
    rw [orderedRankBlock_card, orderedRankBlock_card]
  have hLeft : ∀ b : Fin q, (L b).Nonempty := fun b => orderedRankBlock_nonempty σ 0 _ hs b
  have hSep : ∀ b l, l ∈ L b → ∀ j, j ∈ R b → (2 : ℝ) * (1 / 3) < dist (y l) (y j) := by
    intro b l hl j hj
    exact norm_ordered_blocks_separated y m2 ⟨m1 - 1, by omega⟩ hTop hTail
      (by change q * s ≤ m1 - 1 + 1; omega)
      (by simpa only [show (2 : ℝ) * (1 / 3) = 2 / 3 by ring] using hGap) b l hl j hj
  have hx : equalBlockRatioThreshold cw ≤ x := by
    have h := equalBlockScale_ratio_lower hd hn (by linarith : 0 ≤ equalBlockLargeConstant cw) hmLarge
    have hConstant : equalBlockLargeConstant cw / 400 = equalBlockRatioThreshold cw := by
      unfold equalBlockLargeConstant
      ring
    rw [hConstant] at h
    exact h
  have haLower : cw / 8 * x ≤ a := by
    have hHalf := quotient_product_ge_half hs hsm
    have hMul := mul_le_mul_of_nonneg_left hHalf
      (by positivity : 0 ≤ cw * (d : ℝ) / (4 * (n : ℝ)))
    convert hMul using 1 <;> dsimp only [a, B, x, q] <;> ring
  obtain ⟨ha, hp, hpHalf, hEsseen, hLog⟩ := equal_block_large_probability_parameters hcw hx haLower
  have hBound := equal_blocks_many_witnesses_euclidean_log (by omega : d ≤ n)
    (by omega : 0 < n) (by simpa only [Fintype.card_fin] using hq) hDimension
    L R hDis (fun b => hHalves b b) hSize hLeft y (by norm_num : (0 : ℝ) < 1 / 3)
    (by positivity : 0 ≤ B) hp hpHalf
    (by simpa only [Fintype.card_fin] using ha) hSep
    (by simpa only [Fintype.card_fin] using hEsseen) c ζ index
  apply (uniformProbability_mono ?_).trans (hBound.trans ?_)
  · intro rows hEvent
    refine ⟨hEvent.1.trans (equal_block_large_radius hcw (by positivity)), ?_⟩
    intro b
    have h := hEvent.2 (L b) (R b) (hHalves b b)
      (orderedRankBlock_card σ 0 _ b) (orderedRankBlock_card σ m2 hTail b)
    simpa only [B, s, mul_assoc] using h
  · apply Real.exp_le_exp.mpr
    have hLogX : 0 ≤ Real.log x := by
      apply Real.log_nonneg
      have hD := equalBlockCoefficient_ge_two cw
      have hPower : (2 : ℝ) ^ 4 ≤ equalBlockCoefficient cw ^ 4 :=
        pow_le_pow_left₀ (by norm_num) hD 4
      have h := (le_max_right (8 / cw) (equalBlockCoefficient cw ^ 4)).trans hx
      nlinarith
    have hRate : equalBlockRateConstant cw ≤ 3 * witnessLogRate * cw / 16 := min_le_right _ _
    have hRateMul := mul_le_mul_of_nonneg_right hRate
      (mul_nonneg (by positivity : 0 ≤ (d : ℝ) * s) hLogX)
    have hCoefficient : 0 ≤ witnessLogRate * ((3 / 4 : ℝ) * B) :=
      mul_nonneg witnessLogRate_pos.le (by positivity)
    have hLogMul := mul_le_mul_of_nonneg_left hLog hCoefficient
    have hCombined := hRateMul.trans (by convert hLogMul using 1; dsimp only [B]; ring)
    dsimp only [s, x, p, B] at hCombined ⊢
    nlinarith

end CircularLaw
