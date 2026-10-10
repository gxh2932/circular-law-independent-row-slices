import CircularLaw.SteepNetUnion

/-!
# Equal-block small balls for every actual steep-net member

The filtered gap and zero tail supply the literal ordered hypothesis of
the checked equal-block lemma. Both fixed-vector estimates use the full
matrix sample space and exact restriction to the retained rows.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem steepNonconstantNet_ordered_gap {n d rank next : ℕ} {cap : ℝ}
    (hRank : 0 < rank) (hRankNext : rank ≤ next) (hFit : next + rank ≤ n)
    (u : Fin n → ℂ) (hu : u ∈ steepNonconstantNet n d rank next cap) :
    ∀ j : Fin n, next ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm u j < orderedNorm u ⟨rank - 1, by omega⟩ := by
  have h := steepNonconstantNet_gap_and_tail u hu
  rw [orderedNormAt_eq u hRank (by omega : rank ≤ n)] at h
  intro j hj
  have hTailZero : orderedNorm u j = 0 := by
    have hOrder : (⟨next - 1, by omega⟩ : Fin n) ≤ j :=
      Fin.le_iff_val_le_val.mpr (by change next - 1 ≤ j.val; omega)
    have hNorm := orderedNorm_antitone u hOrder
    rw [← orderedNormAt_eq u (by omega : 0 < next) (by omega : next ≤ n), h.2] at hNorm
    exact le_antisymm hNorm (orderedNorm_nonneg u j)
  simpa only [hTailZero, add_zero] using h.1

theorem steep_net_fixed_vector_small {n d rank next : ℕ} {cap cw R : ℝ}
    (hdn : d ≤ n) (hRank : 0 < rank) (hRankNext : rank ≤ next) (hFit : next + rank ≤ n)
    (hcw : 0 < cw) (I : Finset (Fin n)) (u : Fin n → ℂ)
    (hu : u ∈ steepNonconstantNet n d rank next cap) (w ζ : ℂ)
    (hRadius : R ≤ equalBlockNormConstant cw * Real.sqrt ((d : ℝ) * rank)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      shiftedRowsL2Norm (fun i : I => rows i.val) u w ζ (fun i => i.val) ≤ R ∧
        UniformEqualBlockWitness cw rank (fun i : I => rows i.val)) ≤
      Real.exp (-equalBlockRateConstant cw * (d : ℝ) * rank) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  rw [uniformProbability_pi_restrict (α := fun _ : Fin n => RowSlice n d) I
    (fun rows : I → RowSlice n d => shiftedRowsL2Norm rows u w ζ (fun i => i.val) ≤ R ∧
      UniformEqualBlockWitness cw rank rows)]
  apply (uniformProbability_mono ?_).trans
    (equal_block_ordered_small hdn hRank hRankNext hFit u hcw
      (steepNonconstantNet_ordered_gap hRank hRankNext hFit u hu) w ζ (fun i : I => i.val))
  intro rows hEvent
  exact ⟨hEvent.1.trans hRadius, hEvent.2⟩

theorem steep_net_fixed_vector_large {n d rank next : ℕ} {cap cw R : ℝ}
    (hd : 0 < d) (hn : 400 * d ≤ n) (hRank : 0 < rank)
    (hRankNext : rank ≤ next) (hFit : next + rank ≤ n) (hcw : 0 < cw)
    (hLarge : equalBlockLargeConstant cw * equalBlockScale n d ≤ (rank : ℝ))
    (I : Finset (Fin n)) (u : Fin n → ℂ)
    (hu : u ∈ steepNonconstantNet n d rank next cap) (w ζ : ℂ)
    (hRadius : R ≤ equalBlockNormConstant cw * Real.sqrt ((d : ℝ) * equalBlockScale n d)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      shiftedRowsL2Norm (fun i : I => rows i.val) u w ζ (fun i => i.val) ≤ R ∧
        UniformEqualBlockWitness cw (equalBlockScale n d) (fun i : I => rows i.val)) ≤
      Real.exp (-equalBlockRateConstant cw * (d : ℝ) * equalBlockScale n d *
        Real.log ((d : ℝ) * rank / n)) := by
  have hdn : d ≤ n := by omega
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  rw [uniformProbability_pi_restrict (α := fun _ : Fin n => RowSlice n d) I
    (fun rows : I → RowSlice n d => shiftedRowsL2Norm rows u w ζ (fun i => i.val) ≤ R ∧
      UniformEqualBlockWitness cw (equalBlockScale n d) rows)]
  apply (uniformProbability_mono ?_).trans
    (equal_block_ordered_large hd hn
      (by simpa only [Fintype.card_coe, Fintype.card_fin] using Finset.card_le_univ I)
      hRank hRankNext hFit u hcw hLarge
      (steepNonconstantNet_ordered_gap hRank hRankNext hFit u hu) w ζ (fun i : I => i.val))
  intro rows hEvent
  exact ⟨hEvent.1.trans hRadius, hEvent.2⟩

theorem source_shifted_T1_kernel_finite_probability {n d L : ℕ} {cw Z₀ : ℝ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (hdn : d ≤ n) (hZ : 0 ≤ Z₀) (hcw : 0 < cw)
    (hRanks : firstSteepScale n d ≤ secondSteepScale n d)
    (hFit : secondSteepScale n d + firstSteepScale n d ≤ n)
    (hRadius : 2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) ≤
      equalBlockNormConstant cw * Real.sqrt ((d : ℝ) * firstSteepScale n d))
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ v ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ¬UniformEqualBlockWitness cw (firstSteepScale n d) (fun i : I => rows i.val)) +
            ((sourceT1Net n d).card : ℝ) * (steepConstantNet d 1).card *
              Real.exp (-equalBlockRateConstant cw * (d : ℝ) * firstSteepScale n d) := by
  have hData := source_kernel_first_scale_data h hL
  apply source_shifted_T1_kernel_finite_net_bound h hL hCubic hZ I ζ hShift
  intro u hu w _
  exact steep_net_fixed_vector_small hdn (by omega : 0 < firstSteepScale n d)
    hRanks hFit hcw I u hu w ζ hRadius

theorem source_shifted_T2_kernel_finite_probability {n d L : ℕ} {a₃ cw Z₀ : ℝ}
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hSize : 2 ≤ a₃ * (n : ℝ))
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (hn : 400 * d ≤ n) (hZ : 0 ≤ Z₀) (hcw : 0 < cw)
    (hRanks : secondSteepScale n d ≤ thirdSteepScale n a₃)
    (hFit : thirdSteepScale n a₃ + secondSteepScale n d ≤ n)
    (hLarge : equalBlockLargeConstant cw * equalBlockScale n d ≤ (secondSteepScale n d : ℝ))
    (hRadius : 2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) ≤
      equalBlockNormConstant cw * Real.sqrt ((d : ℝ) * equalBlockScale n d))
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ v ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ¬UniformEqualBlockWitness cw (equalBlockScale n d) (fun i : I => rows i.val)) +
            ((sourceT2Net n d a₃).card : ℝ) *
              (steepConstantNet d (Real.rpow (d : ℝ) (3 / 2))).card *
                Real.exp (-equalBlockRateConstant cw * (d : ℝ) * equalBlockScale n d *
                  Real.log ((d : ℝ) * secondSteepScale n d / n)) := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hSecond := secondSteepScale_valid hd h.dimension_root
  apply source_shifted_T2_kernel_finite_net_bound ha haOne hSize h hL hCubic hZ I ζ hShift
  intro u hu w _
  exact steep_net_fixed_vector_large hd hn hSecond.1 hRanks hFit hcw hLarge I u hu w ζ hRadius

end CircularLaw
