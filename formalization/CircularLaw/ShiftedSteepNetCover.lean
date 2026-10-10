import CircularLaw.SteepNetMatrixError

/-!
# Covering the literal normalized shifted `T1` and `T2` classes

Both components are approximated separately by actual finite grid
members. A kernel vector therefore produces a net point with the source
L2 action bound. The constant grid preserves the row-sum contribution
in the small-ball event.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem normalized_shifted_sourceT1_net_cover {n d L : ℕ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (x : Fin n → ℂ)
    (hx : x ∈ sourceT1 n d L) (hNorm : orderedNormAt x (firstSteepScale n d) = 1)
    (c : ℂ) (hc : ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10) :
    ∃ u ∈ sourceT1Net n d, ∃ w ∈ steepConstantNet d 1,
      (∀ j, ‖x j - u j‖ ≤ steepNetError d) ∧ ‖c - w‖ ≤ steepNetError d := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hCenter : ‖c‖ ≤ 1 := by rw [hNorm] at hc; linarith
  obtain ⟨u, hu, hError⟩ := normalized_sourceT1_net_approximation h hL hCubic x hx hNorm
  obtain ⟨w, hw, hCError⟩ := steep_constant_net_approximation hd c hCenter
  exact ⟨u, hu, w, hw, hError, hCError⟩

theorem normalized_shifted_sourceT2_net_cover {n d L : ℕ} {a₃ : ℝ}
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hSize : 2 ≤ a₃ * (n : ℝ))
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (x : Fin n → ℂ)
    (hx : x ∈ sourceT2 n d L a₃) (hNorm : orderedNormAt x (secondSteepScale n d) = 1)
    (c : ℂ) (hc : ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10) :
    ∃ u ∈ sourceT2Net n d a₃, ∃ w ∈ steepConstantNet d (Real.rpow (d : ℝ) (3 / 2)),
      (∀ j, ‖x j - u j‖ ≤ steepNetError d) ∧ ‖c - w‖ ≤ steepNetError d := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hFirst := (normalized_sourceT2_coordinate_ranges h hL hCubic x hx hNorm).1
  have hCenter : ‖c‖ ≤ Real.rpow (d : ℝ) (3 / 2) :=
    hc.trans ((div_le_self (orderedNormAt_nonneg x _) (by norm_num : (1 : ℝ) ≤ 10)).trans hFirst)
  obtain ⟨u, hu, hError⟩ := normalized_sourceT2_net_approximation ha haOne hSize h hL hCubic x hx hNorm
  obtain ⟨w, hw, hCError⟩ := steep_constant_net_approximation hd c hCenter
  exact ⟨u, hu, w, hw, hError, hCError⟩

theorem shifted_kernel_net_action_le {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (x u : Fin n → ℂ) (c w : ℂ) {R : ℝ}
    (hKernel : (retainedShiftedMatrix I ζ rows).mulVec (fun j => x j + c) = 0)
    (hError : ‖(WithLp.toLp 2 ((retainedShiftedMatrix I ζ rows).mulVec
      (fun j => (x j + c) - (u j + w))) : EuclideanSpace ℂ I)‖ ≤ R) :
    shiftedRowsL2Norm (fun i : I => rows i.val) u w ζ (fun i => i.val) ≤ R := by
  have hAction : (retainedShiftedMatrix I ζ rows).mulVec
      (fun j => (x j + c) - (u j + w)) =
        -((retainedShiftedMatrix I ζ rows).mulVec (fun j => u j + w)) := by
    change (retainedShiftedMatrix I ζ rows).mulVec
      ((fun j => x j + c) - (fun j => u j + w)) = _
    rw [Matrix.mulVec_sub, hKernel, zero_sub]
  rw [hAction, WithLp.toLp_neg, norm_neg] at hError
  rw [shiftedRowsL2Norm_eq_matrix_action]
  exact hError

theorem normalized_shifted_sourceT1_kernel_net {n d L : ℕ} {Z₀ : ℝ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (hZ : 0 ≤ Z₀)
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d)
    (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (hx : x ∈ sourceT1 n d L)
    (hNorm : orderedNormAt x (firstSteepScale n d) = 1)
    (c : ℂ) (hc : ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10)
    (hKernel : (retainedShiftedMatrix I ζ rows).mulVec (fun j => x j + c) = 0) :
    ∃ u ∈ sourceT1Net n d, ∃ w ∈ steepConstantNet d 1,
      shiftedRowsL2Norm (fun i : I => rows i.val) u w ζ (fun i => i.val) ≤
        2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  obtain ⟨u, hu, w, hw, hX, hC⟩ := normalized_shifted_sourceT1_net_cover h hL hCubic x hx hNorm c hc
  exact ⟨u, hu, w, hw, shifted_kernel_net_action_le I ζ rows x u c w hKernel
    (source_shifted_net_matrix_error hd hZ I ζ hShift rows x u c w hX hC)⟩

theorem normalized_shifted_sourceT2_kernel_net {n d L : ℕ} {a₃ Z₀ : ℝ}
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hSize : 2 ≤ a₃ * (n : ℝ))
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (hZ : 0 ≤ Z₀)
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d)
    (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (hx : x ∈ sourceT2 n d L a₃)
    (hNorm : orderedNormAt x (secondSteepScale n d) = 1)
    (c : ℂ) (hc : ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10)
    (hKernel : (retainedShiftedMatrix I ζ rows).mulVec (fun j => x j + c) = 0) :
    ∃ u ∈ sourceT2Net n d a₃, ∃ w ∈ steepConstantNet d (Real.rpow (d : ℝ) (3 / 2)),
      shiftedRowsL2Norm (fun i : I => rows i.val) u w ζ (fun i => i.val) ≤
        2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  obtain ⟨u, hu, w, hw, hX, hC⟩ :=
    normalized_shifted_sourceT2_net_cover ha haOne hSize h hL hCubic x hx hNorm c hc
  exact ⟨u, hu, w, hw, shifted_kernel_net_action_le I ζ rows x u c w hKernel
    (source_shifted_net_matrix_error hd hZ I ζ hShift rows x u c w hX hC)⟩

end CircularLaw
