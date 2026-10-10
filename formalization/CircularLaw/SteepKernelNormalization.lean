import CircularLaw.ShiftedSteepNetCover

/-!
# Normalization of every literal shifted steep kernel vector

The strict `T1` and `T2` jumps make the relevant modulus positive.
Scaling the nonconstant part and its permitted center by the same
nonzero complex scalar preserves the class, the center condition and
the actual rectangular kernel equation.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem shifted_kernel_normalize_at_rank {n d rank : ℕ} (S : Set (Fin n → ℂ))
    (hHomogeneous : ∀ z : ℂ, z ≠ 0 → ∀ x ∈ S, z • x ∈ S)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (x : Fin n → ℂ) (hx : x ∈ S) (hPos : 0 < orderedNormAt x rank)
    (c : ℂ) (hc : ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10)
    (hKernel : (retainedShiftedMatrix I ζ rows).mulVec (fun j => x j + c) = 0) :
    ∃ y ∈ S, orderedNormAt y rank = 1 ∧ ∃ w : ℂ,
      ‖w‖ ≤ orderedNormAt y (firstSteepScale n d) / 10 ∧
        (retainedShiftedMatrix I ζ rows).mulVec (fun j => y j + w) = 0 := by
  let B := orderedNormAt x rank
  let z : ℂ := (B : ℂ)⁻¹
  have hB : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hPos.ne'
  have hz : z ≠ 0 := inv_ne_zero hB
  have hNormZ : ‖z‖ = B⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPos]
  refine ⟨z • x, hHomogeneous z hz x hx, ?_, z * c, ?_, ?_⟩
  · rw [orderedNormAt_smul, hNormZ]
    exact inv_mul_cancel₀ hPos.ne'
  · rw [norm_mul, orderedNormAt_smul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hc (norm_nonneg z)
  · have hSum : (fun j => (z • x) j + z * c) = z • (fun j => x j + c) := by
      funext j
      simp only [Pi.smul_apply, smul_eq_mul, mul_add]
    rw [hSum, Matrix.mulVec_smul, hKernel, smul_zero]

theorem source_shifted_T1_kernel_normalization {n d L : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (v : Fin n → ℂ) (hv : v ∈ sourceShiftedT1 n d L)
    (hKernel : (retainedShiftedMatrix I ζ rows).mulVec v = 0) :
    ∃ x ∈ sourceT1 n d L, orderedNormAt x (firstSteepScale n d) = 1 ∧ ∃ c : ℂ,
      ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10 ∧
        (retainedShiftedMatrix I ζ rows).mulVec (fun j => x j + c) = 0 := by
  obtain ⟨x, c, hx, hc, hEq⟩ := hv
  have hPos : 0 < orderedNormAt x (firstSteepScale n d) :=
    lt_of_le_of_lt (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) (3 / 2))
      (orderedNormAt_nonneg x _)) hx.2.2
  rw [hEq] at hKernel
  exact shifted_kernel_normalize_at_rank (sourceT1 n d L)
    (fun z hz y hy => (sourceT1_smul_iff z hz y).mpr hy) I ζ rows x hx hPos c hc hKernel

theorem source_shifted_T2_kernel_normalization {n d L : ℕ} {a₃ : ℝ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (v : Fin n → ℂ) (hv : v ∈ sourceShiftedT2 n d L a₃)
    (hKernel : (retainedShiftedMatrix I ζ rows).mulVec v = 0) :
    ∃ x ∈ sourceT2 n d L a₃, orderedNormAt x (secondSteepScale n d) = 1 ∧ ∃ c : ℂ,
      ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10 ∧
        (retainedShiftedMatrix I ζ rows).mulVec (fun j => x j + c) = 0 := by
  obtain ⟨x, c, hx, hc, hEq⟩ := hv
  have hPos : 0 < orderedNormAt x (secondSteepScale n d) :=
    lt_of_le_of_lt (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) (3 / 2))
      (orderedNormAt_nonneg x _)) hx.2.2.2
  rw [hEq] at hKernel
  exact shifted_kernel_normalize_at_rank (sourceT2 n d L a₃)
    (fun z hz y hy => (sourceT2_smul_iff z hz y a₃).mpr hy) I ζ rows x hx hPos c hc hKernel

end CircularLaw
