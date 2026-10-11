import CircularLaw.RowLoadFailure
import CircularLaw.UniformSourceKernelConditions

/-!
# The source row-load failure rate

Small-set entropy is absorbed into the checked row-count rate. A single
small positive third-scale constant is sufficient, and the resulting
`exp(-c*n)` bound is uniform over the literal lower degree band and both
source codimensions.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_row_load_degree_entropy :
    ∀ᶠ d : ℕ in atTop, smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4 := by
  have hDen : Tendsto (fun d : ℕ => (16 : ℝ) * d) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 16)).mpr
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  have hLimit : Tendsto (fun d : ℕ => 1 / (16 * (d : ℝ))) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hDen
  have hEntropy := (smallSetEntropy_continuous.continuousAt.tendsto (x := (0 : ℝ))).comp hLimit
  rw [smallSetEntropy_zero] at hEntropy
  exact (hEntropy.eventually (gt_mem_nhds (div_pos rowLoadRate_pos (by norm_num)))).mono
    (fun _ h => h.le)

theorem row_load_prefactor_absorbed {n : ℕ} (hDimension : 4 * Real.log 2 ≤ rowLoadRate * n) :
    (2 : ℝ) * Real.exp (-(rowLoadRate / 2) * n) ≤ Real.exp (-(rowLoadRate / 4) * n) := by
  calc
    _ = Real.exp (Real.log 2) * Real.exp (-(rowLoadRate / 2) * n) := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp (Real.log 2 - (rowLoadRate / 2) * n) := by
      rw [← Real.exp_add, sub_eq_add_neg, neg_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem uniform_row_load_failure_absorbed {n d : ℕ} {a₃ : ℝ} (hd : 0 < d) (hdn : d ≤ n)
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hk : 0 < thirdSteepScale n a₃)
    (I : Finset (Fin n)) (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy3 : smallSetEntropy a₃ ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 2 ≤ rowLoadRate * n) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceRowLoad I (thirdSteepScale n a₃) rows) ≤
      Real.exp (-(rowLoadRate / 4) * n) := by
  have hRowScaled := mul_le_mul_of_nonneg_left hRows rowLoadRate_pos.le
  have hSmall0 := mul_le_mul_of_nonneg_left hEntropy0 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hSmall3 := mul_le_mul_of_nonneg_left hEntropy3 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hNRate : (0 : ℝ) ≤ rowLoadRate * n := mul_nonneg rowLoadRate_pos.le (Nat.cast_nonneg n)
  have hExp0 : Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ))) - rowLoadRate * I.card) ≤
      Real.exp (-(rowLoadRate / 2) * n) := Real.exp_le_exp.mpr (by nlinarith)
  have hExp3 : Real.exp ((n : ℝ) * smallSetEntropy a₃ - rowLoadRate * I.card) ≤
      Real.exp (-(rowLoadRate / 2) * n) := Real.exp_le_exp.mpr (by nlinarith)
  apply (uniform_row_load_failure_entropy hd hdn ha haOne hk I).trans
  apply (add_le_add hExp0 hExp3).trans
  simpa only [two_mul] using row_load_prefactor_absorbed hDimension

theorem eventually_source_row_load_failure_uniform {C a₃ : ℝ} (hC : 0 < C)
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hEntropy : smallSetEntropy a₃ ≤ rowLoadRate / 4)
    (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceRowLoad I (thirdSteepScale n a₃) rows) ≤
          Real.exp (-(rowLoadRate / 4) * n) := by
  have hNSize : ∀ᶠ n : ℕ in atTop, 2 / a₃ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop _
  have hNRate : ∀ᶠ n : ℕ in atTop, 4 * Real.log 2 / rowLoadRate ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC eventually_row_load_degree_entropy, hNSize, hNRate]
    with n hConditions hDegreeEntropy hNSize hNRate
  intro d hBand L hL I hI
  have h := hConditions d hBand.1 hBand.2
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hdn : d ≤ n := by
    have hPower := Nat.pow_le_pow_right hd (by decide : 1 ≤ 4)
    simp only [pow_one] at hPower
    have hDimension := h.dimension_fourth
    omega
  have hn3 : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans h.dimension_fourth
  have hRows := kernelCodimension_retained_card (by have hLarge := h.degree_large; omega) hn3 hL I hI
  have hSize : 2 ≤ a₃ * (n : ℝ) := by
    have hScaled := (div_le_iff₀ ha).mp hNSize
    nlinarith
  have hk := (thirdSteepScale_bounds ha hSize).1
  have hDim := (div_le_iff₀ rowLoadRate_pos).mp hNRate
  exact uniform_row_load_failure_absorbed hd hdn ha (by linarith) hk I hRows
    (hDegreeEntropy d hBand.1) hEntropy (by nlinarith)

theorem source_row_load_small_constant :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 1000 ∧
      ∀ a₃ : ℝ, 0 < a₃ → a₃ ≤ a → smallSetEntropy a₃ ≤ rowLoadRate / 4 := by
  obtain ⟨b, hb, _, hEntropy⟩ := small_set_entropy_threshold
    (show (0 : ℝ) < rowLoadRate / 4 from div_pos rowLoadRate_pos (by norm_num))
  refine ⟨min b (1 / 1000), lt_min hb (by norm_num), min_le_right _ _, ?_⟩
  intro a₃ ha hSmall
  exact hEntropy a₃ ha (hSmall.trans (min_le_left _ _))

end CircularLaw
