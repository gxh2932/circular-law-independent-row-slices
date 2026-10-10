import CircularLaw.StructuralFailureBudgets
import CircularLaw.RestrictedNormUniform
import CircularLaw.RetainedRowOrthogonality

/-!
# The full named row-slice structural theorem

The checked retained norm tail closes the last probability premise.
Absolute positive decomposition, normal-rank and lower-degree constants
are chosen before sigma and the spectral window. The actual two
alternatives then hold with probability at least `1-5/n`, uniformly in
the degree band, both source codimensions and each deterministic row set.
-/

noncomputable section
open Classical Filter
open scoped Topology InnerProductSpace

namespace CircularLaw

theorem eventually_source_structural_kernel_good_uniform {a a₃ C σ : ℝ}
    (hC : sourceKernelLowerConstant ≤ C) (hC96 : 96 ≤ C)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 65536)
    (hEntropy : smallSetEntropy a₃ ≤ rowLoadRate / 4)
    (ha₃Net : 7 * a₃ ≤ equalBlockRateConstant (1 / 4) / 4800)
    (ha : 0 < a) (haOne : a ≤ 1) (hσ : σ ≤ 1) (Z₀ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
          1 - 5 / (n : ℝ) ≤ uniformProbability (SourceStructuralKernel (d := d) L a I ζ) := by
  have hNorm := eventually_retainedCenteredNormBound_hundred_uniform hC96 σ
  have hNorm' : ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ¬RetainedCenteredNormBound I rows (rowSliceComplexNormConstant 100)) ≤
            1 / (n : ℝ) ^ 100 := by
    filter_upwards [hNorm] with n hn
    intro d hBand _ _ I _
    exact hn d hBand I
  have hGood := eventually_source_structural_kernel_good_of_norm_tail_uniform hC hC96 ha₃ ha₃Small
    hEntropy ha₃Net ha haOne hσ (rowSliceComplexNormConstant 100) (max 0 Z₀)
    (rowSliceComplexNormConstant_nonneg (by norm_num)) (le_max_left _ _) hNorm'
  filter_upwards [hGood] with n hn
  intro d hBand L hL I hI ζ hShift
  exact hn d hBand L hL I hI ζ
    (hShift.trans (mul_le_mul_of_nonneg_right (le_max_right 0 Z₀) (Real.sqrt_nonneg _)))

def SourceStructuralRowSpan {n d : ℕ} (L : ℕ) (a : ℝ) (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) : Prop :=
  ∀ v : Fin n → ℂ, v ≠ 0 →
    (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n)) ∈ (retainedRowSpan I ζ rows)ᗮ →
    (∃ i : ℕ, 0 < i ∧ i ≤ sourceNormalRank a L ∧
      (9 / 10 : ℝ) * ((n : ℝ) / i) ^ 3 * orderedNormAt v (sourceNormalRank a L) <
        orderedNormAt v i) ∨
    (∀ i : ℕ, 0 < i → i ≤ sourceNormalRank a L →
      orderedNormAt v i ≤
        (9 / 10 : ℝ) * ((n : ℝ) / i) ^ 3 * orderedNormAt v (sourceNormalRank a L)) ∧
    ∀ center : ℂ,
      ((Finset.univ.filter (fun j => ‖v j - center‖ ≤
        Real.exp (-2 * structuralGrowth n L) * orderedNormAt v (sourceNormalRank a L))).card : ℝ) ≤
          structuralClusterFraction n L * n

theorem sourceStructuralRowSpan_iff_kernel {n d : ℕ} (L : ℕ) (a : ℝ)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) :
    SourceStructuralRowSpan L a I ζ rows ↔ SourceStructuralKernel L a I ζ rows := by
  constructor
  · intro h v hv hKernel
    exact h v hv ((retainedRowSpan_orthogonal_iff_kernel I ζ rows v).mpr hKernel)
  · intro h v hv hOrthogonal
    exact h v hv ((retainedRowSpan_orthogonal_iff_kernel I ζ rows v).mp hOrthogonal)

def RowSliceStructuralTheorem : Prop :=
  ∃ a Cstar : ℝ, 0 < a ∧ 0 < Cstar ∧
    ∀ C : ℝ, Cstar ≤ C → ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
        ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
          ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
            1 - 5 / (n : ℝ) ≤ uniformProbability (SourceStructuralRowSpan (d := d) L a I ζ)

theorem row_slice_structural_theorem : RowSliceStructuralTheorem := by
  obtain ⟨aLoad, haLoad, _, hEntropy⟩ := source_row_load_small_constant
  let a₃ : ℝ := min aLoad (min (1 / 65536) (equalBlockRateConstant (1 / 4) / 33600))
  have ha₃ : 0 < a₃ := lt_min haLoad (lt_min (by norm_num)
    (div_pos (equalBlockRateConstant_pos (by norm_num)) (by norm_num)))
  have haLoadBound : a₃ ≤ aLoad := min_le_left _ _
  have haSmall : a₃ ≤ 1 / 65536 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have haRate : a₃ ≤ equalBlockRateConstant (1 / 4) / 33600 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have haNet : 7 * a₃ ≤ equalBlockRateConstant (1 / 4) / 4800 := by linarith only [haRate]
  let Cstar : ℝ := max sourceKernelLowerConstant 96
  have hCstar : 0 < Cstar := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 96) (le_max_right _ _)
  refine ⟨1 / 2, Cstar, by norm_num, hCstar, ?_⟩
  intro C hC σ Z₀ _ hσ
  have hKernel : sourceKernelLowerConstant ≤ C := (le_max_left _ _).trans hC
  have hNorm : 96 ≤ C := (le_max_right _ _).trans hC
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_source_structural_kernel_good_uniform hKernel hNorm ha₃ haSmall
    (hEntropy a₃ ha₃ haLoadBound) haNet (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hσ.le Z₀)
  refine ⟨N, ?_⟩
  intro n hn d hBand L hL I hI ζ hShift
  apply (hN n hn d hBand L hL I hI ζ hShift).trans
  exact uniformProbability_mono (fun rows hGood =>
    (sourceStructuralRowSpan_iff_kernel L (1 / 2) I ζ rows).mpr hGood)

end CircularLaw
