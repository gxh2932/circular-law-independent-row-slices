import CircularLaw.SourceHomogeneity
import CircularLaw.SourceVerySteepInclusion

/-!
# Normalization into the exact source gradual class

The class and its nonzero complex scalar cone reproduce the manuscript's
definitions. The final deterministic kernel alternative is derived from
the stated class exclusions, with no homogeneity or normalization result
assumed.
-/

noncomputable section
open Classical

namespace CircularLaw

def sourceGradual (n d L : ℕ) (a₃ : ℝ) : Set (Fin n → ℂ) :=
  {x | x ∉ sourceSteepUnion n d L a₃ ∧ x ∉ sourceAlmostConstant n d a₃ ∧
    orderedNormAt x (thirdSteepScale n a₃) = 1}

def nonzeroScalarCone {n : ℕ} (S : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {v | ∃ z : ℂ, z ≠ 0 ∧ ∃ x ∈ S, v = z • x}

theorem sourceAlmostConstant_of_tail_zero {n d : ℕ} {a₃ : ℝ}
    (hk : 0 < thirdSteepScale n a₃) (hkn : thirdSteepScale n a₃ ≤ n)
    (x : Fin n → ℂ) (hZero : orderedNormAt x (thirdSteepScale n a₃) = 0) :
    x ∈ sourceAlmostConstant n d a₃ := by
  let k := thirdSteepScale n a₃
  let F := (Finset.univ : Finset (Fin n)) \ orderedPrefix x (k - 1)
  have hCard : F.card = n - (k - 1) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      orderedPrefix_card x (by omega : k - 1 ≤ n)]
  have hSub : F ⊆ almostConstantCoordinates x k (almostConstantRadius d) 0 := by
    intro j hj
    have hjNot := (Finset.mem_sdiff.mp hj).2
    have hRank : (⟨k - 1, by omega⟩ : Fin n) ≤ (normOrderPerm x).symm j := by
      apply Fin.le_iff_val_le_val.mpr
      change k - 1 ≤ ((normOrderPerm x).symm j).val
      have hNot : ¬((normOrderPerm x).symm j).val < k - 1 := fun h =>
        hjNot ((mem_orderedPrefix x (k - 1) j).mpr h)
      omega
    have hNorm := orderedNorm_antitone x hRank
    rw [orderedNorm_of_rank, ← orderedNormAt_eq x hk hkn, hZero] at hNorm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, by
      change ‖x j - 0‖ ≤ almostConstantRadius d * orderedNormAt x (thirdSteepScale n a₃)
      simpa only [sub_zero, hZero, mul_zero] using hNorm⟩
  refine ⟨0, ?_⟩
  have hCount := Finset.card_le_card hSub
  rw [hCard] at hCount
  change n - thirdSteepScale n a₃ < _
  dsimp only [k] at hCount
  omega

theorem source_not_almost_constant_tail_pos {n d : ℕ} {a₃ : ℝ}
    (hk : 0 < thirdSteepScale n a₃) (hkn : thirdSteepScale n a₃ ≤ n)
    (x : Fin n → ℂ) (hB : x ∉ sourceAlmostConstant n d a₃) :
    0 < orderedNormAt x (thirdSteepScale n a₃) := by
  by_contra h
  have hZero := le_antisymm (le_of_not_gt h) (orderedNormAt_nonneg x (thirdSteepScale n a₃))
  exact hB (sourceAlmostConstant_of_tail_zero hk hkn x hZero)

theorem source_gradual_normalization {n d L : ℕ} {a₃ : ℝ}
    (hk : 0 < thirdSteepScale n a₃) (hkn : thirdSteepScale n a₃ ≤ n)
    (x : Fin n → ℂ) (hT : x ∉ sourceSteepUnion n d L a₃)
    (hB : x ∉ sourceAlmostConstant n d a₃) :
    (orderedNormAt x (thirdSteepScale n a₃) : ℂ)⁻¹ • x ∈ sourceGradual n d L a₃ := by
  let B := orderedNormAt x (thirdSteepScale n a₃)
  have hPositive : 0 < B := source_not_almost_constant_tail_pos hk hkn x hB
  have hComplex : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hPositive.ne'
  have hInv : (B : ℂ)⁻¹ ≠ 0 := inv_ne_zero hComplex
  have hNorm : ‖(B : ℂ)⁻¹‖ = B⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPositive]
  refine ⟨fun h => hT ((sourceSteepUnion_smul_iff _ hInv x a₃).mp h),
    fun h => hB ((sourceAlmostConstant_smul_iff _ hInv x a₃).mp h), ?_⟩
  rw [orderedNormAt_smul, hNorm]
  exact inv_mul_cancel₀ hPositive.ne'

theorem source_gradual_cone_of_not_steep_not_almost_constant {n d L : ℕ} {a₃ : ℝ}
    (hk : 0 < thirdSteepScale n a₃) (hkn : thirdSteepScale n a₃ ≤ n)
    (x : Fin n → ℂ) (hT : x ∉ sourceSteepUnion n d L a₃)
    (hB : x ∉ sourceAlmostConstant n d a₃) :
    x ∈ nonzeroScalarCone (sourceGradual n d L a₃) := by
  let B := orderedNormAt x (thirdSteepScale n a₃)
  have hPositive : 0 < B := source_not_almost_constant_tail_pos hk hkn x hB
  have hComplex : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hPositive.ne'
  refine ⟨(B : ℂ), hComplex, (B : ℂ)⁻¹ • x, source_gradual_normalization hk hkn x hT hB, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hComplex, one_smul]

theorem sourceSteepUnion_subset_shifted {n d L : ℕ} (a₃ : ℝ) :
    sourceSteepUnion n d L a₃ ⊆ sourceShiftedSteepUnion n d L a₃ := by
  intro x hx
  refine ⟨x, 0, hx, ?_, ?_⟩
  · simp only [norm_zero]
    exact div_nonneg (orderedNormAt_nonneg x _) (by norm_num)
  · ext j
    simp only [add_zero]

theorem source_kernel_alternative_of_class_exclusions {n d L : ℕ} {a₃ a : ℝ}
    (hk : 0 < thirdSteepScale n a₃) (hkn : thirdSteepScale n a₃ ≤ n)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (h₀ : ∀ x ∈ sourceShiftedT0 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (h₁ : ∀ x ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (h₂ : ∀ x ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (hB : ∀ x ∈ sourceAlmostConstant n d a₃ \ sourceShiftedT3 n d L,
      x ≠ 0 → (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (hVL : sourceShiftedT3 n d L ⊆ sourceVL n L a) :
    {x | x ≠ 0 ∧ (retainedShiftedMatrix I ζ rows).mulVec x = 0} ⊆
      sourceVL n L a ∪ nonzeroScalarCone (sourceGradual n d L a₃) := by
  intro x hx
  by_cases h₃ : x ∈ sourceShiftedT3 n d L
  · exact Or.inl (hVL h₃)
  have hNotB : x ∉ sourceAlmostConstant n d a₃ := fun hxB => hB x ⟨hxB, h₃⟩ hx.1 hx.2
  have hNotT : x ∉ sourceSteepUnion n d L a₃ := by
    intro hxT
    have hShift := sourceSteepUnion_subset_shifted a₃ hxT
    rw [sourceShiftedSteepUnion_eq] at hShift
    rcases hShift with ((h0 | h1) | h2) | h3
    · exact h₀ x h0 hx.2
    · exact h₁ x h1 hx.2
    · exact h₂ x h2 hx.2
    · exact h₃ h3
  exact Or.inr (source_gradual_cone_of_not_steep_not_almost_constant hk hkn x hNotT hNotB)

end CircularLaw
