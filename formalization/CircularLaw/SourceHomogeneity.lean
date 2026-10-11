import CircularLaw.AlmostConstantGeometry

/-!
# Homogeneity of the literal source order statistics and classes

Sorted moduli scale by the scalar norm even when sorting permutations
change. The recursive steep classes and the count-defined almost-constant
class are invariant under every nonzero complex scalar.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem orderedNorm_smul {n : ℕ} (z : ℂ) (x : Fin n → ℂ) (i : Fin n) :
    orderedNorm (z • x) i = ‖z‖ * orderedNorm x i := by
  let f : Fin n → ℝ := fun j => ‖(z • x) j‖
  have hNew : Antitone (f ∘ normOrderPerm (z • x)) := orderedNorm_antitone (z • x)
  have hOld : Antitone (f ∘ normOrderPerm x) := by
    intro a b hab
    change ‖z * x (normOrderPerm x b)‖ ≤ ‖z * x (normOrderPerm x a)‖
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (orderedNorm_antitone x hab) (norm_nonneg z)
  have hSame := congrFun (Tuple.unique_antitone hNew hOld) i
  change orderedNorm (z • x) i = ‖z * x (normOrderPerm x i)‖ at hSame
  rw [hSame, norm_mul]
  rfl

theorem orderedNormAt_smul {n : ℕ} (z : ℂ) (x : Fin n → ℂ) (k : ℕ) :
    orderedNormAt (z • x) k = ‖z‖ * orderedNormAt x k := by
  by_cases hk : 0 < k ∧ k ≤ n
  · simp only [orderedNormAt, dif_pos hk, orderedNorm_smul]
  · simp only [orderedNormAt, dif_neg hk, mul_zero]

theorem ordered_jump_smul_iff {n : ℕ} (z : ℂ) (hz : z ≠ 0)
    (x : Fin n → ℂ) (A : ℝ) (r s : ℕ) :
    A * orderedNormAt (z • x) r < orderedNormAt (z • x) s ↔
      A * orderedNormAt x r < orderedNormAt x s := by
  rw [orderedNormAt_smul, orderedNormAt_smul,
    show A * (‖z‖ * orderedNormAt x r) = ‖z‖ * (A * orderedNormAt x r) by ring,
    mul_lt_mul_iff_right₀ (norm_pos_iff.mpr hz)]

theorem sourceT3_smul_iff {n d L : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) :
    z • x ∈ sourceT3 n d L ↔ x ∈ sourceT3 n d L := by
  simp only [sourceT3, Set.mem_setOf_eq, ordered_jump_smul_iff z hz]

theorem sourceT0JumpAt_smul_iff {n d i : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) :
    sourceT0JumpAt n d i (z • x) ↔ sourceT0JumpAt n d i x :=
  ordered_jump_smul_iff z hz x (4 * d) _ _

theorem sourceT0Previous_smul_iff {n d L : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) (i : ℕ) :
    z • x ∈ sourceT0Previous n d L i ↔ x ∈ sourceT0Previous n d L i := by
  induction i with
  | zero => exact sourceT3_smul_iff z hz x
  | succ i ih =>
    simp only [sourceT0Previous, Set.mem_union, Set.mem_setOf_eq, ih, sourceT0JumpAt_smul_iff z hz]

theorem sourceT0ClassAt_smul_iff {n d L i : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) :
    z • x ∈ sourceT0ClassAt n d L i ↔ x ∈ sourceT0ClassAt n d L i := by
  simp only [sourceT0ClassAt, Set.mem_setOf_eq, sourceT0Previous_smul_iff z hz,
    sourceT0JumpAt_smul_iff z hz]

theorem sourceT0_smul_iff {n d L : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) :
    z • x ∈ sourceT0 n d L ↔ x ∈ sourceT0 n d L := by
  simp only [sourceT0, Set.mem_setOf_eq, sourceT0ClassAt_smul_iff z hz]

theorem sourceT1_smul_iff {n d L : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) :
    z • x ∈ sourceT1 n d L ↔ x ∈ sourceT1 n d L := by
  simp only [sourceT1, Set.mem_setOf_eq, sourceT0_smul_iff z hz, sourceT3_smul_iff z hz,
    ordered_jump_smul_iff z hz]

theorem sourceT2_smul_iff {n d L : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) (a₃ : ℝ) :
    z • x ∈ sourceT2 n d L a₃ ↔ x ∈ sourceT2 n d L a₃ := by
  simp only [sourceT2, Set.mem_setOf_eq, sourceT0_smul_iff z hz, sourceT1_smul_iff z hz,
    sourceT3_smul_iff z hz, ordered_jump_smul_iff z hz]

theorem sourceSteepUnion_smul_iff {n d L : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) (a₃ : ℝ) :
    z • x ∈ sourceSteepUnion n d L a₃ ↔ x ∈ sourceSteepUnion n d L a₃ := by
  simp only [sourceSteepUnion, Set.mem_union, sourceT0_smul_iff z hz, sourceT1_smul_iff z hz,
    sourceT2_smul_iff z hz, sourceT3_smul_iff z hz]

theorem almostConstantCoordinates_smul {n : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ)
    (k : ℕ) (θ : ℝ) (c : ℂ) :
    almostConstantCoordinates (z • x) k θ (z * c) = almostConstantCoordinates x k θ c := by
  ext j
  have hDifference : (z • x) j - z * c = z * (x j - c) := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_sub]
  simp only [almostConstantCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
    hDifference, norm_mul, orderedNormAt_smul]
  rw [show θ * (‖z‖ * orderedNormAt x k) = ‖z‖ * (θ * orderedNormAt x k) by ring,
    mul_le_mul_iff_right₀ (norm_pos_iff.mpr hz)]

theorem sourceAlmostConstant_smul_iff {n d : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) (a₃ : ℝ) :
    z • x ∈ sourceAlmostConstant n d a₃ ↔ x ∈ sourceAlmostConstant n d a₃ := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨z⁻¹ * c, ?_⟩
    rw [← almostConstantCoordinates_smul z hz x]
    simpa only [mul_inv_cancel_left₀ hz] using hc
  · rintro ⟨c, hc⟩
    refine ⟨z * c, ?_⟩
    rwa [almostConstantCoordinates_smul z hz x]

end CircularLaw
