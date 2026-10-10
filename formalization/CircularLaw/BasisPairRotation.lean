import CircularLaw.FourierBasisMass

/-!
# Pair rotations of an orthonormal basis

Replacing two basis vectors by their normalized sum and difference
preserves orthonormality. The ambient coordinate l1 masses satisfy the
triangle inequality used to compare a maximizing basis pair.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def basisPairRotationFrame {κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : OrthonormalBasis κ ℂ E) (i j k : κ) : E :=
  if k = i then (Real.sqrt (1 / 2 : ℝ) : ℂ) • (B i + B j)
  else if k = j then (Real.sqrt (1 / 2 : ℝ) : ℂ) • (B i - B j)
  else B k

theorem basis_pair_rotation_frame_orthonormal {κ E : Type*} [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (B : OrthonormalBasis κ ℂ E) {i j : κ} (hij : i ≠ j) :
    Orthonormal ℂ (basisPairRotationFrame B i j) := by
  classical
  have hSquare : (Real.sqrt (1 / 2 : ℝ) : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [orthonormal_iff_ite]
  intro k l
  unfold basisPairRotationFrame
  split_ifs <;>
    simp_all only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, B.inner_eq_ite, Complex.conj_ofReal] <;>
    grind

def basisPairRotation {κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (B : OrthonormalBasis κ ℂ E) {i j : κ} (hij : i ≠ j) : OrthonormalBasis κ ℂ E :=
  OrthonormalBasis.mk (basis_pair_rotation_frame_orthonormal B hij)
    ((basis_pair_rotation_frame_orthonormal B hij).linearIndependent.span_eq_top_of_card_eq_finrank'
      (Module.finrank_eq_card_basis B.toBasis).symm).ge

theorem basis_pair_rotation_apply {κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (B : OrthonormalBasis κ ℂ E) {i j : κ} (hij : i ≠ j) (k : κ) :
    basisPairRotation B hij k = basisPairRotationFrame B i j k := by
  exact congrFun (OrthonormalBasis.coe_mk _ _) k

def coordinateL1Mass {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) : ℝ :=
  ∑ i, ‖v i‖

theorem coordinate_l1_mass_nonneg {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    0 ≤ coordinateL1Mass v := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem coordinate_l1_mass_real_smul {ι : Type*} [Fintype ι]
    (r : ℝ) (v : EuclideanSpace ℂ ι) :
    coordinateL1Mass ((r : ℂ) • v) = |r| * coordinateL1Mass v := by
  simp only [coordinateL1Mass, PiLp.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, Finset.mul_sum]

theorem coordinate_l1_mass_sum_difference {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℂ ι) :
    2 * coordinateL1Mass v ≤ coordinateL1Mass (u + v) + coordinateL1Mass (u - v) := by
  unfold coordinateL1Mass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := norm_sub_le (u i + v i) (u i - v i)
  have hDiff : (u i + v i) - (u i - v i) = (2 : ℂ) * v i := by ring
  rw [hDiff, norm_mul] at h
  norm_num only [Complex.norm_ofNat] at h
  exact h

theorem basis_pair_rotation_l1_mass {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V)
    {i j : κ} (hij : i ≠ j) :
    subspaceBasisL1Mass (basisPairRotation B hij) = subspaceBasisL1Mass B -
      coordinateL1Mass (B i : EuclideanSpace ℂ ι) -
      coordinateL1Mass (B j : EuclideanSpace ℂ ι) +
      coordinateL1Mass (basisPairRotation B hij i : EuclideanSpace ℂ ι) +
      coordinateL1Mass (basisPairRotation B hij j : EuclideanSpace ℂ ι) := by
  classical
  have hPoint (k : κ) :
      coordinateL1Mass (basisPairRotation B hij k : EuclideanSpace ℂ ι) =
        coordinateL1Mass (B k : EuclideanSpace ℂ ι) +
        (if k = i then coordinateL1Mass (basisPairRotation B hij i : EuclideanSpace ℂ ι) -
          coordinateL1Mass (B i : EuclideanSpace ℂ ι) else 0) +
        (if k = j then coordinateL1Mass (basisPairRotation B hij j : EuclideanSpace ℂ ι) -
          coordinateL1Mass (B j : EuclideanSpace ℂ ι) else 0) := by
    by_cases hki : k = i
    · subst k
      simp only [ite_true, if_neg hij]
      ring
    · by_cases hkj : k = j
      · subst k
        simp only [ite_true, if_neg (Ne.symm hij)]
        ring
      · have hEq : basisPairRotation B hij k = B k := by
          rw [basis_pair_rotation_apply]
          simp only [basisPairRotationFrame, if_neg hki, if_neg hkj]
        rw [hEq]
        simp only [if_neg hki, if_neg hkj, add_zero]
  change (∑ k, coordinateL1Mass (basisPairRotation B hij k : EuclideanSpace ℂ ι)) = _
  rw [Finset.sum_congr rfl (fun k _ => hPoint k)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change subspaceBasisL1Mass B + _ + _ = _
  ring

theorem basis_pair_rotation_pair_l1_lower {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V)
    {i j : κ} (hij : i ≠ j) :
    (5 / 4) * coordinateL1Mass (B j : EuclideanSpace ℂ ι) ≤
      coordinateL1Mass (basisPairRotation B hij i : EuclideanSpace ℂ ι) +
      coordinateL1Mass (basisPairRotation B hij j : EuclideanSpace ℂ ι) := by
  have hRoot := Real.sqrt_nonneg (1 / 2 : ℝ)
  have hSquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hScale : 5 / 4 ≤ 2 * Real.sqrt (1 / 2 : ℝ) := by nlinarith
  simp only [basis_pair_rotation_apply, basisPairRotationFrame, ite_true,
    if_neg (Ne.symm hij), Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sub]
  rw [coordinate_l1_mass_real_smul, coordinate_l1_mass_real_smul, abs_of_nonneg hRoot]
  have hTriangle := coordinate_l1_mass_sum_difference
    (B i : EuclideanSpace ℂ ι) (B j : EuclideanSpace ℂ ι)
  calc
    _ ≤ (2 * Real.sqrt (1 / 2 : ℝ)) * coordinateL1Mass (B j : EuclideanSpace ℂ ι) :=
      mul_le_mul_of_nonneg_right hScale (coordinate_l1_mass_nonneg _)
    _ ≤ _ := by nlinarith

end CircularLaw
