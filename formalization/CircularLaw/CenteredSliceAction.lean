import CircularLaw.ScalarMeanGrid
import CircularLaw.FullMatrixFixedNet

/-!
# Centered row action and the exact net-shift identity

The restricted norm is represented by its actual action on every
complex vector. Zero coordinate sum removes the expected row action.
The deterministic shifted-kernel identity uses the exact row sum `d`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def centeredRowLinearForm {n d : ℕ} (S : RowSlice n d) (v : Fin n → ℂ) : ℂ :=
  ∑ j, centeredRow S j * v j

def RetainedCenteredNormBound {n d : ℕ} (I : Finset (Fin n))
    (rows : RowSliceMatrix n d) (B : ℝ) : Prop :=
  ∀ v : Fin n → ℂ,
    ‖(WithLp.toLp 2 (fun i : I => centeredRowLinearForm (rows i.val) v) : EuclideanSpace ℂ I)‖ ≤
      B * Real.sqrt d * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖

def canonicalNetShift {n : ℕ} (I : Finset (Fin n)) (d : ℕ) (ζ : ℂ)
    (y : Fin n → ℂ) (β : ℂ) (i : I) : ℂ :=
  -ζ * y i.val + β * ((d : ℂ) - ζ)

theorem centeredRowLinearForm_eq {n d : ℕ} (S : RowSlice n d) (v : Fin n → ℂ) :
    centeredRowLinearForm S v = rowLinearForm S v - (d : ℂ) / (n : ℂ) * ∑ j, v j := by
  simp only [centeredRowLinearForm, centeredRow, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, rowLinearForm]

theorem centeredRowLinearForm_of_sum_zero {n d : ℕ} (S : RowSlice n d)
    (v : Fin n → ℂ) (hSum : ∑ j, v j = 0) : centeredRowLinearForm S v = rowLinearForm S v := by
  rw [centeredRowLinearForm_eq, hSum, mul_zero, sub_zero]

theorem euclidean_retained_norm_le {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℂ) :
    ‖(WithLp.toLp 2 (fun i : I => v i.val) : EuclideanSpace ℂ I)‖ ≤
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Finset.sum_coe_sort I (fun j => ‖v j‖ ^ 2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun _ _ _ => sq_nonneg _)

theorem retainedShiftedMatrix_zero_sum_norm_bound {n d : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) (B : ℝ)
    (hNorm : RetainedCenteredNormBound I rows B) (v : Fin n → ℂ) (hSum : ∑ j, v j = 0) :
    ‖(WithLp.toLp 2 ((retainedShiftedMatrix I ζ rows).mulVec v) : EuclideanSpace ℂ I)‖ ≤
      (B * Real.sqrt d + ‖ζ‖) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  have hAction : (WithLp.toLp 2 ((retainedShiftedMatrix I ζ rows).mulVec v) : EuclideanSpace ℂ I) =
      WithLp.toLp 2 (fun i : I => centeredRowLinearForm (rows i.val) v) -
        ζ • (WithLp.toLp 2 (fun i : I => v i.val) : EuclideanSpace ℂ I) := by
    apply WithLp.ofLp_injective
    funext i
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, retainedShiftedMatrix_mulVec, centeredRowLinearForm_of_sum_zero _ v hSum]
  rw [hAction]
  apply (norm_sub_le _ _).trans
  rw [norm_smul]
  have hRight := mul_le_mul_of_nonneg_left (euclidean_retained_norm_le I v) (norm_nonneg ζ)
  have h := add_le_add (hNorm v) hRight
  convert h using 1
  ring

theorem canonicalNetShift_kernel_identity {n d : ℕ} (k : ℕ)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) (x : Fin n → ℂ)
    (hKernel : (retainedShiftedMatrix I ζ rows).mulVec x = 0) (β : ℂ) (i : I) :
    rowLinearForm (rows i.val) (fun j => canonicalApprox k (x j)) +
        canonicalNetShift I d ζ (fun j => canonicalApprox k (x j)) β i =
      -(retainedShiftedMatrix I ζ rows).mulVec (centeredCanonicalError k x) i +
        (β - canonicalErrorMean k x) * ((d : ℂ) - ζ) := by
  have hDecomposition : x = fun j => canonicalApprox k (x j) + centeredCanonicalError k x j +
      canonicalErrorMean k x := funext (centeredCanonicalError_decomposition k x)
  have hRow : rowLinearForm (rows i.val) x =
      rowLinearForm (rows i.val) (fun j => canonicalApprox k (x j)) +
        rowLinearForm (rows i.val) (centeredCanonicalError k x) + (d : ℂ) * canonicalErrorMean k x := by
    conv_lhs => rw [hDecomposition]
    rw [rowLinearForm_add_const]
    simp only [rowLinearForm, mul_add, Finset.sum_add_distrib]
  have hK := congrFun hKernel i
  change (retainedShiftedMatrix I ζ rows).mulVec x i = 0 at hK
  rw [retainedShiftedMatrix_mulVec, hRow, centeredCanonicalError_decomposition k x i.val] at hK
  simp only [canonicalNetShift, retainedShiftedMatrix_mulVec]
  linear_combination hK

end CircularLaw
