import CircularLaw.PositiveContractionGeometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.Fintype.BigOperators

/-!
# The actual regularized distance is convex and one-Lipschitz

The source function is `sqrt(eta^2 + <P(x+u),x+u>)`. An added constant
coordinate `eta`, followed by the square-root matrix action, realizes it
as a Euclidean norm. Its affine geometry proves convexity, and the
square-root contraction proves the required dimension-free Lipschitz
constant. All vector norms here are Euclidean.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace CircularLaw

section Geometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def regularizedDistance (P : Matrix ι ι ℂ) (η : ℝ) (u x : EuclideanSpace ℂ ι) : ℝ :=
  Real.sqrt (η ^ 2 + matrixEuclideanQuadratic P (x + u))

def augmentedRegularizedVector (P : Matrix ι ι ℂ) (η : ℝ) (u x : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (Option ι) :=
  WithLp.toLp 2 (fun o => o.elim (η : ℂ) (fun i => (CFC.sqrt P).toEuclideanLin (x + u) i))

theorem augmentedRegularizedVector_norm_sq (P : Matrix ι ι ℂ) (η : ℝ)
    (u x : EuclideanSpace ℂ ι) :
    ‖augmentedRegularizedVector P η u x‖ ^ 2 = η ^ 2 + ‖(CFC.sqrt P).toEuclideanLin (x + u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_option]
  simp only [augmentedRegularizedVector, PiLp.toLp_apply, Option.elim_none, Option.elim_some,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem regularizedDistance_eq_augmented_norm {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (η : ℝ) (u x : EuclideanSpace ℂ ι) :
    regularizedDistance P η u x = ‖augmentedRegularizedVector P η u x‖ := by
  rw [regularizedDistance, ← matrix_squareRoot_norm_sq hP,
    ← augmentedRegularizedVector_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem augmentedRegularizedVector_sub (P : Matrix ι ι ℂ) (η : ℝ)
    (u x y : EuclideanSpace ℂ ι) :
    augmentedRegularizedVector P η u x - augmentedRegularizedVector P η u y =
      augmentedRegularizedVector P 0 0 (x - y) := by
  ext o
  cases o with
  | none => simp [augmentedRegularizedVector]
  | some i =>
    change (CFC.sqrt P).toEuclideanLin (x + u) i - (CFC.sqrt P).toEuclideanLin (y + u) i =
      (CFC.sqrt P).toEuclideanLin ((x - y) + 0) i
    have h := congrArg (fun v : EuclideanSpace ℂ ι => v i)
      ((CFC.sqrt P).toEuclideanLin.map_sub (x + u) (y + u))
    simpa only [add_sub_add_right_eq_sub, PiLp.sub_apply, add_zero] using h.symm

theorem augmentedRegularizedVector_sub_norm (P : Matrix ι ι ℂ) (η : ℝ)
    (u x y : EuclideanSpace ℂ ι) :
    ‖augmentedRegularizedVector P η u x - augmentedRegularizedVector P η u y‖ =
      ‖(CFC.sqrt P).toEuclideanLin (x - y)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [augmentedRegularizedVector_sub, augmentedRegularizedVector_norm_sq]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_add, add_zero]

theorem regularizedDistance_lipschitz {P : Matrix ι ι ℂ} (hP : IsPositiveMatrixContraction P)
    (η : ℝ) (u : EuclideanSpace ℂ ι) : LipschitzWith 1 (regularizedDistance P η u) := by
  apply LipschitzWith.mk_one
  intro x y
  rw [regularizedDistance_eq_augmented_norm hP.1, regularizedDistance_eq_augmented_norm hP.1,
    Real.dist_eq]
  exact (abs_norm_sub_norm_le _ _).trans (by
    rw [augmentedRegularizedVector_sub_norm, dist_eq_norm]
    exact positiveContraction_squareRoot_norm_le hP (x - y))

theorem augmentedRegularizedVector_convex_combination (P : Matrix ι ι ℂ) (η : ℝ)
    (u x y : EuclideanSpace ℂ ι) {a b : ℝ} (hab : a + b = 1) :
    augmentedRegularizedVector P η u (a • x + b • y) =
      a • augmentedRegularizedVector P η u x + b • augmentedRegularizedVector P η u y := by
  have hU : a • u + b • u = u := by rw [← add_smul, hab, one_smul]
  have hArgument : (a • x + b • y) + u = a • (x + u) + b • (y + u) := by
    rw [smul_add, smul_add]
    calc
      _ = (a • x + b • y) + (a • u + b • u) := by rw [hU]
      _ = _ := by abel
  ext o
  cases o with
  | none =>
    change (η : ℂ) = a • (η : ℂ) + b • (η : ℂ)
    rw [← add_smul, hab, one_smul]
  | some i =>
    let L := (CFC.sqrt P).toEuclideanLin.restrictScalars ℝ
    change L ((a • x + b • y) + u) i = a • L (x + u) i + b • L (y + u) i
    rw [hArgument, L.map_add, L.map_smul, L.map_smul]
    rfl

theorem regularizedDistance_convex {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (η : ℝ) (u : EuclideanSpace ℂ ι) : ConvexOn ℝ Set.univ (regularizedDistance P η u) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  rw [regularizedDistance_eq_augmented_norm hP, regularizedDistance_eq_augmented_norm hP,
    regularizedDistance_eq_augmented_norm hP, augmentedRegularizedVector_convex_combination P η u x y hab]
  apply (norm_add_le _ _).trans_eq
  rw [norm_smul_of_nonneg ha, norm_smul_of_nonneg hb]
  rfl

theorem regularizedDistance_sq {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (η : ℝ) (u x : EuclideanSpace ℂ ι) :
    regularizedDistance P η u x ^ 2 = η ^ 2 + matrixEuclideanQuadratic P (x + u) :=
  Real.sq_sqrt (add_nonneg (sq_nonneg η) (matrixEuclideanQuadratic_nonneg hP _))

theorem regularizedDistance_nonneg (P : Matrix ι ι ℂ) (η : ℝ) (u x : EuclideanSpace ℂ ι) :
    0 ≤ regularizedDistance P η u x := Real.sqrt_nonneg _

theorem regularizedDistance_ge_eta {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (η : ℝ) (u x : EuclideanSpace ℂ ι) : η ≤ regularizedDistance P η u x := by
  have hSq := regularizedDistance_sq hP η u x
  have hPos := regularizedDistance_nonneg P η u x
  have hQuad := matrixEuclideanQuadratic_nonneg hP (x + u)
  nlinarith

theorem regularizedDistance_le_euclidean_bound {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (η : ℝ) (u x : EuclideanSpace ℂ ι)
    {R : ℝ} (hNorm : ‖x‖ ≤ R) :
    regularizedDistance P η u x ≤ Real.sqrt (η ^ 2 + (R + ‖u‖) ^ 2) := by
  apply Real.sqrt_le_sqrt
  apply add_le_add_right
  apply (positiveContraction_quadratic_le_norm_sq hP (x + u)).trans
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le x u).trans (add_le_add_left hNorm ‖u‖)) 2

end Geometry

end CircularLaw
