import CircularLaw.GaussianInnerLaw
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Standard complex Gaussians in orthonormal coordinates

The adjoint of any complex linear isometric embedding maps the actual
standard Gaussian vector to the standard Gaussian law in the smaller
Euclidean space. This gives independent Gaussian coordinates on every
deterministic subspace, with the existing variance-one-half normalization.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace CircularLaw

def standardComplexGaussianEuclideanLaw (n : ℕ) : Measure (EuclideanSpace ℂ (Fin n)) :=
  (standardComplexGaussianVectorLaw n).map (standardComplexGaussianVector n)

instance standardComplexGaussianEuclideanLaw_probability (n : ℕ) :
    IsProbabilityMeasure (standardComplexGaussianEuclideanLaw n) :=
  Measure.isProbabilityMeasure_map (standardComplexGaussianVector_continuous n).measurable.aemeasurable

theorem standardComplexGaussianLaw_charFun (t : ℂ) :
    charFun standardComplexGaussianLaw t = Complex.exp (-((‖t‖ ^ 2 / 4 : ℝ) : ℂ)) := by
  rw [charFun_eq_charFunDual_toDualMap, standardComplexGaussianLaw_charFunDual]
  congr 3
  rw [← Complex.normSq_eq_norm_sq]
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.normSq_apply, pow_two]

theorem standardComplexGaussianEuclideanLaw_charFun {n : ℕ}
    (t : EuclideanSpace ℂ (Fin n)) :
    charFun (standardComplexGaussianEuclideanLaw n) t =
      Complex.exp (-((‖t‖ ^ 2 / 4 : ℝ) : ℂ)) := by
  rw [standardComplexGaussianEuclideanLaw, standardComplexGaussianVectorLaw]
  change charFun ((Measure.pi (fun _ : Fin n => standardComplexGaussianLaw)).map
    (WithLp.toLp 2)) t = _
  rw [charFun_pi]
  simp only [standardComplexGaussianLaw_charFun]
  rw [← Complex.exp_sum, Finset.sum_neg_distrib, ← Complex.ofReal_sum, ← Finset.sum_div,
    EuclideanSpace.norm_sq_eq]

theorem complexEuclidean_real_inner {n : ℕ} (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp only [PiLp.inner_apply, real_inner_eq_re_inner ℂ, Complex.re_sum]
  rfl

theorem complexIsometryAdjoint_charFun {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (t : EuclideanSpace ℂ (Fin m)) :
    charFun ((standardComplexGaussianEuclideanLaw n).map
      (ContinuousLinearMap.adjoint U.toContinuousLinearMap)) t =
      charFun (standardComplexGaussianEuclideanLaw n) (U t) := by
  rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [complexEuclidean_real_inner, complexEuclidean_real_inner,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem complexIsometryAdjoint_standardGaussian_law {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    (standardComplexGaussianEuclideanLaw n).map
      (ContinuousLinearMap.adjoint U.toContinuousLinearMap) =
        standardComplexGaussianEuclideanLaw m := by
  haveI : IsProbabilityMeasure ((standardComplexGaussianEuclideanLaw n).map
      (ContinuousLinearMap.adjoint U.toContinuousLinearMap)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFun
  funext t
  rw [complexIsometryAdjoint_charFun, standardComplexGaussianEuclideanLaw_charFun,
    standardComplexGaussianEuclideanLaw_charFun, U.norm_map]

def subspaceGaussianIsometry {n : ℕ} (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) :=
  F.subtypeₗᵢ.comp (stdOrthonormalBasis ℂ F).repr.symm.toLinearIsometry

def subspaceGaussianCoordinateMap {n : ℕ} (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) :=
  (stdOrthonormalBasis ℂ F).repr.toContinuousLinearMap.comp F.orthogonalProjection

theorem subspaceGaussianCoordinateMap_eq_adjoint {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    subspaceGaussianCoordinateMap F =
      ContinuousLinearMap.adjoint (subspaceGaussianIsometry F).toContinuousLinearMap := by
  letI : InnerProductSpace ℂ (EuclideanSpace ℂ (Fin n)) :=
    PiLp.innerProductSpace (fun _ : Fin n => ℂ)
  letI : InnerProductSpace ℂ F := Submodule.innerProductSpace F
  let b := stdOrthonormalBasis ℂ F
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_right ℂ
  intro t
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪b.repr (F.orthogonalProjection y), t⟫_ℂ = ⟪y, (b.repr.symm t : EuclideanSpace ℂ (Fin n))⟫_ℂ
  let pY : F := (F.orthogonalProjection : EuclideanSpace ℂ (Fin n) →L[ℂ] F) y
  have hInner : ⟪b.repr pY, b.repr (b.repr.symm t)⟫_ℂ = ⟪pY, b.repr.symm t⟫_ℂ :=
    LinearIsometryEquiv.inner_map_map (𝕜 := ℂ) b.repr pY (b.repr.symm t)
  rw [b.repr.apply_symm_apply] at hInner
  rw [hInner]
  change ⟪F.starProjection y, (b.repr.symm t : EuclideanSpace ℂ (Fin n))⟫_ℂ = _
  rw [F.inner_starProjection_left_eq_right,
    F.starProjection_eq_self_iff.mpr (b.repr.symm t).property]

theorem subspaceGaussianCoordinateMap_norm {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (y : EuclideanSpace ℂ (Fin n)) :
    ‖subspaceGaussianCoordinateMap F y‖ = ‖F.starProjection y‖ := by
  change ‖(stdOrthonormalBasis ℂ F).repr (F.orthogonalProjection y)‖ = _
  rw [LinearIsometryEquiv.norm_map]
  rfl

theorem subspaceGaussianCoordinateMap_law {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    (standardComplexGaussianEuclideanLaw n).map (subspaceGaussianCoordinateMap F) =
      standardComplexGaussianEuclideanLaw (Module.finrank ℂ F) := by
  rw [subspaceGaussianCoordinateMap_eq_adjoint]
  exact complexIsometryAdjoint_standardGaussian_law (subspaceGaussianIsometry F)

theorem subspaceGaussianCoordinateMap_raw_law {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    (standardComplexGaussianVectorLaw n).map
      (fun z => subspaceGaussianCoordinateMap F (standardComplexGaussianVector n z)) =
      standardComplexGaussianEuclideanLaw (Module.finrank ℂ F) := by
  change (standardComplexGaussianVectorLaw n).map
    (subspaceGaussianCoordinateMap F ∘ standardComplexGaussianVector n) = _
  rw [← Measure.map_map (subspaceGaussianCoordinateMap F).measurable
    (standardComplexGaussianVector_continuous n).measurable]
  exact subspaceGaussianCoordinateMap_law F

end CircularLaw
