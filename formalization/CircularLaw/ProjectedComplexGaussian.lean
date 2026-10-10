import CircularLaw.StandardComplexGaussian
import CircularLaw.RetainedRowOrthogonality
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Actual complex Gaussian vectors and their orthogonal projections

The coordinate law is a finite product of the explicitly normalized
standard complex Gaussian measure. The normal is the literal orthogonal
projection onto the complement of a deterministic subspace.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace CircularLaw

def standardComplexGaussianVectorLaw (n : ℕ) : Measure (Fin n → ℂ) :=
  Measure.pi (fun _ => standardComplexGaussianLaw)

instance standardComplexGaussianVectorLaw_probability (n : ℕ) :
    IsProbabilityMeasure (standardComplexGaussianVectorLaw n) := by
  unfold standardComplexGaussianVectorLaw
  infer_instance

theorem standardComplexGaussianVectorLaw_coordinate {n : ℕ} (i : Fin n) :
    (standardComplexGaussianVectorLaw n).map (fun z => z i) = standardComplexGaussianLaw :=
  (measurePreserving_eval (fun _ : Fin n => standardComplexGaussianLaw) i).map_eq

theorem standardComplexGaussianVectorLaw_independent (n : ℕ) :
    iIndepFun (fun i (z : Fin n → ℂ) => z i) (standardComplexGaussianVectorLaw n) :=
  iIndepFun_pi (X := fun _ : Fin n => id) (fun _ => measurable_id.aemeasurable)

theorem standardComplexGaussianVectorLaw_hasGaussianLaw (n : ℕ) :
    HasGaussianLaw id (standardComplexGaussianVectorLaw n) := by
  exact (standardComplexGaussianVectorLaw_independent n).hasGaussianLaw
    (fun i => (show HasLaw (fun z : Fin n → ℂ => z i)
      standardComplexGaussianLaw (standardComplexGaussianVectorLaw n) from
      ⟨(measurable_pi_apply i).aemeasurable, standardComplexGaussianVectorLaw_coordinate i⟩).hasGaussianLaw)

def standardComplexGaussianVector (n : ℕ) (z : Fin n → ℂ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 z

theorem standardComplexGaussianVector_continuous (n : ℕ) :
    Continuous (standardComplexGaussianVector n) :=
  PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)

theorem standardComplexGaussianVector_hasGaussianLaw (n : ℕ) :
    HasGaussianLaw (standardComplexGaussianVector n) (standardComplexGaussianVectorLaw n) :=
  (standardComplexGaussianVectorLaw_hasGaussianLaw n).toLp_pi 2

def projectedComplexGaussian {n : ℕ} (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (z : Fin n → ℂ) : EuclideanSpace ℂ (Fin n) :=
  Eᗮ.starProjection (standardComplexGaussianVector n z)

theorem projectedComplexGaussian_continuous {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : Continuous (projectedComplexGaussian E) := by
  unfold projectedComplexGaussian
  exact (ContinuousLinearMap.continuous (Eᗮ.starProjection :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))).comp
      (standardComplexGaussianVector_continuous n)

theorem projectedComplexGaussian_hasGaussianLaw {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    HasGaussianLaw (projectedComplexGaussian E) (standardComplexGaussianVectorLaw n) :=
  (standardComplexGaussianVector_hasGaussianLaw n).map_fun
    (Eᗮ.starProjection.restrictScalars ℝ)

def projectedComplexGaussianLaw {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : Measure (EuclideanSpace ℂ (Fin n)) :=
  (standardComplexGaussianVectorLaw n).map (projectedComplexGaussian E)

instance projectedComplexGaussianLaw_probability {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    IsProbabilityMeasure (projectedComplexGaussianLaw E) :=
  Measure.isProbabilityMeasure_map (projectedComplexGaussian_continuous E).measurable.aemeasurable

instance projectedComplexGaussianLaw_gaussian {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    IsGaussian (projectedComplexGaussianLaw E) :=
  (projectedComplexGaussian_hasGaussianLaw E).isGaussian_map

theorem projectedComplexGaussian_mem_orthogonal {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (z : Fin n → ℂ) :
    projectedComplexGaussian E z ∈ Eᗮ :=
  Eᗮ.starProjection_apply_mem _

theorem projectedComplexGaussian_norm_le {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (z : Fin n → ℂ) :
    ‖projectedComplexGaussian E z‖ ≤ ‖standardComplexGaussianVector n z‖ := by
  unfold projectedComplexGaussian
  exact Submodule.norm_starProjection_apply_le (𝕜 := ℂ) Eᗮ
    (standardComplexGaussianVector n z)

theorem projectedComplexGaussian_inner {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (x : EuclideanSpace ℂ (Fin n)) (z : Fin n → ℂ) :
    ⟪x, projectedComplexGaussian E z⟫_ℂ =
      ⟪Eᗮ.starProjection x, standardComplexGaussianVector n z⟫_ℂ :=
  (Eᗮ.inner_starProjection_left_eq_right x (standardComplexGaussianVector n z)).symm

theorem projectedComplexGaussian_retained_kernel {n d : ℕ} (I : Finset (Fin n))
    (ζ : ℂ) (rows : RowSliceMatrix n d) (z : Fin n → ℂ) :
    (retainedShiftedMatrix I ζ rows).mulVec
      (WithLp.ofLp (projectedComplexGaussian (retainedRowSpan I ζ rows) z)) = 0 :=
  (retainedRowSpan_orthogonal_iff_kernel I ζ rows _).mp
    (projectedComplexGaussian_mem_orthogonal (retainedRowSpan I ζ rows) z)

end CircularLaw
