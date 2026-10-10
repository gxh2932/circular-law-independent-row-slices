import CircularLaw.GaussianIsometryLaw
import CircularLaw.ComplexGaussianNormLaplace

/-!
# Gaussian norm concentration on an actual deterministic subspace

The squared norm of the orthogonal projection has the standard Gaussian
squared-norm law in the subspace dimension. Its lower small-ball and upper
tail estimates therefore have that dimension, rather than the ambient one.
-/

noncomputable section
open MeasureTheory

namespace CircularLaw

theorem subspaceGaussian_normSq_law {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    (standardComplexGaussianVectorLaw n).map
      (fun z => ‖F.starProjection (standardComplexGaussianVector n z)‖ ^ 2) =
      (standardComplexGaussianVectorLaw (Module.finrank ℂ F)).map
        (fun z => ‖standardComplexGaussianVector (Module.finrank ℂ F) z‖ ^ 2) := by
  have hEq : (fun z => ‖F.starProjection (standardComplexGaussianVector n z)‖ ^ 2) =
      (fun y : EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) => ‖y‖ ^ 2) ∘
        (fun z => subspaceGaussianCoordinateMap F (standardComplexGaussianVector n z)) := by
    funext z
    exact congrArg (fun r : ℝ => r ^ 2) (subspaceGaussianCoordinateMap_norm F _).symm
  rw [hEq, ← Measure.map_map
    (f := fun z => subspaceGaussianCoordinateMap F (standardComplexGaussianVector n z))
    (g := fun y : EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) => ‖y‖ ^ 2) (by fun_prop)
    ((subspaceGaussianCoordinateMap F).continuous.comp
      (standardComplexGaussianVector_continuous n)).measurable,
    subspaceGaussianCoordinateMap_raw_law, standardComplexGaussianEuclideanLaw,
    Measure.map_map (by fun_prop) (standardComplexGaussianVector_continuous _).measurable]
  rfl

theorem subspaceGaussian_normSq_event {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (A : Set ℝ) (hA : MeasurableSet A) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖F.starProjection (standardComplexGaussianVector n z)‖ ^ 2 ∈ A} =
      (standardComplexGaussianVectorLaw (Module.finrank ℂ F)).real
        {z | ‖standardComplexGaussianVector (Module.finrank ℂ F) z‖ ^ 2 ∈ A} := by
  have h1 := map_measureReal_apply (μ := standardComplexGaussianVectorLaw n)
    (show Measurable (fun z => ‖F.starProjection (standardComplexGaussianVector n z)‖ ^ 2) by
      exact ((F.starProjection : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).continuous.comp
        (standardComplexGaussianVector_continuous n)).measurable.norm.pow_const 2) hA
  have h2 := map_measureReal_apply
    (μ := standardComplexGaussianVectorLaw (Module.finrank ℂ F))
    (show Measurable (fun z => ‖standardComplexGaussianVector (Module.finrank ℂ F) z‖ ^ 2) by
      exact (standardComplexGaussianVector_continuous _).measurable.norm.pow_const 2) hA
  rw [subspaceGaussian_normSq_law F] at h1
  exact h1.symm.trans h2

theorem subspaceGaussian_normSq_lower_tail {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {a : ℝ} (ha : 0 ≤ a) (u : ℝ) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖F.starProjection (standardComplexGaussianVector n z)‖ ^ 2 ≤ u} ≤
      ((1 + a)⁻¹) ^ (Module.finrank ℂ F) * Real.exp (a * u) := by
  have h := subspaceGaussian_normSq_event F {r : ℝ | r ≤ u}
    (measurableSet_le measurable_id measurable_const)
  exact h.trans_le (standardComplexGaussianVector_normSq_lower_tail (Module.finrank ℂ F) ha u)

theorem subspaceGaussian_normSq_upper_tail {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (u : ℝ) :
    (standardComplexGaussianVectorLaw n).real
      {z | u ≤ ‖F.starProjection (standardComplexGaussianVector n z)‖ ^ 2} ≤
      ((1 - t)⁻¹) ^ (Module.finrank ℂ F) * Real.exp (-t * u) := by
  have h := subspaceGaussian_normSq_event F {r : ℝ | u ≤ r}
    (measurableSet_le measurable_const measurable_id)
  exact h.trans_le (standardComplexGaussianVector_normSq_upper_tail (Module.finrank ℂ F) ht ht1 u)

theorem subspaceGaussian_normSq_smallBall {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hF : 0 < Module.finrank ℂ F)
    {u : ℝ} (hu : 0 < u) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖F.starProjection (standardComplexGaussianVector n z)‖ ^ 2 ≤ u} ≤
      (Real.exp 1 * u / (Module.finrank ℂ F)) ^ (Module.finrank ℂ F) := by
  have h := subspaceGaussian_normSq_event F {r : ℝ | r ≤ u}
    (measurableSet_le measurable_id measurable_const)
  exact h.trans_le (standardComplexGaussianVector_normSq_smallBall hF hu)

theorem subspaceGaussian_normSq_upper_half_tail {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (u : ℝ) :
    (standardComplexGaussianVectorLaw n).real
      {z | u ≤ ‖F.starProjection (standardComplexGaussianVector n z)‖ ^ 2} ≤
      (2 : ℝ) ^ (Module.finrank ℂ F) * Real.exp (-u / 2) := by
  have h := subspaceGaussian_normSq_event F {r : ℝ | u ≤ r}
    (measurableSet_le measurable_const measurable_id)
  exact h.trans_le (standardComplexGaussianVector_normSq_upper_half_tail (Module.finrank ℂ F) u)

theorem projectedComplexGaussian_normSq_smallBall {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hE : 0 < Module.finrank ℂ Eᗮ)
    {u : ℝ} (hu : 0 < u) :
    (standardComplexGaussianVectorLaw n).real {z | ‖projectedComplexGaussian E z‖ ^ 2 ≤ u} ≤
      (Real.exp 1 * u / (Module.finrank ℂ Eᗮ)) ^ (Module.finrank ℂ Eᗮ) :=
  subspaceGaussian_normSq_smallBall Eᗮ hE hu

theorem projectedComplexGaussian_normSq_upper_half_tail {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (u : ℝ) :
    (standardComplexGaussianVectorLaw n).real {z | u ≤ ‖projectedComplexGaussian E z‖ ^ 2} ≤
      (2 : ℝ) ^ (Module.finrank ℂ Eᗮ) * Real.exp (-u / 2) :=
  subspaceGaussian_normSq_upper_half_tail Eᗮ u

end CircularLaw
