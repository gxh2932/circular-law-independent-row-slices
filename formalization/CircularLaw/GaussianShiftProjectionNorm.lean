import CircularLaw.GaussianShiftNormLaplace
import CircularLaw.GaussianProjectionNorm

/-!
# Shifted Gaussian small-ball estimates on every deterministic subspace

The actual subspace coordinate law transports the shifted projection
norm to a shifted standard Gaussian in the subspace dimension. The exact
shifted lower Laplace estimate therefore gives a bound uniform over both
the deterministic shift and the subspace.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem subspaceGaussian_shift_normSq_law {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (w : EuclideanSpace ℂ (Fin n)) :
    (standardComplexGaussianVectorLaw n).map
      (fun z => ‖F.starProjection (standardComplexGaussianVector n z + w)‖ ^ 2) =
      (standardComplexGaussianVectorLaw (Module.finrank ℂ F)).map
        (fun z => ‖standardComplexGaussianVector (Module.finrank ℂ F) z +
          subspaceGaussianCoordinateMap F w‖ ^ 2) := by
  have hEq : (fun z => ‖F.starProjection (standardComplexGaussianVector n z + w)‖ ^ 2) =
      (fun y : EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) =>
        ‖y + subspaceGaussianCoordinateMap F w‖ ^ 2) ∘
          (fun z => subspaceGaussianCoordinateMap F (standardComplexGaussianVector n z)) := by
    funext z
    rw [← subspaceGaussianCoordinateMap_norm]
    simp only [ContinuousLinearMap.map_add, Function.comp_apply]
  rw [hEq, ← Measure.map_map
    (f := fun z => subspaceGaussianCoordinateMap F (standardComplexGaussianVector n z))
    (g := fun y : EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) =>
      ‖y + subspaceGaussianCoordinateMap F w‖ ^ 2) (by fun_prop)
    ((subspaceGaussianCoordinateMap F).continuous.comp
      (standardComplexGaussianVector_continuous n)).measurable,
    subspaceGaussianCoordinateMap_raw_law, standardComplexGaussianEuclideanLaw,
    Measure.map_map (by fun_prop) (standardComplexGaussianVector_continuous _).measurable]
  rfl

theorem subspaceGaussian_shift_normSq_event {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (w : EuclideanSpace ℂ (Fin n))
    (A : Set ℝ) (hA : MeasurableSet A) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖F.starProjection (standardComplexGaussianVector n z + w)‖ ^ 2 ∈ A} =
      (standardComplexGaussianVectorLaw (Module.finrank ℂ F)).real
        {z | ‖standardComplexGaussianVector (Module.finrank ℂ F) z +
          subspaceGaussianCoordinateMap F w‖ ^ 2 ∈ A} := by
  have h1 := map_measureReal_apply (μ := standardComplexGaussianVectorLaw n)
    (show Measurable (fun z => ‖F.starProjection (standardComplexGaussianVector n z + w)‖ ^ 2) by
      exact ((F.starProjection : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).continuous.comp
        ((standardComplexGaussianVector_continuous n).add continuous_const)).measurable.norm.pow_const 2) hA
  have h2 := map_measureReal_apply
    (μ := standardComplexGaussianVectorLaw (Module.finrank ℂ F))
    (show Measurable (fun z => ‖standardComplexGaussianVector (Module.finrank ℂ F) z +
        subspaceGaussianCoordinateMap F w‖ ^ 2) by
      exact ((standardComplexGaussianVector_continuous _).add continuous_const).measurable.norm.pow_const 2) hA
  rw [subspaceGaussian_shift_normSq_law F w] at h1
  exact h1.symm.trans h2

theorem subspaceGaussian_shift_normSq_lower_tail {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (w : EuclideanSpace ℂ (Fin n))
    {a : ℝ} (ha : 0 ≤ a) (u : ℝ) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖F.starProjection (standardComplexGaussianVector n z + w)‖ ^ 2 ≤ u} ≤
        ((1 + a)⁻¹) ^ (Module.finrank ℂ F) * Real.exp (a * u) := by
  have h := subspaceGaussian_shift_normSq_event F w {r : ℝ | r ≤ u}
    (measurableSet_le measurable_id measurable_const)
  exact h.trans_le (standardComplexGaussianVector_shift_normSq_lower_tail
    (subspaceGaussianCoordinateMap F w) ha u)

theorem subspaceGaussian_shift_normSq_smallBall {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hF : 0 < Module.finrank ℂ F)
    (w : EuclideanSpace ℂ (Fin n)) {u : ℝ} (hu : 0 < u) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖F.starProjection (standardComplexGaussianVector n z + w)‖ ^ 2 ≤ u} ≤
        (Real.exp 1 * u / (Module.finrank ℂ F)) ^ (Module.finrank ℂ F) := by
  have h := subspaceGaussian_shift_normSq_event F w {r : ℝ | r ≤ u}
    (measurableSet_le measurable_id measurable_const)
  exact h.trans_le (standardComplexGaussianVector_shift_normSq_smallBall hF
    (subspaceGaussianCoordinateMap F w) hu)

theorem subspaceGaussian_shift_normSq_lower_eighth_tail {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hF : 0 < Module.finrank ℂ F)
    (w : EuclideanSpace ℂ (Fin n)) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖F.starProjection (standardComplexGaussianVector n z + w)‖ ^ 2 ≤
        (Module.finrank ℂ F : ℝ) / 8} ≤ (1 / 2 : ℝ) ^ (Module.finrank ℂ F) := by
  have hRank : (0 : ℝ) < Module.finrank ℂ F := by exact_mod_cast hF
  apply (subspaceGaussian_shift_normSq_smallBall F hF w (by positivity :
    0 < (Module.finrank ℂ F : ℝ) / 8)).trans
  apply pow_le_pow_left₀ (by positivity)
  have hEq : Real.exp 1 * ((Module.finrank ℂ F : ℝ) / 8) / Module.finrank ℂ F = Real.exp 1 / 8 := by
    field_simp
  rw [hEq]
  linarith [Real.exp_one_lt_three]

theorem projectedComplexGaussian_shift_normSq_smallBall {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hE : 0 < Module.finrank ℂ Eᗮ)
    (w : EuclideanSpace ℂ (Fin n)) {u : ℝ} (hu : 0 < u) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖Eᗮ.starProjection (standardComplexGaussianVector n z + w)‖ ^ 2 ≤ u} ≤
        (Real.exp 1 * u / (Module.finrank ℂ Eᗮ)) ^ (Module.finrank ℂ Eᗮ) :=
  subspaceGaussian_shift_normSq_smallBall Eᗮ hE w hu

end CircularLaw
