import CircularLaw.GaussianProjectionNorm
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Gaussian small-ball reduction after deleting coordinates

The normal vectors that vanish on a deleted set form an actual subspace
whose dimension loses at most the size of that set. Projection onto this
subspace is controlled by the remaining coordinates of the actual normal.
The previously checked Gaussian norm law then supplies its small-ball bound.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped BigOperators InnerProductSpace

namespace CircularLaw

def gaussianDeletedCoordinateMap {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n)) :
    Eᗮ →ₗ[ℂ] (K → ℂ) :=
  LinearMap.pi (fun j =>
    (PiLp.projₗ (𝕜 := ℂ) (β := fun _ : Fin n => ℂ) 2 j).comp Eᗮ.subtype)

theorem gaussianDeletedCoordinateMap_apply {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n))
    (x : Eᗮ) (j : K) : gaussianDeletedCoordinateMap E K x j = (x : EuclideanSpace ℂ (Fin n)) j :=
  rfl

def gaussianDeletedCoordinateSubspace {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  (LinearMap.ker (gaussianDeletedCoordinateMap E K)).map Eᗮ.subtype

theorem gaussianDeletedCoordinateSubspace_mem {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n))
    (x : EuclideanSpace ℂ (Fin n)) :
    x ∈ gaussianDeletedCoordinateSubspace E K ↔ x ∈ Eᗮ ∧ ∀ j ∈ K, x j = 0 := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.property, ?_⟩
    intro j hj
    have h := congrFun (LinearMap.mem_ker.mp hv) (⟨j, hj⟩ : K)
    exact h
  · rintro ⟨hx, hZero⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext j
    exact hZero j j.property

theorem gaussianDeletedCoordinateSubspace_le {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n)) :
    gaussianDeletedCoordinateSubspace E K ≤ Eᗮ := by
  intro x hx
  exact ((gaussianDeletedCoordinateSubspace_mem E K x).mp hx).1

theorem gaussianDeletedCoordinateSubspace_dimension {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n)) :
    Module.finrank ℂ Eᗮ ≤ Module.finrank ℂ (gaussianDeletedCoordinateSubspace E K) + K.card := by
  rw [gaussianDeletedCoordinateSubspace, Submodule.finrank_map_subtype_eq]
  have hRank := (gaussianDeletedCoordinateMap E K).finrank_range_add_finrank_ker
  have hRange : Module.finrank ℂ (LinearMap.range (gaussianDeletedCoordinateMap E K)) ≤ K.card := by
    simpa using (LinearMap.range (gaussianDeletedCoordinateMap E K)).finrank_le
  omega

def gaussianEraseCoordinates {n : ℕ} (K : Finset (Fin n)) (y : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun i => if i ∈ K then 0 else y i)

theorem gaussianEraseCoordinates_apply {n : ℕ} (K : Finset (Fin n))
    (y : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    gaussianEraseCoordinates K y i = if i ∈ K then 0 else y i := rfl

theorem gaussianEraseCoordinates_inner {n : ℕ} (K : Finset (Fin n))
    (y w : EuclideanSpace ℂ (Fin n)) (hZero : ∀ i ∈ K, w i = 0) :
    ⟪gaussianEraseCoordinates K y, w⟫_ℂ = ⟪y, w⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ K
  · simp only [gaussianEraseCoordinates_apply, if_pos hi, hZero i hi, inner_zero_right]
  · simp only [gaussianEraseCoordinates_apply, if_neg hi]

theorem gaussianEraseCoordinates_projection {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n))
    (hZero : ∀ w ∈ F, ∀ i ∈ K, w i = 0) (y : EuclideanSpace ℂ (Fin n)) :
    F.starProjection (gaussianEraseCoordinates K y) = F.starProjection y := by
  letI : InnerProductSpace ℂ (EuclideanSpace ℂ (Fin n)) :=
    PiLp.innerProductSpace (fun _ : Fin n => ℂ)
  apply ext_inner_right ℂ
  intro v
  rw [F.inner_starProjection_left_eq_right, F.inner_starProjection_left_eq_right]
  exact gaussianEraseCoordinates_inner K y _
    (hZero _ (F.starProjection_apply_mem v))

theorem gaussianDeletedCoordinateProjection_norm_le {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n)) (z : Fin n → ℂ) :
    ‖(gaussianDeletedCoordinateSubspace E K).starProjection (standardComplexGaussianVector n z)‖ ≤
      ‖gaussianEraseCoordinates K (projectedComplexGaussian E z)‖ := by
  let F := gaussianDeletedCoordinateSubspace E K
  have hComp := Submodule.starProjection_comp_starProjection_of_le (𝕜 := ℂ)
    (gaussianDeletedCoordinateSubspace_le E K)
  have hNest := congrArg (fun T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) =>
    T (standardComplexGaussianVector n z)) hComp
  have hZero : ∀ w ∈ F, ∀ i ∈ K, w i = 0 := by
    intro w hw
    exact ((gaussianDeletedCoordinateSubspace_mem E K w).mp hw).2
  calc
    _ = ‖F.starProjection (projectedComplexGaussian E z)‖ := congrArg norm hNest.symm
    _ = ‖F.starProjection (gaussianEraseCoordinates K (projectedComplexGaussian E z))‖ :=
      congrArg norm (gaussianEraseCoordinates_projection F K hZero _).symm
    _ ≤ _ := Submodule.norm_starProjection_apply_le (𝕜 := ℂ) F _

theorem gaussianEraseCoordinates_normSq_bound {n : ℕ} (K : Finset (Fin n))
    (y : EuclideanSpace ℂ (Fin n)) {τ : ℝ} (hτ : 0 ≤ τ)
    (hSmall : ∀ i ∉ K, ‖y i‖ ≤ τ) :
    ‖gaussianEraseCoordinates K y‖ ^ 2 ≤ (n : ℝ) * τ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin n, τ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [gaussianEraseCoordinates_apply]
      by_cases hi : i ∈ K
      · simp only [if_pos hi, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        exact sq_nonneg τ
      · rw [if_neg hi]
        exact (sq_le_sq₀ (norm_nonneg _) hτ).mpr (hSmall i hi)
    _ = _ := by simp

theorem gaussianDeletedCoordinates_smallBall {n : ℕ} (hn : 0 < n)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n))
    (hK : K.card < Module.finrank ℂ Eᗮ) {τ : ℝ} (hτ : 0 < τ) :
    (standardComplexGaussianVectorLaw n).real
      {z | ∀ i ∉ K, ‖projectedComplexGaussian E z i‖ ≤ τ} ≤
      (Real.exp 1 * ((n : ℝ) * τ ^ 2) /
        (Module.finrank ℂ (gaussianDeletedCoordinateSubspace E K))) ^
          (Module.finrank ℂ (gaussianDeletedCoordinateSubspace E K)) := by
  have hDim := gaussianDeletedCoordinateSubspace_dimension E K
  have hF : 0 < Module.finrank ℂ (gaussianDeletedCoordinateSubspace E K) := by omega
  have hu : 0 < (n : ℝ) * τ ^ 2 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hSubset : {z | ∀ i ∉ K, ‖projectedComplexGaussian E z i‖ ≤ τ} ⊆
      {z | ‖(gaussianDeletedCoordinateSubspace E K).starProjection
        (standardComplexGaussianVector n z)‖ ^ 2 ≤ (n : ℝ) * τ ^ 2} := by
    intro z hz
    exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (gaussianDeletedCoordinateProjection_norm_le E K z)).trans
        (gaussianEraseCoordinates_normSq_bound K _ hτ.le hz)
  exact (measureReal_mono hSubset).trans
    (subspaceGaussian_normSq_smallBall (gaussianDeletedCoordinateSubspace E K) hF hu)

end CircularLaw
