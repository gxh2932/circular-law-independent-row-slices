import CircularLaw.GaussianOrderSmallBall
import CircularLaw.OrderedNormContinuity
import CircularLaw.GaussianCopiesCombinationLaw

/-!
# Order-statistic small balls for actual Gaussian combinations

Every fixed unit combination has the checked projected Gaussian law.
The closed order-statistic event therefore has the same probability,
and a finite coefficient set costs exactly its cardinality in a union bound.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem projectedGaussianCopiesCombination_unit_orderedNorm_event {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (x : EuclideanSpace ℂ (Fin p)) (hx : ‖x‖ = 1) (k : ℕ) (τ : ℝ) :
    (standardGaussianCopiesLaw n p).real
      {z | orderedNormAt
        (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i) k ≤ τ} =
      (standardComplexGaussianVectorLaw n).real
        {z | orderedNormAt (fun i => projectedComplexGaussian E z i) k ≤ τ} := by
  let A := {y : EuclideanSpace ℂ (Fin n) | orderedNormAt (fun i => y i) k ≤ τ}
  have hA : MeasurableSet A := orderedNormAt_sublevel_measurableSet k τ
  change (standardGaussianCopiesLaw n p).real
    {z | gaussianCopiesCombination (projectedGaussianCopies E z) x ∈ A} = _
  rw [projectedGaussianCopiesCombination_unit_event_real E x hx A hA]
  unfold projectedComplexGaussianLaw
  rw [map_measureReal_apply (projectedComplexGaussian_continuous E).measurable hA]
  rfl

theorem projectedGaussianCopiesCombination_unit_nonflat_smallBall {n p m : ℕ}
    (hn : 0 < n) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hm : m ≤ Module.finrank ℂ Eᗮ) (hLarge : 512 ≤ m)
    (x : EuclideanSpace ℂ (Fin p)) (hx : ‖x‖ = 1) :
    (standardGaussianCopiesLaw n p).real
      {z | orderedNormAt
        (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i) (m / 512) ≤
          (m : ℝ) / (512 * n)} ≤ Real.exp (-(m : ℝ) / 512) := by
  rw [projectedGaussianCopiesCombination_unit_orderedNorm_event E x hx]
  exact projectedComplexGaussian_nonflat_smallBall hn E hm hLarge

theorem projectedGaussianCopiesCombination_finite_unit_nonflat_smallBall {n p m : ℕ}
    (hn : 0 < n) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hm : m ≤ Module.finrank ℂ Eᗮ) (hLarge : 512 ≤ m)
    (S : Finset (EuclideanSpace ℂ (Fin p))) (hS : ∀ x ∈ S, ‖x‖ = 1) :
    (standardGaussianCopiesLaw n p).real
      {z | ∃ x ∈ S, orderedNormAt
        (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i) (m / 512) ≤
          (m : ℝ) / (512 * n)} ≤ (S.card : ℝ) * Real.exp (-(m : ℝ) / 512) := by
  have hUnion : {z | ∃ x ∈ S, orderedNormAt
      (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i) (m / 512) ≤
        (m : ℝ) / (512 * n)} =
      ⋃ x ∈ S, {z | orderedNormAt
        (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i) (m / 512) ≤
          (m : ℝ) / (512 * n)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hUnion]
  apply (measureReal_biUnion_finset_le S _).trans
  calc
    _ ≤ ∑ _x ∈ S, Real.exp (-(m : ℝ) / 512) := Finset.sum_le_sum
      (fun x hx => projectedGaussianCopiesCombination_unit_nonflat_smallBall
        hn E hm hLarge x (hS x hx))
    _ = _ := by simp

end CircularLaw
