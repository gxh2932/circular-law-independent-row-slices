import CircularLaw.OrderedNormStability
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Continuity of one-based ordered coordinate norms

The actual order statistic is Lipschitz with constant one in Euclidean
norm. This makes its closed sublevel events measurable, including ties.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem orderedNormAt_euclidean_lipschitz {n : ℕ} (k : ℕ) :
    LipschitzWith 1 (fun x : EuclideanSpace ℂ (Fin n) => orderedNormAt (fun i => x i) k) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hk : 0 < k ∧ k ≤ n
  · have hPert := orderedNormAt_perturbation (fun i => x i) (fun i => y i)
      hk.1 hk.2 ‖y - x‖ (fun i => by
        simpa only [PiLp.sub_apply] using PiLp.norm_apply_le (y - x) i)
    rw [norm_sub_rev] at hPert
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    apply abs_sub_le_iff.mpr
    constructor <;> linarith
  · simp [orderedNormAt, hk]

theorem orderedNormAt_euclidean_continuous {n : ℕ} (k : ℕ) :
    Continuous (fun x : EuclideanSpace ℂ (Fin n) => orderedNormAt (fun i => x i) k) :=
  (orderedNormAt_euclidean_lipschitz k).continuous

theorem orderedNormAt_euclidean_measurable {n : ℕ} (k : ℕ) :
    Measurable (fun x : EuclideanSpace ℂ (Fin n) => orderedNormAt (fun i => x i) k) :=
  (orderedNormAt_euclidean_continuous k).measurable

theorem orderedNormAt_sublevel_isClosed {n : ℕ} (k : ℕ) (τ : ℝ) :
    IsClosed {x : EuclideanSpace ℂ (Fin n) | orderedNormAt (fun i => x i) k ≤ τ} :=
  isClosed_le (orderedNormAt_euclidean_continuous k) continuous_const

theorem orderedNormAt_sublevel_measurableSet {n : ℕ} (k : ℕ) (τ : ℝ) :
    MeasurableSet {x : EuclideanSpace ℂ (Fin n) | orderedNormAt (fun i => x i) k ≤ τ} :=
  (orderedNormAt_sublevel_isClosed k τ).measurableSet

end CircularLaw
