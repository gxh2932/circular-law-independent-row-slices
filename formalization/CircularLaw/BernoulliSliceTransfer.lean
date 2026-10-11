import CircularLaw.BernoulliSliceMassBound
import CircularLaw.RegularizedDistanceMeanComparison

/-!
# The complete square-root-degree loss in Bernoulli-to-slice transfer

Every event transfers from the actual independent Bernoulli cube to the
uniform row slice with factor `4*exp(1)^2*sqrt(d)`. The regularized-distance
tail corollary keeps its Bernoulli concentration bound explicit: the
dimension-free convex concentration theorem remains a separate obligation.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace CircularLaw

theorem bernoulliSlice_event_transfer_sqrt {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (event : (Fin n → Bool) → Prop) :
    uniformProbability (fun s : RowSlice n d => event (rowSliceBoolRow s)) ≤
      4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ) *
        (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
          (rowBernoulliParameter_le_one (by omega) hdn)).real {x | event x} := by
  let p := rowBernoulliParameter n d
  let hp := rowBernoulliParameter_le_one (show 0 < n by omega) hdn
  let μ := bernoulliCubeLaw (Fin n) p hp
  let K := 4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  have hMass : 0 < bernoulliSliceMass n d p := bernoulliSliceMass_pos hd hdn
  have hLower := bernoulliSliceMass_lower hd hdn
  have hOne : 1 ≤ K * bernoulliSliceMass n d p := by
    have h := (div_le_iff₀ hK).mp hLower
    nlinarith
  have hTransfer := bernoulliSlice_event_transfer hdn p hp hMass event
  apply hTransfer.trans
  apply (div_le_iff₀ hMass).mpr
  have hNonneg : 0 ≤ μ.real {x | event x} := measureReal_nonneg
  have hWeighted := mul_le_mul_of_nonneg_left hOne hNonneg
  change μ.real {x | event x} ≤ K * μ.real {x | event x} * bernoulliSliceMass n d p
  nlinarith

def rowSliceEuclideanRow {n d : ℕ} (s : RowSlice n d) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (rowEntry s)

theorem rowSliceEuclideanRow_eq_cube {n d : ℕ} (s : RowSlice n d) :
    rowSliceEuclideanRow s = bernoulliCubeVector (rowSliceBoolRow s) :=
  (bernoulliCubeVector_rowSliceBoolRow s).symm

theorem rowSliceEuclideanRow_norm_le {n d : ℕ} (s : RowSlice n d) :
    ‖rowSliceEuclideanRow s‖ ≤ Real.sqrt (n : ℝ) := by
  rw [rowSliceEuclideanRow_eq_cube]
  simpa only [Fintype.card_fin] using bernoulliCubeVector_norm_le (rowSliceBoolRow s)

theorem rowSliceLaw_event_transfer_sqrt {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (event : EuclideanSpace ℂ (Fin n) → Prop) :
    (rowSliceLaw n d).real {s | event (rowSliceEuclideanRow s)} ≤
      4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ) *
        (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
          (rowBernoulliParameter_le_one (by omega) hdn)).real {x | event (bernoulliCubeVector x)} := by
  have h := bernoulliSlice_event_transfer_sqrt hd hdn (fun x => event (bernoulliCubeVector x))
  simpa only [rowSliceLaw, finiteUniformMeasure_real, rowSliceEuclideanRow_eq_cube] using h

theorem regularizedDistance_slice_bound {n d : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsPositiveMatrixContraction P) (η : ℝ) (u : EuclideanSpace ℂ (Fin n)) (s : RowSlice n d) :
    regularizedDistance P η u (rowSliceEuclideanRow s) ≤
      Real.sqrt (η ^ 2 + (Real.sqrt (n : ℝ) + ‖u‖) ^ 2) :=
  regularizedDistance_le_euclidean_bound hP η u _ (rowSliceEuclideanRow_norm_le s)

theorem regularizedDistance_slice_tail_transfer {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (P : Matrix (Fin n) (Fin n) ℂ) (η : ℝ) (u : EuclideanSpace ℂ (Fin n))
    (center t : ℝ) :
    (rowSliceLaw n d).real {s | t ≤ |regularizedDistance P η u (rowSliceEuclideanRow s) - center|} ≤
      4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ) *
        (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
          (rowBernoulliParameter_le_one (by omega) hdn)).real
            {x | t ≤ |regularizedDistance P η u (bernoulliCubeVector x) - center|} :=
  rowSliceLaw_event_transfer_sqrt hd hdn (fun v => t ≤ |regularizedDistance P η u v - center|)

theorem regularizedDistance_slice_tail_of_bernoulli {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (P : Matrix (Fin n) (Fin n) ℂ) (η : ℝ) (u : EuclideanSpace ℂ (Fin n))
    (center t C c : ℝ)
    (hTail : (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one (by omega) hdn)).real
        {x | t ≤ |regularizedDistance P η u (bernoulliCubeVector x) - center|} ≤ C * Real.exp (-c * t ^ 2)) :
    (rowSliceLaw n d).real {s | t ≤ |regularizedDistance P η u (rowSliceEuclideanRow s) - center|} ≤
      (4 * Real.exp 1 ^ 2 * C) * Real.sqrt (d : ℝ) * Real.exp (-c * t ^ 2) := by
  apply (regularizedDistance_slice_tail_transfer hd hdn P η u center t).trans
  have h := mul_le_mul_of_nonneg_left hTail
    (by positivity : 0 ≤ 4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ))
  convert h using 1
  ring

end CircularLaw
