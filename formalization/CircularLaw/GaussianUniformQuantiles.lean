import CircularLaw.GaussianSmallValueQuantiles
import Mathlib.Data.Nat.Sqrt

/-!
# Simultaneous Gaussian lower quantiles above sqrt(n)

A finite union controls every intermediate quantile with deletion
parameter at least sqrt(n). The resulting failure bound n^2*2^(-sqrt(n))
tends to zero. Outside this event, every rank r>2*sqrt(n) has singular
value at least r/(16*n), uniformly in the deterministic complex shift.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology BigOperators

namespace CircularLaw

def gaussianUniformQuantileBad (z : ℂ) (n : ℕ) : Set (GaussianSquareSample n) :=
  {x | ∃ q : Fin n, Nat.sqrt n ≤ q.val ∧ 0 < q.val ∧ 2 * q.val < n ∧
    ∃ j : Fin n, j.val = n - 2 * q.val ∧
      orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j < (q.val : ℝ) / (4 * n)}

theorem gaussian_uniform_quantile_probability_bound (z : ℂ) (n : ℕ) :
    (gaussianSquareMatrixLaw n).real (gaussianUniformQuantileBad z n) ≤
      (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ Nat.sqrt n := by
  let A : Fin n → Set (GaussianSquareSample n) := fun q =>
    {x | Nat.sqrt n ≤ q.val ∧ 0 < q.val ∧ 2 * q.val < n ∧
      ∃ j : Fin n, j.val = n - 2 * q.val ∧
        orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j < (q.val : ℝ) / (4 * n)}
  have hEach (q : Fin n) : (gaussianSquareMatrixLaw n).real (A q) ≤
      (n : ℝ) * (1 / 2 : ℝ) ^ Nat.sqrt n := by
    by_cases hq : Nat.sqrt n ≤ q.val ∧ 0 < q.val ∧ 2 * q.val < n
    · have hSubset : A q ⊆ {x | ∃ j : Fin n, j.val = n - 2 * q.val ∧
          orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j < (q.val : ℝ) / (4 * n)} :=
        fun _ h => h.2.2.2
      exact ((measureReal_mono (μ := gaussianSquareMatrixLaw n) hSubset).trans
        (gaussian_normalized_shift_quantile_tail hq.2.1 hq.2.2 z)).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) hq.1) (Nat.cast_nonneg _))
    · have hEmpty : A q = ∅ := by
        ext x
        simp only [A, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hq ⟨h.1, h.2.1, h.2.2.1⟩
      rw [hEmpty, measureReal_empty]
      positivity
  have hEq : gaussianUniformQuantileBad z n = ⋃ q ∈ (Finset.univ : Finset (Fin n)), A q := by
    ext x
    simp only [gaussianUniformQuantileBad, Set.mem_setOf_eq, Set.mem_iUnion,
      Finset.mem_univ, exists_true_left, A]
  rw [hEq]
  calc
    _ ≤ ∑ q : Fin n, (gaussianSquareMatrixLaw n).real (A q) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _q : Fin n, (n : ℝ) * (1 / 2 : ℝ) ^ Nat.sqrt n := Finset.sum_le_sum (fun q _ => hEach q)
    _ = _ := by simp; ring

theorem natural_sqrt_tendsto : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with n hn
  exact Nat.le_sqrt.mpr hn

theorem gaussian_uniform_quantile_failure_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ Nat.sqrt n) atTop (𝓝 0) := by
  have hPoly := (tendsto_pow_const_mul_const_pow_of_lt_one 4
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp natural_sqrt_tendsto
  have hLimit := hPoly.const_mul 16
  simp only [mul_zero] at hLimit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
    (Eventually.of_forall (fun _ => by positivity))
  filter_upwards [natural_sqrt_tendsto.eventually (eventually_ge_atTop 1)] with n hn
  have hN : (n : ℝ) ≤ 4 * (Nat.sqrt n : ℝ) ^ 2 := by
    have hRaw := Nat.lt_succ_sqrt' n
    have hUpper : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by exact_mod_cast hRaw
    have hOne : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hn
    nlinarith
  have hSquare : (n : ℝ) ^ 2 ≤ 16 * (Nat.sqrt n : ℝ) ^ 4 := by
    nlinarith [sq_nonneg (4 * (Nat.sqrt n : ℝ) ^ 2 - n)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hSquare
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Nat.sqrt n)

theorem gaussian_uniform_quantile_bad_probability_tendsto (z : ℂ) :
    Tendsto (fun n => (gaussianSquareMatrixLaw n).real (gaussianUniformQuantileBad z n))
      atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds gaussian_uniform_quantile_failure_tendsto
    (Eventually.of_forall (fun _ => measureReal_nonneg))
    (Eventually.of_forall (gaussian_uniform_quantile_probability_bound z))

theorem gaussian_good_uniform_quantile_rank_lower {n : ℕ} (hn : 2 ≤ Nat.sqrt n)
    (z : ℂ) (x : GaussianSquareSample n) (hGood : x ∉ gaussianUniformQuantileBad z n)
    (j : Fin n) (hRank : 2 * Nat.sqrt n < n - j.val) :
    ((n - j.val : ℕ) : ℝ) / (16 * n) ≤
      orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j := by
  let r := n - j.val
  let q := (r - 1) / 2
  have hrn : r ≤ n := Nat.sub_le _ _
  have hq0 : Nat.sqrt n ≤ q := by dsimp [q, r]; omega
  have hqPos : 0 < q := by omega
  have hqn : 2 * q < n := by dsimp [q]; omega
  let qFin : Fin n := ⟨q, by omega⟩
  let i : Fin n := ⟨n - 2 * q, by omega⟩
  have hLower : (q : ℝ) / (4 * n) ≤
      orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) i := by
    apply le_of_not_gt
    intro h
    exact hGood ⟨qFin, hq0, hqPos, hqn, i, rfl, h⟩
  have hIndex : j ≤ i := by change j.val ≤ n - 2 * q; dsimp [q, r]; omega
  have hRankScale : (r : ℝ) ≤ 4 * q := by
    have hRN : r ≤ 4 * q := by dsimp [q]; omega
    exact_mod_cast hRN
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hFraction : (r : ℝ) / (16 * n) ≤ (q : ℝ) / (4 * n) := by
    have h := div_le_div_of_nonneg_right hRankScale hnR.le
    convert (div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 16)) using 1 <;> ring
  exact hFraction.trans (hLower.trans
    (orderedSquareSingularValues_antitone (normalizedShiftedGaussianMatrix z x) hIndex))

end CircularLaw
