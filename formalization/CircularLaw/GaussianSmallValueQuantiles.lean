import CircularLaw.GaussianIntermediateSingularBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Gaussian lower quantiles at every fixed positive fraction

The singular value at index `n-2*q` is at least `q/(4*n)`, except with
probability at most `n*2^(-q)`. For `q=floor(eta*n)` and `0<eta<1/3`,
this failure probability tends to zero and the quantile is eventually
at least `eta/8`. Every estimate is uniform in the deterministic shift.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem gaussian_normalized_shift_quantile_tail {n q : ℕ} (hq : 0 < q) (hqn : 2 * q < n)
    (z : ℂ) :
    (gaussianSquareMatrixLaw n).real
      {x | ∃ j : Fin n, j.val = n - 2 * q ∧
        orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j < (q : ℝ) / (4 * n)} ≤
      (n : ℝ) * (1 / 2 : ℝ) ^ q := by
  let m := n - q - 1
  have hmn : m < n := by dsimp [m]; omega
  have hk : m + 1 = n - q := by dsimp [m]; omega
  have hCodim : n - m = q + 1 := by dsimp [m]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hkR : (0 : ℝ) < (n - q : ℕ) := by exact_mod_cast (by omega : 0 < n - q)
  have hkLe : (n - q : ℕ) ≤ n := Nat.sub_le _ _
  have hDen : 8 * (n - q : ℕ) * (n : ℝ) ≤ 8 * (n : ℝ) ^ 2 := by
    have hCross := mul_le_mul_of_nonneg_right (by exact_mod_cast hkLe : (n - q : ℕ) ≤ (n : ℝ)) hnR.le
    nlinarith
  have hThreshold : ((q : ℝ) / (4 * n)) ^ 2 ≤
      (q + 1 : ℕ) * (q : ℝ) / (8 * (n - q : ℕ) * n) := by
    calc
      _ = (q : ℝ) ^ 2 / (16 * (n : ℝ) ^ 2) := by ring
      _ ≤ (q : ℝ) ^ 2 / (8 * (n : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
      _ ≤ (q : ℝ) ^ 2 / (8 * (n - q : ℕ) * n) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hDen
      _ ≤ _ := div_le_div_of_nonneg_right (by push_cast; nlinarith) (by positivity)
  have hSubset : {x : GaussianSquareSample n | ∃ j : Fin n, j.val = n - 2 * q ∧
      orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j < (q : ℝ) / (4 * n)} ⊆
      {x | ∃ i : Fin (m + 1),
        orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x)
          (Fin.castLE (Nat.succ_le_of_lt hmn) i) ^ 2 <
            (n - m : ℕ) * ((m + 1 - i.val : ℕ) : ℝ) / (8 * (m + 1 : ℕ) * n)} := by
    rintro x ⟨j, hjVal, hj⟩
    let i : Fin (m + 1) := ⟨j.val, by omega⟩
    have hCast : Fin.castLE (Nat.succ_le_of_lt hmn) i = j := Fin.ext rfl
    have hTail : m + 1 - i.val = q := by dsimp [i]; omega
    refine ⟨i, ?_⟩
    rw [hCast, hTail, hk, hCodim]
    exact ((sq_lt_sq₀ (orderedSquareSingularValues_nonneg _ _) (by positivity)).mpr hj).trans_le hThreshold
  apply ((measureReal_mono (μ := gaussianSquareMatrixLaw n) hSubset).trans
    (gaussian_normalized_shift_intermediate_tail hmn z)).trans
  rw [hk, hCodim]
  exact mul_le_mul (by exact_mod_cast hkLe)
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ q))
    (by positivity) (Nat.cast_nonneg n)

def gaussianQuantileDeletion (eta : ℝ) (n : ℕ) : ℕ := ⌊eta * (n : ℝ)⌋₊

theorem gaussian_quantile_deletion_ratio_tendsto {eta : ℝ} (hEta : 0 ≤ eta) :
    Tendsto (fun n : ℕ => (gaussianQuantileDeletion eta n : ℝ) / n) atTop (𝓝 eta) :=
  (tendsto_nat_floor_mul_div_atTop hEta).comp tendsto_natCast_atTop_atTop

theorem gaussian_quantile_deletion_tendsto {eta : ℝ} (hEta : 0 < eta) :
    Tendsto (gaussianQuantileDeletion eta) atTop atTop := tendsto_nat_floor_mul_atTop eta hEta

theorem gaussian_quantile_geometric_failure_tendsto {eta : ℝ} (hEta : 0 < eta) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ gaussianQuantileDeletion eta n) atTop (𝓝 0) := by
  have hRatio := (gaussian_quantile_deletion_ratio_tendsto hEta.le).inv₀ hEta.ne'
  have hGeom := (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp (gaussian_quantile_deletion_tendsto hEta)
  have hProduct := hRatio.mul hGeom
  simp only [mul_zero] at hProduct
  apply hProduct.congr'
  filter_upwards [(gaussian_quantile_deletion_tendsto hEta).eventually (eventually_gt_atTop 0)] with n hn
  have hq : (gaussianQuantileDeletion eta n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [inv_div, Function.comp_apply]
  field_simp

theorem gaussian_quantile_parameters_eventually {eta : ℝ} (hEta : 0 < eta) (hEtaUpper : eta < 1 / 3) :
    ∀ᶠ n in atTop, 0 < gaussianQuantileDeletion eta n ∧ 2 * gaussianQuantileDeletion eta n < n ∧
      eta / 8 ≤ (gaussianQuantileDeletion eta n : ℝ) / (4 * n) := by
  have hLower := (gaussian_quantile_deletion_ratio_tendsto hEta.le).eventually
    (lt_mem_nhds (by linarith : eta / 2 < eta))
  filter_upwards [hLower, (gaussian_quantile_deletion_tendsto hEta).eventually
    (eventually_gt_atTop 0), eventually_gt_atTop 0] with n hn hq hnPos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hFloor : (gaussianQuantileDeletion eta n : ℝ) ≤ eta * n :=
    Nat.floor_le (by positivity)
  have hTwice : (2 : ℝ) * gaussianQuantileDeletion eta n < n := by nlinarith
  refine ⟨hq, by exact_mod_cast hTwice, ?_⟩
  have hDivide : (gaussianQuantileDeletion eta n : ℝ) / (4 * n) =
      ((gaussianQuantileDeletion eta n : ℝ) / n) / 4 := by ring
  rw [hDivide]
  linarith

def gaussianSmallQuantileBad (eta : ℝ) (z : ℂ) (n : ℕ) : Set (GaussianSquareSample n) :=
  {x | ∃ j : Fin n, j.val = n - 2 * gaussianQuantileDeletion eta n ∧
    orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j < eta / 8}

theorem gaussian_small_quantile_bad_probability_tendsto {eta : ℝ}
    (hEta : 0 < eta) (hEtaUpper : eta < 1 / 3) (z : ℂ) :
    Tendsto (fun n => (gaussianSquareMatrixLaw n).real (gaussianSmallQuantileBad eta z n))
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (gaussian_quantile_geometric_failure_tendsto hEta)
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [gaussian_quantile_parameters_eventually hEta hEtaUpper] with n hn
  apply (measureReal_mono (μ := gaussianSquareMatrixLaw n) (s₂ :=
    {x | ∃ j : Fin n, j.val = n - 2 * gaussianQuantileDeletion eta n ∧
      orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j <
        (gaussianQuantileDeletion eta n : ℝ) / (4 * n)}) ?_).trans
    (gaussian_normalized_shift_quantile_tail hn.1 hn.2.1 z)
  rintro x ⟨j, hj, hSmall⟩
  exact ⟨j, hj, hSmall.trans_le hn.2.2⟩

end CircularLaw
