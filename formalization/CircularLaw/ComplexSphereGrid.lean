import CircularLaw.GridBox
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# Explicit finite grids on the complex Euclidean unit sphere

Round each coordinate into the actual canonical grid box, omit zero,
and normalize. Coordinate rounding and the reverse triangle inequality
give a sphere cover; its cardinality is bounded by the counted grid box.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators

namespace CircularLaw

def complexUnitNormalize {p : ℕ} (x : EuclideanSpace ℂ (Fin p)) :
    EuclideanSpace ℂ (Fin p) := (‖x‖⁻¹ : ℝ) • x

theorem complexUnitNormalize_norm {p : ℕ} (x : EuclideanSpace ℂ (Fin p)) (hx : x ≠ 0) :
    ‖complexUnitNormalize x‖ = 1 := norm_smul_inv_norm hx

theorem complexUnitNormalize_distance {p : ℕ} (x u : EuclideanSpace ℂ (Fin p))
    (hx : ‖x‖ = 1) (hu : u ≠ 0) :
    ‖x - complexUnitNormalize u‖ ≤ 2 * ‖x - u‖ := by
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hDiff : ‖u - complexUnitNormalize u‖ = |‖u‖ - 1| := by
    have hSub : u - complexUnitNormalize u = (1 - ‖u‖⁻¹ : ℝ) • u := by
      rw [sub_smul, one_smul]
      rfl
    rw [hSub, norm_smul, Real.norm_eq_abs]
    calc
      _ = |(1 - ‖u‖⁻¹) * ‖u‖| := by rw [abs_mul, abs_of_pos huNorm]
      _ = _ := by rw [sub_mul, one_mul, inv_mul_cancel₀ huNorm.ne']
  have hReverse : |‖u‖ - 1| ≤ ‖x - u‖ := by
    simpa only [hx, norm_sub_rev] using abs_norm_sub_norm_le u x
  calc
    _ ≤ ‖x - u‖ + ‖u - complexUnitNormalize u‖ := norm_sub_le_norm_sub_add_norm_sub x u _
    _ ≤ ‖x - u‖ + ‖x - u‖ := by rw [hDiff]; exact add_le_add_right hReverse _
    _ = _ := by ring

def complexSphereGridBox (p k : ℕ) : Finset (EuclideanSpace ℂ (Fin p)) :=
  (Fintype.piFinset (fun _ : Fin p => gridBox k (gridBoxRadius k 1))).image (WithLp.toLp 2)

def complexSphereGrid (p k : ℕ) : Finset (EuclideanSpace ℂ (Fin p)) :=
  ((complexSphereGridBox p k).filter (fun x => x ≠ 0)).image complexUnitNormalize

theorem complexSphereGrid_unit {p k : ℕ} (x : EuclideanSpace ℂ (Fin p))
    (hx : x ∈ complexSphereGrid p k) : ‖x‖ = 1 := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  exact complexUnitNormalize_norm u (Finset.mem_filter.mp hu).2

theorem complexSphereGridBox_card_le (p k : ℕ) :
    (complexSphereGridBox p k).card ≤ (2 * k + 3) ^ (2 * p) := by
  apply Finset.card_image_le.trans
  rw [Fintype.card_piFinset]
  have hRadius : gridBoxRadius k 1 = k + 1 := by simp [gridBoxRadius]
  calc
    _ = (gridBox k (gridBoxRadius k 1)).card ^ p := by simp
    _ ≤ ((2 * (gridBoxRadius k 1) + 1) ^ 2) ^ p :=
      Nat.pow_le_pow_left (gridBox_card_le _ _) _
    _ = _ := by
      rw [hRadius, ← pow_mul]
      have hBase : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [hBase]

theorem complexSphereGrid_card_le (p k : ℕ) :
    (complexSphereGrid p k).card ≤ (2 * k + 3) ^ (2 * p) :=
  Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (complexSphereGridBox_card_le p k))

def complexSphereRound {p : ℕ} (k : ℕ) (x : EuclideanSpace ℂ (Fin p)) :
    EuclideanSpace ℂ (Fin p) := WithLp.toLp 2 (fun i => canonicalApprox k (x i))

theorem complexSphereRound_mem_box {p : ℕ} (k : ℕ) (x : EuclideanSpace ℂ (Fin p))
    (hx : ‖x‖ ≤ 1) : complexSphereRound k x ∈ complexSphereGridBox p k := by
  refine Finset.mem_image.mpr ⟨(fun i => canonicalApprox k (x i)), ?_, rfl⟩
  exact Fintype.mem_piFinset.mpr (fun i =>
    canonicalApprox_mem_gridBox (x i) ((PiLp.norm_apply_le x i).trans hx))

theorem complexSphereRound_error {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (x : EuclideanSpace ℂ (Fin p)) : ‖x - complexSphereRound k x‖ ≤ 2 * (p : ℝ) / k := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hCoord : ∀ i, ‖(x - complexSphereRound k x) i‖ ≤ 2 / (k : ℝ) := by
    intro i
    change ‖x i - canonicalApprox k (x i)‖ ≤ _
    apply (canonicalApprox_norm_error hk (x i)).trans
    apply div_le_div_of_nonneg_right _ hkR.le
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hSq : ‖x - complexSphereRound k x‖ ^ 2 ≤ (p : ℝ) * (2 / (k : ℝ)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin p, (2 / (k : ℝ)) ^ 2 := Finset.sum_le_sum
        (fun i _ => (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hCoord i))
      _ = _ := by simp
  have hP : (p : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have hFinal : ‖x - complexSphereRound k x‖ ^ 2 ≤ (2 * (p : ℝ) / k) ^ 2 := by
    apply hSq.trans
    convert mul_le_mul_of_nonneg_right hP (sq_nonneg (2 / (k : ℝ))) using 1
    ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hFinal

theorem complexSphereGrid_cover {p k : ℕ} (hp : 0 < p) (hk : 8 * p ≤ k)
    (x : EuclideanSpace ℂ (Fin p)) (hx : ‖x‖ = 1) :
    ∃ y ∈ complexSphereGrid p k, ‖x - y‖ ≤ 4 * (p : ℝ) / k := by
  have hkPos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkPos
  have hpkR : 8 * (p : ℝ) ≤ k := by exact_mod_cast hk
  have hError := complexSphereRound_error hp hkPos x
  have hQuarter : 2 * (p : ℝ) / k ≤ 1 / 4 := (div_le_iff₀ hkR).mpr (by nlinarith)
  have hNonzero : complexSphereRound k x ≠ 0 := by
    intro hZero
    rw [hZero, sub_zero, hx] at hError
    linarith
  refine ⟨complexUnitNormalize (complexSphereRound k x), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨complexSphereRound k x,
      Finset.mem_filter.mpr ⟨complexSphereRound_mem_box k x hx.le, hNonzero⟩, rfl⟩
  · apply (complexUnitNormalize_distance x _ hx hNonzero).trans
    calc
      _ ≤ 2 * (2 * (p : ℝ) / k) := mul_le_mul_of_nonneg_left hError (by norm_num)
      _ = _ := by ring

end CircularLaw
