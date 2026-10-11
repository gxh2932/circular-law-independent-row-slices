import CircularLaw.BernoulliSecondMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The literal deletion count for both hermitization regimes

The lower-band choice has a=1/2, and the superlogarithmic choice has
0<a<1. The ceiling is retained in every finite bound. Its relative size
tends to zero along sparse growing degree sequences.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def hermitizationDeletionCount (n d : ℕ) (a : ℝ) : ℕ :=
  ⌈(n : ℝ) / Real.rpow (d : ℝ) a⌉₊

theorem hermitizationDeletionCount_pos {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (a : ℝ) :
    0 < hermitizationDeletionCount n d a := by
  exact Nat.ceil_pos.mpr (div_pos (by exact_mod_cast hn)
    (Real.rpow_pos_of_pos (by exact_mod_cast hd) a))

theorem hermitizationDeletionCount_lower (n d : ℕ) (a : ℝ) :
    (n : ℝ) / Real.rpow (d : ℝ) a ≤ hermitizationDeletionCount n d a := Nat.le_ceil _

theorem hermitizationDeletionCount_upper {n d : ℕ} (hd : 0 < d) (a : ℝ)
    (hDimension : Real.rpow (d : ℝ) a ≤ n) :
    (hermitizationDeletionCount n d a : ℝ) ≤ 2 * n / Real.rpow (d : ℝ) a := by
  have hPower : 0 < Real.rpow (d : ℝ) a := Real.rpow_pos_of_pos (by exact_mod_cast hd) a
  have hRatio : (1 : ℝ) ≤ n / Real.rpow (d : ℝ) a :=
    (le_div_iff₀ hPower).mpr (by simpa only [one_mul] using hDimension)
  have hCeil := Nat.ceil_lt_add_one (le_trans zero_le_one hRatio)
  change (hermitizationDeletionCount n d a : ℝ) < (n : ℝ) / Real.rpow (d : ℝ) a + 1 at hCeil
  calc
    _ ≤ 2 * ((n : ℝ) / Real.rpow (d : ℝ) a) := by linarith
    _ = _ := by ring

theorem hermitizationDeletionCount_le_dimension {n d : ℕ} (hd : 1 ≤ d)
    {a : ℝ} (ha : 0 ≤ a) : hermitizationDeletionCount n d a ≤ n := by
  have hPower : (1 : ℝ) ≤ Real.rpow (d : ℝ) a := by
    simpa only [Real.rpow_eq_pow] using
      Real.one_le_rpow (show (1 : ℝ) ≤ d by exact_mod_cast hd) ha
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by linarith : 0 < Real.rpow (d : ℝ) a)).mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hPower (Nat.cast_nonneg n)

theorem hermitization_deletion_fraction_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) :
    Tendsto (fun n => (hermitizationDeletionCount n (d n) a : ℝ) / n) atTop (𝓝 0) := by
  have hCast : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hInv := ((tendsto_rpow_atTop ha).comp hCast).inv_tendsto_atTop
  have hUpper : Tendsto (fun n => 2 / Real.rpow (d n : ℝ) a) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hInv.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun _ => by positivity))
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse, eventually_gt_atTop 0]
    with n hDegreeN hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPow : Real.rpow (d n : ℝ) a ≤ n := by
    calc
      _ ≤ (d n : ℝ) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ d n by exact_mod_cast hDegreeN.1) haOne
      _ ≤ n := by exact_mod_cast hDegreeN.2
  have hBound := div_le_div_of_nonneg_right
    (hermitizationDeletionCount_upper hDegreeN.1 a hPow) hnR.le
  have hScale : (2 * (n : ℝ) / Real.rpow (d n : ℝ) a) / n =
      2 / Real.rpow (d n : ℝ) a := by field_simp
  exact hScale ▸ hBound

theorem eventually_hermitization_deletion_valid (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) :
    ∀ᶠ n in atTop, 0 < hermitizationDeletionCount n (d n) a ∧
      hermitizationDeletionCount n (d n) a < n ∧
      1 ≤ n - hermitizationDeletionCount n (d n) a := by
  have hSmall := (hermitization_deletion_fraction_tendsto_zero d hDegree hSparse ha haOne).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hSmall, eventually_valid_bernoulli_degrees hDegree hSparse, eventually_gt_atTop 0]
    with n hFraction hd hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRn : hermitizationDeletionCount n (d n) a < n := by
    exact_mod_cast (div_lt_one hnR).mp hFraction
  exact ⟨hermitizationDeletionCount_pos hn hd.1 a, hRn, by omega⟩

end CircularLaw
