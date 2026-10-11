import CircularLaw.HermitizationDeletionParameters
import CircularLaw.RowReplacementProbability

/-!
# Effective codimension at the literal hermitization cutoff

The ceiling supplies Q >= d^(1-a)/2 when d/n <= 1/2. This discharges
Q >= 1 eventually for every 0<a<1, including the exact balanced
superlogarithmic exponent from the manuscript.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem hermitization_row_comparison_Q_lower {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {a : ℝ} (hHalf : (d : ℝ) / n ≤ 1 / 2) :
    Real.rpow (d : ℝ) (1 - a) / 2 ≤
      rowLogComparisonQ n d (hermitizationDeletionCount n d a) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : (0 : ℝ) ≤ (d : ℝ) / n := by positivity
  have hVariance : (d : ℝ) / n / 2 ≤ ((d : ℝ) / n) * (1 - (d : ℝ) / n) := by
    nlinarith [mul_nonneg hp (show 0 ≤ 1 / 2 - (d : ℝ) / n by linarith)]
  have hCount := hermitizationDeletionCount_lower n d a
  have hCountNonneg : (0 : ℝ) ≤ hermitizationDeletionCount n d a := by positivity
  have hVarianceNonneg : 0 ≤ ((d : ℝ) / n) * (1 - (d : ℝ) / n) :=
    mul_nonneg hp (by linarith)
  have hIdentity : Real.rpow (d : ℝ) (1 - a) = (d : ℝ) / Real.rpow (d : ℝ) a := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using Real.rpow_sub hdR 1 a
  have hCancel : ((d : ℝ) / n / 2) * ((n : ℝ) / Real.rpow (d : ℝ) a) =
      (d : ℝ) / Real.rpow (d : ℝ) a / 2 := by field_simp
  rw [hIdentity, rowLogComparisonQ, rowBernoulliParameter_coe]
  calc
    _ = ((d : ℝ) / n / 2) * ((n : ℝ) / Real.rpow (d : ℝ) a) := hCancel.symm
    _ ≤ ((d : ℝ) / n / 2) * hermitizationDeletionCount n d a :=
      mul_le_mul_of_nonneg_left hCount (by positivity)
    _ ≤ (((d : ℝ) / n) * (1 - (d : ℝ) / n)) *
        ((hermitizationDeletionCount n d a : ℝ) + 1) :=
      mul_le_mul hVariance (by linarith) hCountNonneg hVarianceNonneg

theorem eventually_hermitization_row_comparison_Q_ge_one (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    ∀ᶠ n in atTop, 1 ≤ rowLogComparisonQ n (d n)
      (n - (n - hermitizationDeletionCount n (d n) a)) := by
  have hCast : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hLarge := ((tendsto_rpow_atTop (sub_pos.mpr haOne)).comp hCast).eventually_ge_atTop 2
  have hHalf := hSparse.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hLarge, hHalf, eventually_valid_bernoulli_degrees hDegree hSparse,
    eventually_hermitization_deletion_valid d hDegree hSparse ha haOne.le] with n hL hH hd hr
  have hn : 0 < n := lt_of_lt_of_le hd.1 hd.2
  rw [Nat.sub_sub_self hr.2.1.le]
  have hLower := hermitization_row_comparison_Q_lower hn hd.1 hH.le (a := a)
  have hPower : (2 : ℝ) ≤ Real.rpow (d n : ℝ) (1 - a) := by
    simpa only [Real.rpow_eq_pow] using hL
  exact (show (1 : ℝ) ≤ Real.rpow (d n : ℝ) (1 - a) / 2 by linarith).trans hLower

def superlogHermitizationExponent (ε : ℝ) : ℝ := (2 + ε) / (2 * (1 + ε))

theorem superlog_hermitization_exponent_range {ε : ℝ} (hε : 0 < ε) :
    0 < superlogHermitizationExponent ε ∧ superlogHermitizationExponent ε < 1 := by
  unfold superlogHermitizationExponent
  refine ⟨by positivity, ?_⟩
  apply (div_lt_one (by positivity : (0 : ℝ) < 2 * (1 + ε))).mpr
  linarith

theorem superlog_hermitization_exponent_identities {ε : ℝ} (hε : 0 < ε) :
    1 - superlogHermitizationExponent ε = ε / (2 * (1 + ε)) ∧
      superlogHermitizationExponent ε * (1 + ε) - 1 = ε / 2 := by
  have hDen : (1 + ε : ℝ) ≠ 0 := by positivity
  unfold superlogHermitizationExponent
  constructor <;> field_simp <;> ring

end CircularLaw
