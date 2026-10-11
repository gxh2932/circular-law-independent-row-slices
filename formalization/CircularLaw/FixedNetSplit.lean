import CircularLaw.ClassRowEnergy
import CircularLaw.FixedNetSlice

/-!
# Separating the two fixed-net probability terms

The dispersion term uses the actual canonical class energy. The additive
profile-exception term retains the actual number of class members. The
conditioning cost and logarithmic row factor are shared by both terms.
-/

noncomputable section
open Classical

namespace CircularLaw

def fixedNetRowFactor (n d K : ℕ) (R : ℝ) : ℝ :=
  4 * Real.exp 1 * rowSmallBallConstant * R ^ 2 * ((n : ℝ) / K) * Real.log d ^ 2

def fixedNetSplitCost (n d K : ℕ) (R : ℝ) : ℝ :=
  Real.exp (2 * (K : ℝ) * (d : ℝ) ^ 2 / n) * (2 * fixedNetRowFactor n d K R) ^ K

theorem fixedNetRowFactor_nonneg (n d K : ℕ) (R : ℝ) :
    0 ≤ fixedNetRowFactor n d K R := by
  have hConstant : 0 ≤ rowSmallBallConstant := by linarith [rowSmallBallConstant_ge_one]
  unfold fixedNetRowFactor
  positivity

theorem fixedNetSplitCost_nonneg (n d K : ℕ) (R : ℝ) :
    0 ≤ fixedNetSplitCost n d K R :=
  mul_nonneg (Real.exp_nonneg _) (pow_nonneg (mul_nonneg (by norm_num)
    (fixedNetRowFactor_nonneg n d K R)) K)

theorem fixedNetSliceEstimate_split {n d : ℕ} (hd : 0 < d)
    (k K : ℕ) (y : Fin n → ℂ) (R : ℝ) :
    let P := orderedCanonicalRowProfile y ((d : ℝ) / k)
    fixedNetSliceEstimate k d K y R ≤ fixedNetSplitCost n d K R *
      ((4 : ℝ) ^ K * profileGeometricMean P.part (truncatedProfileWeight P d) ^ K *
        Real.exp (-averagedProfileRate * (K : ℝ) * profileCoordinateDispersion P d) +
          Real.exp (-averagedProfileRate * (K : ℝ) * Real.rpow (d : ℝ) (2 / 3))) := by
  intro P
  let W := profileGeometricMean P.part (truncatedProfileWeight P d)
  let D := profileCoordinateDispersion P d
  let a := 4 * Real.exp (-averagedProfileRate * D) * W
  let b := Real.exp (-averagedProfileRate * Real.rpow (d : ℝ) (2 / 3))
  have hW : 0 ≤ W := (profileGeometricMean_pos P.part _ (truncatedProfileWeight_pos P hd)).le
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _)) hW
  have hb : 0 ≤ b := Real.exp_nonneg _
  have hSplit : (a + b) ^ K ≤ (2 : ℝ) ^ K * (a ^ K + b ^ K) :=
    (add_pow_le ha hb K).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le K 1))
      (add_nonneg (pow_nonneg ha K) (pow_nonneg hb K)))
  have haPow : a ^ K = (4 : ℝ) ^ K * W ^ K * Real.exp (-averagedProfileRate * (K : ℝ) * D) := by
    dsimp only [a]
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
    rw [show (K : ℝ) * (-averagedProfileRate * D) = -averagedProfileRate * (K : ℝ) * D by ring]
    ring
  have hbPow : b ^ K = Real.exp (-averagedProfileRate * (K : ℝ) * Real.rpow (d : ℝ) (2 / 3)) := by
    dsimp only [b]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    fixedNetSliceEstimate k d K y R =
        (Real.exp (2 * (K : ℝ) * (d : ℝ) ^ 2 / n) * fixedNetRowFactor n d K R ^ K) *
          (a + b) ^ K := by
      dsimp only [fixedNetSliceEstimate, fixedNetRowFactor, a, b, W, D, P]
      rw [mul_pow]
      ring
    _ ≤ (Real.exp (2 * (K : ℝ) * (d : ℝ) ^ 2 / n) * fixedNetRowFactor n d K R ^ K) *
        ((2 : ℝ) ^ K * (a ^ K + b ^ K)) :=
      mul_le_mul_of_nonneg_left hSplit (mul_nonneg (Real.exp_nonneg _)
        (pow_nonneg (fixedNetRowFactor_nonneg n d K R) K))
    _ = _ := by
      rw [haPow, hbPow]
      dsimp only [fixedNetSplitCost, W, D]
      rw [mul_pow]
      ring

theorem canonicalClass_fixed_estimate_split {n d : ℕ} (hd : 0 < d)
    (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (k K : ℕ) (R : ℝ) :
    (Nat.card (CoordinateMultisetClassIn A y) : ℝ) * fixedNetSliceEstimate k d K y R ≤
      fixedNetSplitCost n d K R *
        ((4 : ℝ) ^ K * canonicalClassRowEnergy A y ((d : ℝ) / k) d K averagedProfileRate +
          (Nat.card (CoordinateMultisetClassIn A y) : ℝ) *
            Real.exp (-averagedProfileRate * (K : ℝ) * Real.rpow (d : ℝ) (2 / 3))) := by
  have h := mul_le_mul_of_nonneg_left (fixedNetSliceEstimate_split hd k K y R)
    (Nat.cast_nonneg (Nat.card (CoordinateMultisetClassIn A y)) : (0 : ℝ) ≤ _)
  apply h.trans_eq
  dsimp only [canonicalClassRowEnergy]
  ring

end CircularLaw
