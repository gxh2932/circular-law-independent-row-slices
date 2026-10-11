import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Basic

/-!
# A uniform local binomial mass bound from checked Stirling estimates

The denominator bounds follow from the antitone Stirling sequence;
the numerator uses mathlib's effective factorial lower bound. This
supplies the source's `c/sqrt(d)` local conditioning estimate.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators Nat

namespace CircularLaw

def stirlingNormalizedFactorial (n : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((n : ℝ) / Real.exp 1) ^ n

theorem stirlingNormalizedFactorial_pos {n : ℕ} (hn : 0 < n) :
    0 < stirlingNormalizedFactorial n := by
  unfold stirlingNormalizedFactorial
  positivity

theorem stirlingNormalizedFactorial_eq_sequence {n : ℕ} (hn : 0 < n) :
    stirlingNormalizedFactorial n = Stirling.stirlingSeq n * Real.sqrt (2 * (n : ℝ)) := by
  unfold stirlingNormalizedFactorial Stirling.stirlingSeq
  have hRoot : Real.sqrt (2 * (n : ℝ)) ≠ 0 := by positivity
  field_simp

theorem stirlingNormalizedFactorial_lower {n : ℕ} (hn : 0 < n) :
    Real.sqrt (n : ℝ) ≤ stirlingNormalizedFactorial n := by
  have hPower : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
  rw [stirlingNormalizedFactorial, le_div_iff₀ hPower]
  have hRoot : Real.sqrt (n : ℝ) ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_gt_three, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact (mul_le_mul_of_nonneg_right hRoot hPower.le).trans (Stirling.le_factorial_stirling n)

theorem stirlingNormalizedFactorial_upper {n : ℕ} (hn : 0 < n) :
    stirlingNormalizedFactorial n ≤ 2 * Real.exp 1 * Real.sqrt (n : ℝ) := by
  have hSeq : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  have hRootTwo : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hExp : 0 < Real.exp 1 := Real.exp_pos _
  rw [Stirling.stirlingSeq_one] at hSeq
  have hSeqUpper : Stirling.stirlingSeq n ≤ Real.exp 1 :=
    hSeq.trans ((div_le_iff₀ (by positivity : 0 < Real.sqrt 2)).mpr (by nlinarith))
  have hRoot : Real.sqrt (2 * (n : ℝ)) ≤ 2 * Real.sqrt (n : ℝ) := by
    have hSquare := Real.sq_sqrt (by positivity : 0 ≤ 2 * (n : ℝ))
    have hNSquare := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith [Real.sqrt_nonneg (2 * (n : ℝ)), Real.sqrt_nonneg (n : ℝ)]
  rw [stirlingNormalizedFactorial_eq_sequence hn]
  calc
    _ ≤ Real.exp 1 * Real.sqrt (2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hSeqUpper (Real.sqrt_nonneg _)
    _ ≤ Real.exp 1 * (2 * Real.sqrt (n : ℝ)) := mul_le_mul_of_nonneg_left hRoot hExp.le
    _ = _ := by ring

def splitBinomialMass (a b : ℕ) : ℝ :=
  ((a + b).choose a : ℝ) * ((a : ℝ) / (a + b)) ^ a * ((b : ℝ) / (a + b)) ^ b

theorem splitBinomialMass_nonneg (a b : ℕ) : 0 ≤ splitBinomialMass a b := by
  unfold splitBinomialMass
  positivity

theorem splitBinomialMass_normalized_identity {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    splitBinomialMass a b * stirlingNormalizedFactorial a * stirlingNormalizedFactorial b =
      stirlingNormalizedFactorial (a + b) := by
  have hFactorial : ((a + b).choose a : ℝ) * a.factorial * b.factorial = (a + b).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    simpa only [Nat.add_sub_cancel_left, Nat.cast_mul] using congrArg (fun k : ℕ => (k : ℝ)) h
  have haR : (a : ℝ) ≠ 0 := by positivity
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have hSumR : (a : ℝ) + b ≠ 0 := by positivity
  have hExp : Real.exp 1 ≠ 0 := (Real.exp_pos _).ne'
  simp only [splitBinomialMass, stirlingNormalizedFactorial, Nat.cast_add, div_pow, pow_add]
  field_simp
  nlinarith [hFactorial]

theorem splitBinomialMass_lower {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    1 / (4 * Real.exp 1 ^ 2 * Real.sqrt (a : ℝ)) ≤ splitBinomialMass a b := by
  have hMass := splitBinomialMass_nonneg a b
  have hA := stirlingNormalizedFactorial_upper ha
  have hB := stirlingNormalizedFactorial_upper hb
  have hA0 := (stirlingNormalizedFactorial_pos ha).le
  have hB0 := (stirlingNormalizedFactorial_pos hb).le
  have hN := stirlingNormalizedFactorial_lower (show 0 < a + b by omega)
  have hRoot : Real.sqrt (b : ℝ) ≤ Real.sqrt ((a + b : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_add_left b a)
  have hProduct := mul_le_mul hA hB hB0 (by positivity : 0 ≤ 2 * Real.exp 1 * Real.sqrt (a : ℝ))
  have hWeighted := mul_le_mul_of_nonneg_left hProduct hMass
  have hIdentity := splitBinomialMass_normalized_identity ha hb
  have hMassBound : Real.sqrt (b : ℝ) ≤
      (splitBinomialMass a b * (4 * Real.exp 1 ^ 2 * Real.sqrt (a : ℝ))) * Real.sqrt (b : ℝ) := by
    nlinarith [hRoot.trans hN]
  have hRootB : 0 < Real.sqrt (b : ℝ) := by positivity
  have hOne : 1 ≤ splitBinomialMass a b * (4 * Real.exp 1 ^ 2 * Real.sqrt (a : ℝ)) := by
    nlinarith
  exact (div_le_iff₀ (by positivity : 0 < 4 * Real.exp 1 ^ 2 * Real.sqrt (a : ℝ))).mpr hOne

end CircularLaw
