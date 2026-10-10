import CircularLaw.BlockMultisetCounting
import CircularLaw.BinomialEntropy

/-!
# Entropy bounds for the block-multiset count

The weighted binomial theorem bounds each stars-and-bars factor directly
by real size and alphabet caps. No ceiling or floor of these caps is
needed. Both the small-block and small-alphabet forms are available.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem starsBars_exp_parameter (N A : ℕ) {x : ℝ} (hx : 0 < x) :
    ((A + N - 1).choose N : ℝ) ≤
      Real.exp ((A : ℝ) * Real.log (1 + x) + (N : ℝ) * Real.log (1 + x⁻¹)) := by
  have hChoose : ((A + N - 1).choose N : ℝ) ≤ (N + A).choose N := by
    exact_mod_cast Nat.choose_le_choose N (by omega : A + N - 1 ≤ N + A)
  have hTerm := binomial_term_le_power (by omega : N ≤ N + A) hx.le
  have hDiv := (le_div_iff₀ (pow_pos hx N)).mpr hTerm
  have hLog : Real.log (1 + x⁻¹) = Real.log (1 + x) - Real.log x := by
    have hArg : 1 + x⁻¹ = (1 + x) / x := by field_simp; ring
    rw [hArg, Real.log_div (by positivity : (1 + x : ℝ) ≠ 0) hx.ne']
  apply hChoose.trans (hDiv.trans_eq _)
  rw [show (1 + x) ^ (N + A) = Real.exp (((N + A : ℕ) : ℝ) * Real.log (1 + x)) by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 1 + x)],
    show x ^ N = Real.exp ((N : ℝ) * Real.log x) by rw [Real.exp_nat_mul, Real.exp_log hx],
    ← Real.exp_sub]
  congr 1
  rw [Nat.cast_add, hLog]
  ring

theorem starsBars_exp_bound {N A : ℕ} {M V : ℝ} (hM : 0 < M) (hV : 0 < V)
    (hN : (N : ℝ) ≤ M) (hA : (A : ℝ) ≤ V) :
    ((A + N - 1).choose N : ℝ) ≤
      Real.exp (M * Real.log (1 + V / M) + V * Real.log (1 + M / V)) := by
  have hLogM : 0 ≤ Real.log (1 + V / M) := Real.log_nonneg (by
    have h := div_pos hV hM
    linarith)
  have hLogV : 0 ≤ Real.log (1 + M / V) := Real.log_nonneg (by
    have h := div_pos hM hV
    linarith)
  have h := starsBars_exp_parameter N A (div_pos hM hV)
  simp only [inv_div] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right hN hLogM
  have h₂ := mul_le_mul_of_nonneg_right hA hLogV
  linarith

theorem starsBars_exp_bound_size {N A : ℕ} {M V : ℝ} (hM : 0 < M) (hV : 0 < V)
    (hN : (N : ℝ) ≤ M) (hA : (A : ℝ) ≤ V) :
    ((A + N - 1).choose N : ℝ) ≤
      Real.exp (M * (1 + Real.log (1 + V / M))) := by
  apply (starsBars_exp_bound hM hV hN hA).trans
  apply Real.exp_le_exp.mpr
  have hLog : Real.log (1 + M / V) ≤ M / V := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + M / V)
    linarith
  have h := mul_le_mul_of_nonneg_left hLog hV.le
  have hCancel : V * (M / V) = M := by field_simp
  rw [hCancel] at h
  linarith

theorem starsBars_exp_bound_alphabet {N A : ℕ} {M V : ℝ} (hM : 0 < M) (hV : 0 < V)
    (hN : (N : ℝ) ≤ M) (hA : (A : ℝ) ≤ V) :
    ((A + N - 1).choose N : ℝ) ≤
      Real.exp (V * (1 + Real.log (1 + M / V))) := by
  apply (starsBars_exp_bound hM hV hN hA).trans
  apply Real.exp_le_exp.mpr
  have hLog : Real.log (1 + V / M) ≤ V / M := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + V / M)
    linarith
  have h := mul_le_mul_of_nonneg_left hLog hM.le
  have hCancel : M * (V / M) = V := by field_simp
  rw [hCancel] at h
  linarith

end CircularLaw
