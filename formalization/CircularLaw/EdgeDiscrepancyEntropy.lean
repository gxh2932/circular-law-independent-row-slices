import CircularLaw.BinomialEntropy

/-!
# Entropy cost for rectangular discrepancy

The size cost `r * log(e*n/r)` increases for `1 <= r <= n`.
The proof uses `log(u) <= u-1`, rather than assuming this monotonicity.
It absorbs the actual binomial counts of row and column sets.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def edgeSetEntropy (n r : ℕ) : ℝ := (r : ℝ) * Real.log (Real.exp 1 * n / r)

theorem real_edge_entropy_mono {N x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyN : y ≤ N) :
    x * Real.log (Real.exp 1 * N / x) ≤ y * Real.log (Real.exp 1 * N / y) := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : 0 < N := hy.trans_le hyN
  have hBase : Real.exp 1 ≤ Real.exp 1 * N / y := by
    apply (le_div_iff₀ hy).mpr
    exact mul_le_mul_of_nonneg_left hyN (Real.exp_nonneg _)
  have hLogBase : 1 ≤ Real.log (Real.exp 1 * N / y) := by
    have h := Real.log_le_log (Real.exp_pos 1) hBase
    simpa only [Real.log_exp] using h
  have hRatio : Real.exp 1 * N / x = (Real.exp 1 * N / y) * (y / x) := by
    field_simp
  have hLog : Real.log (Real.exp 1 * N / x) =
      Real.log (Real.exp 1 * N / y) + Real.log (y / x) := by
    rw [hRatio, Real.log_mul (by positivity) (div_pos hy hx).ne']
  have hRemainder : x * Real.log (y / x) ≤ y - x := by
    apply (mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hy hx)) hx.le).trans_eq
    field_simp
  have hBaseCost := mul_le_mul_of_nonneg_left hLogBase (sub_nonneg.mpr hxy)
  rw [hLog]
  nlinarith only [hRemainder, hBaseCost]

theorem edgeSetEntropy_mono {n k r : ℕ} (hk : 0 < k) (hkr : k ≤ r) (hrn : r ≤ n) :
    edgeSetEntropy n k ≤ edgeSetEntropy n r := by
  exact real_edge_entropy_mono (by exact_mod_cast hk) (by exact_mod_cast hkr) (by exact_mod_cast hrn)

theorem edgeSetEntropy_log_lower {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n) :
    Real.log (n : ℝ) ≤ edgeSetEntropy n r := by
  have hn : 0 < n := hr.trans_le hrn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := edgeSetEntropy_mono (n := n) (k := 1) (r := r) (by omega) (by omega) hrn
  unfold edgeSetEntropy at h
  simp only [Nat.cast_one, div_one, one_mul,
    Real.log_mul (Real.exp_pos 1).ne' hnR.ne', Real.log_exp] at h
  unfold edgeSetEntropy
  linarith only [h]

theorem choose_rectangular_entropy {m n k l : ℕ} (hn : 0 < n) (hmn : m ≤ n)
    (hk : 0 < k) (hkm : k ≤ m) (hl : 0 < l) (hln : l ≤ n) :
    (m.choose k : ℝ) * (n.choose l : ℝ) ≤ Real.exp (2 * edgeSetEntropy n (max k l)) := by
  have hkn : k ≤ n := hkm.trans hmn
  have hMax : max k l ≤ n := max_le hkn hln
  have hFirst : (m.choose k : ℝ) ≤ Real.exp (edgeSetEntropy n k) := by
    apply (show (m.choose k : ℝ) ≤ n.choose k by exact_mod_cast Nat.choose_mono k hmn).trans
    exact choose_le_exp_entropy hn hk hkn
  have hSecond := choose_le_exp_entropy hn hl hln
  apply (mul_le_mul hFirst hSecond (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hK := edgeSetEntropy_mono hk (le_max_left k l) hMax
  have hL := edgeSetEntropy_mono hl (le_max_right k l) hMax
  change edgeSetEntropy n k + edgeSetEntropy n l ≤ _
  linarith only [hK, hL]

end CircularLaw
