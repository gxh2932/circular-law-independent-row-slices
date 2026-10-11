import CircularLaw.SourceClassRowEnergy

/-!
# The missing-row factor in the structural branches

The literal upper codimension bound and logarithmic lower degree bound
give `(n*sqrt(d))^L <= exp(n)`. This coarse uniform bound suffices for
the subsequent energy absorption; no missing-row estimate is assumed.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem missingRowFactor_exp_bound {n d L : ℕ} (hn : 0 < n) (hd : 2 ≤ d)
    (hL : (L : ℝ) * (d : ℝ) ^ 3 ≤ n) (hLower : Real.log n ≤ (d : ℝ)) :
    ((n : ℝ) * Real.sqrt d) ^ L ≤ Real.exp (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hDTwo : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hLogD : Real.log d ≤ (d : ℝ) :=
    (Real.log_le_sub_one_of_pos hdR).trans (by linarith)
  have hSquare : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hDTwo 2
    norm_num at h
    exact h
  have hCube : (3 / 2 : ℝ) * d ≤ (d : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hSquare hdR.le]
  have hRoot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hLogBase : Real.log ((n : ℝ) * Real.sqrt d) ≤ (d : ℝ) ^ 3 := by
    rw [Real.log_mul hnR.ne' hRoot.ne', Real.log_sqrt hdR.le]
    linarith
  calc
    _ = Real.exp ((L : ℝ) * Real.log ((n : ℝ) * Real.sqrt d)) := by
      rw [Real.exp_nat_mul, Real.exp_log (mul_pos hnR hRoot)]
    _ ≤ Real.exp ((L : ℝ) * (d : ℝ) ^ 3) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLogBase (Nat.cast_nonneg L))
    _ ≤ _ := Real.exp_le_exp.mpr hL

theorem source_missingRowFactor_exp_bound {n d L : ℕ} {C : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hC : 1 ≤ C) (hLower : C * Real.log n ≤ (d : ℝ)) :
    ((n : ℝ) * Real.sqrt d) ^ L ≤ Real.exp (n : ℝ) := by
  have hFinite := source_kernel_dimension_twice_degree hConditions
  have hd : 2 ≤ d := by have h := hConditions.degree_large; omega
  have hCubic : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hFinite.2.1
      (by decide : 3 ≤ 4))).trans hConditions.dimension_fourth
  have hCodim := (kernelCodimension_bounds hFinite.2.1 hCubic hL).2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hFinite.2.1
  apply missingRowFactor_exp_bound hFinite.1 hd ((le_div_iff₀ (pow_pos hdR 3)).mp hCodim)
  have hLogN : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hFinite.1)
  exact (le_mul_of_one_le_left hLogN hC).trans hLower

end CircularLaw
