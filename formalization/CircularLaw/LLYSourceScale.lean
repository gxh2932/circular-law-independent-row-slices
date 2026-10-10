import CircularLaw.LLYSourceRanks

/-!
# The integer source scale including the first-rank-one case

Taking the natural logarithm of the predecessor gives exactly the
source inequalities `ell^r < n1 <= ell^(r+1)` when n1 exceeds one.
For n1 equal to one it gives scale zero and the same upper fit.
-/

noncomputable section
open Classical

namespace CircularLaw

def llySourceScale (n d : ℕ) (a : ℝ) : ℕ :=
  Nat.log (llySourceStride n d) (llySourceFirstRank n d a - 1)

theorem lly_source_scale_ranks {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {C a : ℝ} (hC : 1920000 ≤ C) (hDegree : C * Real.log (n : ℝ) ≤ d) (ha : 0 < a) :
    (llySourceFirstRank n d a = 1 ∨
      (llySourceStride n d) ^ (llySourceScale n d a) < llySourceFirstRank n d a) ∧
        llySourceFirstRank n d a ≤ (llySourceStride n d) ^ (llySourceScale n d a + 1) := by
  have hStride := lly_source_stride_ge_two hn hd hC hDegree
  have hFirst := lly_source_first_rank_pos hn hd ha
  have hUpper := Nat.lt_pow_succ_log_self (by omega : 1 < llySourceStride n d)
    (llySourceFirstRank n d a - 1)
  change llySourceFirstRank n d a - 1 <
    (llySourceStride n d) ^ (llySourceScale n d a + 1) at hUpper
  refine ⟨?_, by omega⟩
  by_cases hOne : llySourceFirstRank n d a = 1
  · exact Or.inl hOne
  · have hLower := Nat.pow_log_le_self (llySourceStride n d)
      (by omega : llySourceFirstRank n d a - 1 ≠ 0)
    change (llySourceStride n d) ^ (llySourceScale n d a) ≤ llySourceFirstRank n d a - 1 at hLower
    exact Or.inr (by omega)

end CircularLaw
