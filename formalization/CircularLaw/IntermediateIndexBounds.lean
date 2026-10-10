import CircularLaw.RowSingularValueComparison
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The literal intermediate-singular-value deletion indices

The manuscript uses `m=floor(n/d^3)-1`, `t=ceil(n/d^2)` and
`q0=m+2*t`. These estimates retain both rounding operations. The
zero-based singular-value position is `n-q0-1`, and its surviving tail
has exactly `t+1` entries.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical

namespace CircularLaw

def intermediateDeletionCount (n d : ℕ) : ℕ :=
  kernelCodimension n d + 2 * rowDeletionThreshold n d

theorem rowDeletionThreshold_dimension_bound {n d : ℕ} (hd : 0 < d) :
    n ≤ rowDeletionThreshold n d * d ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := Nat.le_ceil ((n : ℝ) / (d : ℝ) ^ 2)
  have hScaled := (div_le_iff₀ (pow_pos hdR 2)).mp h
  change (n : ℝ) ≤ (rowDeletionThreshold n d : ℝ) * (d : ℝ) ^ 2 at hScaled
  exact_mod_cast hScaled

theorem rowDeletionThreshold_scale_bound {n d : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) :
    (rowDeletionThreshold n d : ℝ) ≤ 2 * ((n : ℝ) / (d : ℝ) ^ 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPow : d ^ 2 ≤ d ^ 3 := Nat.pow_le_pow_right hd (by decide)
  have hSq : d ^ 2 ≤ n := by omega
  have hSqR : (d : ℝ) ^ 2 ≤ n := by exact_mod_cast hSq
  apply Nat.ceil_le_two_mul
  apply (le_div_iff₀ (pow_pos hdR 2)).mpr
  nlinarith [sq_nonneg (d : ℝ)]

theorem intermediateDeletionCount_scale_bound {n d : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) :
    (intermediateDeletionCount n d : ℝ) ≤ 5 * ((n : ℝ) / (d : ℝ) ^ 2) := by
  have hm := (kernelCodimension_bounds hd hn (Or.inl rfl)).2
  have ht := rowDeletionThreshold_scale_bound hd hn
  have hPow : d ^ 2 ≤ d ^ 3 := Nat.pow_le_pow_right hd (by decide)
  have hPowR : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 := by exact_mod_cast hPow
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRatio := div_le_div_of_nonneg_left (Nat.cast_nonneg n) (pow_pos hdR 2) hPowR
  have hm' := hm.trans hRatio
  simp only [intermediateDeletionCount, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith

theorem intermediateDeletionCount_lt_dimension {n d : ℕ} (hd : 4 ≤ d)
    (hn : 4 * d ^ 3 ≤ n) : intermediateDeletionCount n d < n := by
  have hdPos : 0 < d := by omega
  have hnPos : 0 < n := (mul_pos (by decide) (pow_pos hdPos 3)).trans_le hn
  have hScale := intermediateDeletionCount_scale_bound hdPos hn
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hSq : (5 : ℝ) < (d : ℝ) ^ 2 := by nlinarith
  have hRatio : 5 * ((n : ℝ) / (d : ℝ) ^ 2) < n := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ 2)).mpr
    nlinarith
  exact_mod_cast hScale.trans_lt hRatio

def intermediateSingularIndex (n d : ℕ) (h : intermediateDeletionCount n d < n) : Fin n :=
  ⟨n - intermediateDeletionCount n d - 1, by omega⟩

theorem intermediateSingularIndex_one_based {n d : ℕ}
    (h : intermediateDeletionCount n d < n) :
    (intermediateSingularIndex n d h).val + 1 = n - intermediateDeletionCount n d := by
  simp only [intermediateSingularIndex]
  omega

theorem intermediateSingularIndex_surviving_lt {n d : ℕ}
    (h : intermediateDeletionCount n d < n) :
    (intermediateSingularIndex n d h).val < n - kernelCodimension n d - rowDeletionThreshold n d := by
  unfold intermediateDeletionCount at h
  simp only [intermediateSingularIndex, intermediateDeletionCount]
  omega

theorem intermediateSingularIndex_tail_count {n d : ℕ}
    (h : intermediateDeletionCount n d < n) :
    n - kernelCodimension n d - rowDeletionThreshold n d -
      (intermediateSingularIndex n d h).val = rowDeletionThreshold n d + 1 := by
  unfold intermediateDeletionCount at h
  simp only [intermediateSingularIndex, intermediateDeletionCount]
  omega

theorem intermediateSingularIndex_tail_degree_bound {n d : ℕ} (hd : 0 < d)
    (h : intermediateDeletionCount n d < n) :
    n - kernelCodimension n d - rowDeletionThreshold n d ≤
      (n - kernelCodimension n d - rowDeletionThreshold n d -
        (intermediateSingularIndex n d h).val) * d ^ 2 := by
  rw [intermediateSingularIndex_tail_count]
  exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans
    ((rowDeletionThreshold_dimension_bound hd).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))))

end CircularLaw
