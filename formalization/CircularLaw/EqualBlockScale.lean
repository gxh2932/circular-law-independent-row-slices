import CircularLaw.OrderedBlockGeometry

/-!
# Exact floor scales for equal blocks

The scale is the integer quotient `n/(200*d)`, which is the exact floor
in the manuscript. Both uses of integer division retain their rounding.
-/

noncomputable section
open Classical

namespace CircularLaw

def equalBlockScale (n d : ℕ) : ℕ := n / (200 * d)

theorem equalBlockScale_eq_floor (n d : ℕ) :
    equalBlockScale n d = ⌊(n : ℝ) / (200 * (d : ℝ))⌋₊ := by
  rw [show 200 * (d : ℝ) = ((200 * d : ℕ) : ℝ) by simp only [Nat.cast_mul, Nat.cast_ofNat],
    Nat.floor_div_natCast, Nat.floor_natCast]
  rfl

theorem quotient_product_ge_half {m s : ℕ} (hs : 0 < s) (hsm : s ≤ m) :
    (m : ℝ) / 2 ≤ ((m / s : ℕ) : ℝ) * s := by
  have hq : 0 < m / s := Nat.div_pos hsm hs
  have hUpper : (m : ℝ) < (s : ℝ) * (((m / s : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ m hs
  have hqReal : (1 : ℝ) ≤ (m / s : ℕ) := by exact_mod_cast hq
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  nlinarith

theorem equalBlockScale_pos {n d : ℕ} (hd : 0 < d) (hn : 400 * d ≤ n) :
    0 < equalBlockScale n d := by
  apply Nat.div_pos (by omega)
  omega

theorem equalBlockScale_density_lower {n d : ℕ} (hd : 0 < d) (hn : 400 * d ≤ n) :
    (n : ℝ) / 400 ≤ (d : ℝ) * equalBlockScale n d := by
  have h := quotient_product_ge_half (by omega : 0 < 200 * d) (by omega : 200 * d ≤ n)
  push_cast at h
  change (n : ℝ) / 2 ≤ (equalBlockScale n d : ℝ) * (200 * (d : ℝ)) at h
  nlinarith

theorem equalBlockScale_le_dimension (n d : ℕ) : equalBlockScale n d ≤ n :=
  Nat.div_le_self _ _

theorem equalBlockScale_density_upper {n d : ℕ} :
    (d : ℝ) * equalBlockScale n d ≤ (n : ℝ) / 200 := by
  have h : (equalBlockScale n d : ℝ) * (200 * (d : ℝ)) ≤ n := by
    exact_mod_cast Nat.div_mul_le_self n (200 * d)
  nlinarith

theorem equalBlockScale_quotient_pos {n d m : ℕ} (hd : 0 < d) (hn : 400 * d ≤ n)
    (hm : equalBlockScale n d ≤ m) : 0 < m / equalBlockScale n d :=
  Nat.div_pos hm (equalBlockScale_pos hd hn)

theorem equalBlockScale_quotient_fit {n d m : ℕ} :
    (m / equalBlockScale n d) * equalBlockScale n d ≤ m :=
  Nat.div_mul_le_self _ _

theorem equalBlockScale_quotient_ge_half {n d m : ℕ}
    (hd : 0 < d) (hn : 400 * d ≤ n) (hm : equalBlockScale n d ≤ m) :
    (m : ℝ) / 2 ≤ ((m / equalBlockScale n d : ℕ) : ℝ) * equalBlockScale n d :=
  quotient_product_ge_half (equalBlockScale_pos hd hn) hm

theorem equalBlockScale_ratio_lower {n d m : ℕ} {C : ℝ}
    (hd : 0 < d) (hn : 400 * d ≤ n) (hC : 0 ≤ C)
    (hm : C * equalBlockScale n d ≤ (m : ℝ)) :
    C / 400 ≤ (d : ℝ) * m / n := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (le_div_iff₀ hnPos).mpr
  have hDensity := equalBlockScale_density_lower hd hn
  have hScaled := mul_le_mul_of_nonneg_left hDensity hC
  have hM := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  nlinarith

end CircularLaw
