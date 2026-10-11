import CircularLaw.SteepScales

/-!
# The two source codimensions

The source uses `m=floor(n/d^3)-1` and `L=m,m+1`. The quotient is
positive in the finite range below, so the natural subtraction is the
same subtraction as in the manuscript.
-/

noncomputable section
open Classical

namespace CircularLaw

def kernelCodimension (n d : ℕ) : ℕ := n / d ^ 3 - 1

def IsKernelCodimension (n d L : ℕ) : Prop :=
  L = kernelCodimension n d ∨ L = kernelCodimension n d + 1

theorem kernelCodimension_quotient_bounds {n d L : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) :
    n / d ^ 3 - 1 ≤ L ∧ L ≤ n / d ^ 3 ∧ 0 < L := by
  have hFloor : 4 ≤ n / d ^ 3 := (Nat.le_div_iff_mul_le (pow_pos hd 3)).mpr hn
  rcases hL with hL | hL <;> unfold kernelCodimension at hL <;> omega

theorem kernelCodimension_bounds {n d L : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) :
    (n : ℝ) / (2 * (d : ℝ) ^ 3) ≤ L ∧ (L : ℝ) ≤ (n : ℝ) / (d : ℝ) ^ 3 := by
  have hD : 0 < d ^ 3 := pow_pos hd 3
  have hFloor : 4 ≤ n / d ^ 3 := (Nat.le_div_iff_mul_le hD).mpr hn
  have hBounds := kernelCodimension_quotient_bounds hd hn hL
  have hCount : n / d ^ 3 + 1 ≤ 2 * L := by omega
  have hUpperN := Nat.div_mul_le_self n (d ^ 3)
  have hLowerN := Nat.lt_mul_div_succ n hD
  have hScaled := Nat.mul_le_mul_left (d ^ 3) hCount
  have hNLower : n ≤ 2 * d ^ 3 * L := by nlinarith
  have hNUpper : L * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_right (d ^ 3) hBounds.2.1).trans hUpperN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ) ^ 3)).mpr
    have h : (n : ℝ) ≤ 2 * (d : ℝ) ^ 3 * L := by exact_mod_cast hNLower
    nlinarith
  · apply (le_div_iff₀ (pow_pos hdR 3)).mpr
    exact_mod_cast hNUpper

theorem kernelCodimension_large_lower {n d L : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 4 ≤ n) (hL : IsKernelCodimension n d L) : 2 * d ≤ L := by
  have hFloor : 4 * d ≤ n / d ^ 3 := by
    apply (Nat.le_div_iff_mul_le (pow_pos hd 3)).mpr
    convert hn using 1
    ring
  rcases hL with hL | hL <;> unfold kernelCodimension at hL <;> omega

theorem kernelCodimension_retained_card {n d L : ℕ} (hd : 5 ≤ d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L)
    (I : Finset (Fin n)) (hI : I.card = n - L) :
    (99 / 100 : ℝ) * n ≤ I.card := by
  have hdPos : 0 < d := by omega
  have hBounds := kernelCodimension_quotient_bounds hdPos hn hL
  have hLn : L ≤ n := hBounds.2.1.trans (Nat.div_le_self n (d ^ 3))
  have hPower : 100 ≤ d ^ 3 := by
    have h := Nat.pow_le_pow_left hd 3
    norm_num at h
    omega
  have hLPower : L * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_right (d ^ 3) hBounds.2.1).trans (Nat.div_mul_le_self n (d ^ 3))
  have hLScaled := Nat.mul_le_mul_left L hPower
  have hNat : 100 * L ≤ n := by nlinarith
  have hReal : (100 : ℝ) * L ≤ n := by exact_mod_cast hNat
  rw [hI, Nat.cast_sub hLn]
  linarith

end CircularLaw
