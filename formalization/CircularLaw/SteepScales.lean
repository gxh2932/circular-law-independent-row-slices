import CircularLaw.FirstSteepScale
import Mathlib.Data.Nat.Log

/-!
# The source geometric and terminal steep scales

The beginning exponent is the least one reaching `20*L/d`; the final
exponent satisfies `p^r < n1 <= p^(r+1)`. Natural ceiling logarithms and
floor logarithms implement these definitions, including the terminal
size `ceil(n1/p)`.
-/

noncomputable section
open Classical

namespace CircularLaw

def steepStride (d : ℕ) : ℕ :=
  ⌊(1 / 5 : ℝ) * Real.sqrt ((d : ℝ) / Real.log d)⌋₊

def steepStartExponent (p d L : ℕ) : ℕ :=
  Nat.clog p ⌈20 * (L : ℝ) / d⌉₊

def steepEndExponent (p n1 : ℕ) : ℕ := Nat.log p (n1 - 1)

def terminalSteepSize (p n1 : ℕ) : ℕ := ⌈(n1 : ℝ) / p⌉₊

def steepScalePairs (p n1 r0 r : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico r0 r).image (fun i => (p ^ i, p ^ (i + 1)))) ∪
    {(terminalSteepSize p n1, n1)}

def sourceSteepScalePairs (n d L : ℕ) : Finset (ℕ × ℕ) :=
  steepScalePairs (steepStride d) (firstSteepScale n d)
    (steepStartExponent (steepStride d) d L)
    (steepEndExponent (steepStride d) (firstSteepScale n d))

theorem steepStartExponent_le_iff {p d L r : ℕ} (hp : 1 < p) :
    steepStartExponent p d L ≤ r ↔ 20 * (L : ℝ) / d ≤ (p ^ r : ℕ) := by
  rw [steepStartExponent, Nat.clog_le_iff_le_pow hp, Nat.ceil_le]

theorem steepStartExponent_lower {p d L : ℕ} (hp : 1 < p) :
    20 * (L : ℝ) / d ≤ (p ^ steepStartExponent p d L : ℕ) :=
  (steepStartExponent_le_iff hp).mp le_rfl

theorem steepStartExponent_upper {p d L : ℕ} (hp : 1 < p)
    (hStart : 0 < steepStartExponent p d L) :
    ((p ^ steepStartExponent p d L : ℕ) : ℝ) < (p : ℝ) * (20 * (L : ℝ) / d) := by
  have hPred : ((p ^ (steepStartExponent p d L - 1) : ℕ) : ℝ) < 20 * (L : ℝ) / d := by
    apply lt_of_not_ge
    intro h
    have hBad := (steepStartExponent_le_iff hp).mpr h
    omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have h := mul_lt_mul_of_pos_left hPred hpR
  rw [show steepStartExponent p d L = (steepStartExponent p d L - 1) + 1 by omega,
    Nat.pow_succ, Nat.cast_mul]
  nlinarith

theorem steepEndExponent_bounds {p n1 : ℕ} (hp : 1 < p) (hn1 : 1 < n1) :
    p ^ steepEndExponent p n1 < n1 ∧ n1 ≤ p ^ (steepEndExponent p n1 + 1) := by
  have hLower := Nat.pow_log_le_self p (by omega : n1 - 1 ≠ 0)
  have hUpper := Nat.lt_pow_succ_log_self hp (n1 - 1)
  simp only [Nat.succ_eq_add_one] at hUpper
  unfold steepEndExponent
  constructor <;> omega

theorem terminalSteepSize_bounds {p n1 : ℕ} (hp : 1 ≤ p) (hn1 : 0 < n1) :
    0 < terminalSteepSize p n1 ∧ terminalSteepSize p n1 ≤ n1 ∧
      n1 ≤ p * terminalSteepSize p n1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hn1R : (0 : ℝ) < n1 := by exact_mod_cast hn1
  constructor
  · exact Nat.ceil_pos.mpr (div_pos hn1R hpR)
  constructor
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hpR).mpr
    have hP : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  · have h := (div_le_iff₀ hpR).mp (Nat.le_ceil ((n1 : ℝ) / p))
    have hReal : (n1 : ℝ) ≤ (p : ℝ) * terminalSteepSize p n1 := by
      change (n1 : ℝ) ≤ (p : ℝ) * (⌈(n1 : ℝ) / p⌉₊ : ℝ)
      nlinarith
    exact_mod_cast hReal

theorem steepScalePairs_bounds {p n1 r0 r : ℕ} (hp : 1 < p) (hn1 : 0 < n1)
    (hStart : r0 < r) (hEnd : p ^ r < n1) (a : ℕ × ℕ) (ha : a ∈ steepScalePairs p n1 r0 r) :
    0 < a.1 ∧ a.1 ≤ a.2 ∧ a.2 ≤ n1 ∧ a.2 ≤ p * a.1 ∧ p ^ r0 ≤ a.1 := by
  have hpPos : 0 < p := by omega
  rcases Finset.mem_union.mp ha with hGeom | hTerminal
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hGeom
    obtain ⟨hLo, hHi⟩ := Finset.mem_Ico.mp hi
    have hUpper := Nat.pow_le_pow_right hpPos (by omega : i + 1 ≤ r)
    have hLower := Nat.pow_le_pow_right hpPos hLo
    have hSize := Nat.pow_le_pow_right hpPos (Nat.le_succ i)
    exact ⟨Nat.pow_pos hpPos, hSize, hUpper.trans hEnd.le,
      by simp only [Nat.pow_succ, Nat.mul_comm, le_refl], hLower⟩
  · have hEq := Finset.mem_singleton.mp hTerminal
    subst a
    have hT := terminalSteepSize_bounds (by omega : 1 ≤ p) hn1
    have hLower := Nat.pow_le_pow_right hpPos (by omega : r0 + 1 ≤ r)
    have hProduct : p * p ^ r0 < p * terminalSteepSize p n1 := by
      rw [← Nat.pow_succ']
      exact hLower.trans_lt (hEnd.trans_le hT.2.2)
    have hLowerSize : p ^ r0 ≤ terminalSteepSize p n1 :=
      (Nat.lt_of_mul_lt_mul_left hProduct).le
    exact ⟨hT.1, hT.2.1, le_rfl, hT.2.2, hLowerSize⟩

theorem steepScalePairs_card_le {p n1 r0 : ℕ} (hn1 : 0 < n1) :
    (steepScalePairs p n1 r0 (steepEndExponent p n1)).card ≤ n1 := by
  have hUnion := Finset.card_union_le
    ((Finset.Ico r0 (steepEndExponent p n1)).image (fun i => (p ^ i, p ^ (i + 1))))
    {(terminalSteepSize p n1, n1)}
  have hImage := Finset.card_image_le
    (s := Finset.Ico r0 (steepEndExponent p n1)) (f := fun i => (p ^ i, p ^ (i + 1)))
  have hLog := Nat.log_le_self p (n1 - 1)
  rw [Finset.card_singleton] at hUnion
  rw [Nat.card_Ico] at hImage
  unfold steepScalePairs steepEndExponent at *
  omega

theorem sourceSteepScalePairs_second_le {n d L : ℕ} (hp : 1 < steepStride d)
    (hn1 : 1 < firstSteepScale n d) (a : ℕ × ℕ) (ha : a ∈ sourceSteepScalePairs n d L) :
    a.2 ≤ firstSteepScale n d := by
  rcases Finset.mem_union.mp ha with hGeom | hTerminal
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hGeom
    have hHi := (Finset.mem_Ico.mp hi).2
    have hPower := Nat.pow_le_pow_right (by omega : 0 < steepStride d)
      (by omega : i + 1 ≤ steepEndExponent (steepStride d) (firstSteepScale n d))
    exact hPower.trans (steepEndExponent_bounds hp hn1).1.le
  · have hEq := Finset.mem_singleton.mp hTerminal
    subst a
    exact le_refl _

end CircularLaw
