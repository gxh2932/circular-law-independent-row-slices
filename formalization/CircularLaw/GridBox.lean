import CircularLaw.Discretization
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite complex grid boxes

Coordinatewise floor rounding lands in an explicitly counted finite
square. The integer ceiling is retained in the radius; no continuous
volume estimate substitutes for the actual grid cardinality.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def gridBox (k B : ℕ) : Finset ℂ :=
  ((Finset.Icc (-(B : ℤ)) (B : ℤ)) ×ˢ (Finset.Icc (-(B : ℤ)) (B : ℤ))).image
    (fun ab => gridValue k ab.1 ab.2)

def gridBoxRadius (k : ℕ) (R : ℝ) : ℕ := ⌈(k : ℝ) * R⌉₊ + 1

theorem gridBox_card_le (k B : ℕ) : (gridBox k B).card ≤ (2 * B + 1) ^ 2 := by
  apply (Finset.card_image_le).trans
  rw [Finset.card_product, Int.card_Icc]
  have hCount : ((B : ℤ) + 1 - -(B : ℤ)).toNat = 2 * B + 1 := by omega
  rw [hCount]
  simp only [pow_two, le_refl]

theorem zero_mem_gridBox (k B : ℕ) : (0 : ℂ) ∈ gridBox k B := by
  refine Finset.mem_image.mpr ⟨(0, 0), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  · simp only [gridValue, Int.cast_zero, zero_div]
    rfl

theorem floor_mem_grid_interval {k : ℕ} {R t : ℝ} (ht : |t| ≤ R) :
    ⌊(k : ℝ) * t⌋ ∈ Finset.Icc (-(gridBoxRadius k R : ℤ)) (gridBoxRadius k R : ℤ) := by
  have hBounds := abs_le.mp ht
  have hCeil : (k : ℝ) * R ≤ (gridBoxRadius k R : ℝ) := by
    have h := Nat.le_ceil ((k : ℝ) * R)
    simp only [gridBoxRadius, Nat.cast_add, Nat.cast_one]
    linarith
  have hLower : -(gridBoxRadius k R : ℝ) ≤ (k : ℝ) * t := by
    have h := mul_le_mul_of_nonneg_left hBounds.1 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith
  have hUpper : (⌊(k : ℝ) * t⌋ : ℝ) ≤ gridBoxRadius k R :=
    (Int.floor_le _).trans ((mul_le_mul_of_nonneg_left hBounds.2 (Nat.cast_nonneg k)).trans hCeil)
  apply Finset.mem_Icc.mpr
  constructor
  · apply Int.le_floor.mpr
    simpa only [Int.cast_neg, Int.cast_natCast] using hLower
  · exact_mod_cast hUpper

theorem canonicalApprox_mem_gridBox {k : ℕ} {R : ℝ} (z : ℂ) (hz : ‖z‖ ≤ R) :
    canonicalApprox k z ∈ gridBox k (gridBoxRadius k R) := by
  refine Finset.mem_image.mpr ⟨(⌊(k : ℝ) * z.re⌋, ⌊(k : ℝ) * z.im⌋), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨floor_mem_grid_interval ((Complex.abs_re_le_norm z).trans hz),
    floor_mem_grid_interval ((Complex.abs_im_le_norm z).trans hz)⟩

theorem gridBoxRadius_upper {k : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    (gridBoxRadius k R : ℝ) ≤ (k : ℝ) * R + 2 := by
  have h := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg k) hR)
  simp only [gridBoxRadius, Nat.cast_add, Nat.cast_one]
  linarith

end CircularLaw
