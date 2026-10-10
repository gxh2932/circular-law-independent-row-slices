import CircularLaw.SteepStrideCubic
import CircularLaw.SourceNoSteep
import CircularLaw.SourceStartingRank

/-!
# Coordinate bounds from the actual no-jump chain

The terminal ceiling and every recursive geometric scale are retained.
Outside `T0` and `T3`, backward propagation controls all early ordered
moduli by the first steep-scale modulus. Cubic growth of the floor stride
then gives the weighted envelope used in the source net construction.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem source_terminal_modulus_bound {n d L : ℕ} (hp : 1 < steepStride d)
    (hn1 : 1 < firstSteepScale n d) (hFirst : firstSteepScale n d ≤ n)
    (hBefore : steepStartExponent (steepStride d) d L ≤
      steepEndExponent (steepStride d) (firstSteepScale n d))
    (x : Fin n → ℂ) (h₀ : x ∉ sourceT0 n d L) (h₃ : x ∉ sourceT3 n d L) :
    orderedNormAt x ((steepStride d) ^ steepEndExponent (steepStride d) (firstSteepScale n d)) ≤
      4 * (d : ℝ) * orderedNormAt x (firstSteepScale n d) := by
  let p := steepStride d
  let r := steepEndExponent p (firstSteepScale n d)
  have hEnd := steepEndExponent_bounds hp hn1
  have hTerminal := terminalSteepSize_bounds (by omega : 1 ≤ p) (by omega : 0 < firstSteepScale n d)
  have hTerminalLe : terminalSteepSize p (firstSteepScale n d) ≤ p ^ r := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by exact_mod_cast (by omega : 0 < p) : (0 : ℝ) < p)).mpr
    have hUpper : firstSteepScale n d ≤ p ^ r * p := by
      simpa only [Nat.pow_succ] using hEnd.2
    exact_mod_cast hUpper
  have hNorm := orderedNormAt_antitone x hTerminal.1 hTerminalLe (hEnd.1.le.trans hFirst)
  have hLast := source_no_T0_jump x hBefore (le_refl r) h₀ h₃
  have hr : r = steepEndExponent (steepStride d) (firstSteepScale n d) := rfl
  simp only [sourceSteepPairAt, ← hr, lt_self_iff_false, if_false] at hLast
  exact hNorm.trans hLast

theorem source_no_jump_chain {n d L : ℕ} (hp : 1 < steepStride d)
    (hn1 : 1 < firstSteepScale n d) (hFirst : firstSteepScale n d ≤ n)
    (hBefore : steepStartExponent (steepStride d) d L ≤
      steepEndExponent (steepStride d) (firstSteepScale n d))
    (x : Fin n → ℂ) (h₀ : x ∉ sourceT0 n d L) (h₃ : x ∉ sourceT3 n d L)
    (i : ℕ) (hLo : steepStartExponent (steepStride d) d L ≤ i)
    (hHi : i ≤ steepEndExponent (steepStride d) (firstSteepScale n d)) :
    orderedNormAt x ((steepStride d) ^ i) ≤
      4 * (d : ℝ) * (4 * (d : ℝ)) ^
        (steepEndExponent (steepStride d) (firstSteepScale n d) - i) *
          orderedNormAt x (firstSteepScale n d) := by
  let p := steepStride d
  let r := steepEndExponent p (firstSteepScale n d)
  have hLast : orderedNormAt x (p ^ r) ≤
      4 * (d : ℝ) * (4 * (d : ℝ)) ^ (r - r) * orderedNormAt x (firstSteepScale n d) := by
    simpa only [Nat.sub_self, pow_zero, mul_one] using
      source_terminal_modulus_bound hp hn1 hFirst hBefore x h₀ h₃
  have hStep : ∀ j < r, i ≤ j →
      orderedNormAt x (p ^ (j + 1)) ≤ 4 * (d : ℝ) * (4 * (d : ℝ)) ^ (r - (j + 1)) *
        orderedNormAt x (firstSteepScale n d) →
      orderedNormAt x (p ^ j) ≤ 4 * (d : ℝ) * (4 * (d : ℝ)) ^ (r - j) *
        orderedNormAt x (firstSteepScale n d) := by
    intro j hj hij hNext
    have hBound := source_no_T0_jump x (hLo.trans hij) hj.le h₀ h₃
    have hjSource : j < steepEndExponent (steepStride d) (firstSteepScale n d) := hj
    simp only [sourceSteepPairAt, if_pos hjSource] at hBound
    calc
      _ ≤ 4 * (d : ℝ) * orderedNormAt x (p ^ (j + 1)) := hBound
      _ ≤ 4 * (d : ℝ) * (4 * (d : ℝ) * (4 * (d : ℝ)) ^ (r - (j + 1)) *
          orderedNormAt x (firstSteepScale n d)) :=
        mul_le_mul_of_nonneg_left hNext (by positivity)
      _ = _ := by
        rw [show r - j = (r - (j + 1)) + 1 by omega, pow_succ]
        ring
  exact Nat.decreasingInduction' hStep hHi hLast

theorem source_weighted_no_jump_chain {n d L : ℕ} (hp : 1 < steepStride d)
    (hn1 : 1 < firstSteepScale n d) (hFirst : firstSteepScale n d ≤ n)
    (hBefore : steepStartExponent (steepStride d) d L ≤
      steepEndExponent (steepStride d) (firstSteepScale n d))
    (hCubic : 4 * d ≤ steepStride d ^ 3)
    (x : Fin n → ℂ) (h₀ : x ∉ sourceT0 n d L) (h₃ : x ∉ sourceT3 n d L)
    (i : ℕ) (hLo : steepStartExponent (steepStride d) d L ≤ i)
    (hHi : i ≤ steepEndExponent (steepStride d) (firstSteepScale n d)) :
    (((steepStride d) ^ i : ℕ) : ℝ) ^ 3 * orderedNormAt x ((steepStride d) ^ i) ≤
      4 * (d : ℝ) * (((steepStride d) ^
        steepEndExponent (steepStride d) (firstSteepScale n d) : ℕ) : ℝ) ^ 3 *
          orderedNormAt x (firstSteepScale n d) := by
  let p := steepStride d
  let r := steepEndExponent p (firstSteepScale n d)
  have hChain := source_no_jump_chain hp hn1 hFirst hBefore x h₀ h₃ i hLo hHi
  have hCubicR : 4 * (d : ℝ) ≤ (p : ℝ) ^ 3 := by exact_mod_cast hCubic
  have hPower := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 * d) hCubicR (r - i)
  have hProduct : ((p ^ i : ℕ) : ℝ) * ((p ^ (r - i) : ℕ) : ℝ) = (p ^ r : ℕ) := by
    rw [← Nat.cast_mul, ← pow_add, Nat.add_sub_of_le hHi]
  calc
    _ ≤ ((p ^ i : ℕ) : ℝ) ^ 3 *
        (4 * (d : ℝ) * (4 * (d : ℝ)) ^ (r - i) * orderedNormAt x (firstSteepScale n d)) :=
      mul_le_mul_of_nonneg_left hChain (by positivity)
    _ ≤ ((p ^ i : ℕ) : ℝ) ^ 3 *
        (4 * (d : ℝ) * ((p : ℝ) ^ 3) ^ (r - i) * orderedNormAt x (firstSteepScale n d)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (orderedNormAt_nonneg x _)
      exact mul_le_mul_of_nonneg_left hPower (by positivity)
    _ = 4 * (d : ℝ) * (((p ^ i : ℕ) : ℝ) * ((p ^ (r - i) : ℕ) : ℝ)) ^ 3 *
        orderedNormAt x (firstSteepScale n d) := by simp only [Nat.cast_pow]; ring
    _ = _ := by rw [hProduct]

theorem source_initial_modulus_bound {n d L : ℕ} (hp : 1 < steepStride d)
    (hn1 : 1 < firstSteepScale n d) (hFirst : firstSteepScale n d ≤ n)
    (hBefore : steepStartExponent (steepStride d) d L ≤
      steepEndExponent (steepStride d) (firstSteepScale n d))
    (hCubic : 4 * d ≤ steepStride d ^ 3)
    (x : Fin n → ℂ) (h₀ : x ∉ sourceT0 n d L) (h₃ : x ∉ sourceT3 n d L) :
    orderedNormAt x 1 ≤ 4 * (d : ℝ) * (n : ℝ) ^ 3 * (firstSteepScale n d : ℝ) ^ 3 *
      orderedNormAt x (firstSteepScale n d) := by
  let q := (steepStride d) ^ steepStartExponent (steepStride d) d L
  let r := steepEndExponent (steepStride d) (firstSteepScale n d)
  have hEnd := steepEndExponent_bounds hp hn1
  have hQPos : 0 < q := Nat.pow_pos (by omega : 0 < steepStride d)
  have hChain := source_weighted_no_jump_chain hp hn1 hFirst hBefore hCubic x h₀ h₃
    (steepStartExponent (steepStride d) d L) le_rfl hBefore
  have hQOne : (1 : ℝ) ≤ q := by exact_mod_cast hQPos
  have hQCube : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hQOne
  have hAtQ : orderedNormAt x q ≤ 4 * (d : ℝ) * ((steepStride d) ^ r : ℕ) ^ 3 *
      orderedNormAt x (firstSteepScale n d) := by
    have hScaled := mul_le_mul_of_nonneg_right hQCube (orderedNormAt_nonneg x q)
    simp only [one_mul] at hScaled
    exact hScaled.trans hChain
  have hAtOne : orderedNormAt x 1 ≤ (n : ℝ) ^ 3 * orderedNormAt x q := by
    apply le_of_not_gt
    intro hBad
    apply h₃
    refine ⟨1, by decide, by omega, ?_⟩
    simpa only [Nat.cast_one, div_one] using hBad
  have hFirstR : (((steepStride d) ^ r : ℕ) : ℝ) ≤ firstSteepScale n d := by
    exact_mod_cast hEnd.1.le
  have hPower := pow_le_pow_left₀ (Nat.cast_nonneg ((steepStride d) ^ r)) hFirstR 3
  have hAtQFirst : orderedNormAt x q ≤ 4 * (d : ℝ) * (firstSteepScale n d : ℝ) ^ 3 *
      orderedNormAt x (firstSteepScale n d) := by
    apply hAtQ.trans
    apply mul_le_mul_of_nonneg_right _ (orderedNormAt_nonneg x _)
    exact mul_le_mul_of_nonneg_left hPower (by positivity)
  calc
    _ ≤ (n : ℝ) ^ 3 * orderedNormAt x q := hAtOne
    _ ≤ (n : ℝ) ^ 3 * (4 * (d : ℝ) * (firstSteepScale n d : ℝ) ^ 3 *
        orderedNormAt x (firstSteepScale n d)) := mul_le_mul_of_nonneg_left hAtQFirst (by positivity)
    _ = _ := by ring

end CircularLaw
