import CircularLaw.SourceSteepClasses
import CircularLaw.OrderedNormStability

/-!
# The permitted shifted very-steep class

The source constant `0.9` is obtained from actual order-statistic
stability. No agreement of coordinate orderings under a constant shift
is assumed. Monotonicity then transfers the witness to a larger rank.
-/

noncomputable section
open Classical

namespace CircularLaw

def sourceShiftedT3 (n d L : ℕ) : Set (Fin n → ℂ) :=
  {v | ∃ (x : Fin n → ℂ) (c : ℂ), x ∈ sourceT3 n d L ∧
    ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10 ∧ v = fun j => x j + c}

def sourceVerySteep (n q : ℕ) : Set (Fin n → ℂ) :=
  {v | v ≠ 0 ∧ ∃ i : ℕ, 0 < i ∧ i ≤ q ∧
    (9 / 10 : ℝ) * ((n : ℝ) / i) ^ 3 * orderedNormAt v q < orderedNormAt v i}

theorem orderedNormAt_zero (n k : ℕ) : orderedNormAt (0 : Fin n → ℂ) k = 0 := by
  unfold orderedNormAt
  split <;> simp only [orderedNorm, Pi.zero_apply, norm_zero]

theorem steep_shift_numeric {A a b c u v : ℝ} (hA : 10 < A) (hb : 0 ≤ b)
    (hc : c ≤ b / 10) (hJump : A * b < a) (hLower : a - c ≤ u) (hUpper : v ≤ b + c) :
    (9 / 10 : ℝ) * A * v < u := by
  have hA0 : 0 ≤ A := by linarith
  have hHigh := mul_le_mul_of_nonneg_left hUpper (by positivity : (0 : ℝ) ≤ (9 / 10 : ℝ) * A)
  have hCenter := mul_le_mul_of_nonneg_left hc hA0
  have hBase := mul_le_mul_of_nonneg_right hA.le hb
  nlinarith

theorem sourceT3_constant_shift_witness {n d L : ℕ}
    (hRanks : (steepStride d) ^ steepStartExponent (steepStride d) d L ≤ firstSteepScale n d)
    (hFirst : firstSteepScale n d ≤ n)
    (hRatio : 4 * (steepStride d) ^ steepStartExponent (steepStride d) d L ≤ n)
    (v : Fin n → ℂ) (hv : v ∈ sourceShiftedT3 n d L) :
    v ∈ sourceVerySteep n ((steepStride d) ^ steepStartExponent (steepStride d) d L) := by
  obtain ⟨x, c, hx, hCenter, rfl⟩ := hv
  obtain ⟨i, hi, hiq, hJump⟩ := hx
  let q := (steepStride d) ^ steepStartExponent (steepStride d) d L
  have hq : 0 < q := by omega
  have hqn : q ≤ n := hRanks.trans hFirst
  have hin : i ≤ n := hiq.trans hqn
  have hRefCenter : ‖c‖ ≤ orderedNormAt x q / 10 :=
    hCenter.trans (div_le_div_of_nonneg_right (orderedNormAt_antitone x hq hRanks hFirst)
      (by norm_num))
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hFour : (4 : ℝ) ≤ (n : ℝ) / i := by
    apply (le_div_iff₀ hiR).mpr
    exact_mod_cast ((Nat.mul_le_mul_left 4 hiq).trans hRatio)
  have hCube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hFour 3
  have hFactor : (10 : ℝ) < ((n : ℝ) / i) ^ 3 := by norm_num at hCube; linarith
  have hAtI := (orderedNormAt_constant_shift x c hi hin).2
  have hAtQ := (orderedNormAt_constant_shift x c hq hqn).1
  have hNew := steep_shift_numeric hFactor (orderedNormAt_nonneg x q) hRefCenter
    hJump hAtI hAtQ
  have hNZ : (fun j => x j + c) ≠ (0 : Fin n → ℂ) := by
    intro hZero
    rw [hZero, orderedNormAt_zero, orderedNormAt_zero] at hNew
    simp only [mul_zero, lt_self_iff_false] at hNew
  exact ⟨hNZ, i, hi, hiq, hNew⟩

theorem sourceVerySteep_mono_rank {n q r : ℕ} (hqr : q ≤ r) (hrn : r ≤ n)
    (v : Fin n → ℂ) (hv : v ∈ sourceVerySteep n q) : v ∈ sourceVerySteep n r := by
  obtain ⟨hNZ, i, hi, hiq, hJump⟩ := hv
  have hq : 0 < q := by omega
  have hNorm := orderedNormAt_antitone v hq hqr hrn
  have hFactor : (0 : ℝ) ≤ (9 / 10 : ℝ) * ((n : ℝ) / i) ^ 3 := by positivity
  exact ⟨hNZ, i, hi, hiq.trans hqr, (mul_le_mul_of_nonneg_left hNorm hFactor).trans_lt hJump⟩

end CircularLaw
