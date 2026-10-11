import CircularLaw.SourceSteepClasses
import CircularLaw.PermittedSteepShift

/-!
# Consequences of the recursive exclusions

A strict raw jump outside `T3` belongs to its first applicable `T0`
class. Thus a nonzero vector with zero first-scale modulus is in `T0`
or `T3`, including supports below the starting rank or terminal ceiling.
The proof propagates zero moduli through the actual scale chain.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem sourceT0_of_jump_not_T3 {n d L i : ℕ} (x : Fin n → ℂ)
    (hLo : steepStartExponent (steepStride d) d L ≤ i)
    (hHi : i ≤ steepEndExponent (steepStride d) (firstSteepScale n d))
    (h3 : x ∉ sourceT3 n d L) (hJump : sourceT0JumpAt n d i x) :
    x ∈ sourceT0 n d L := by
  by_cases hPrev : x ∈ sourceT0Previous n d L i
  · rcases (mem_sourceT0Previous x).mp hPrev with h3Bad | ⟨j, _, hx⟩
    · exact (h3 h3Bad).elim
    · exact ⟨j, Finset.mem_Icc.mpr ⟨hx.1, hx.2.1⟩, hx⟩
  · exact ⟨i, Finset.mem_Icc.mpr ⟨hLo, hHi⟩, hLo, hHi, hPrev, hJump⟩

theorem source_no_T0_jump {n d L i : ℕ} (x : Fin n → ℂ)
    (hLo : steepStartExponent (steepStride d) d L ≤ i)
    (hHi : i ≤ steepEndExponent (steepStride d) (firstSteepScale n d))
    (h0 : x ∉ sourceT0 n d L) (h3 : x ∉ sourceT3 n d L) :
    orderedNormAt x (sourceSteepPairAt n d i).1 ≤
      4 * (d : ℝ) * orderedNormAt x (sourceSteepPairAt n d i).2 := by
  exact le_of_not_gt (fun h => h0 (sourceT0_of_jump_not_T3 x hLo hHi h3 h))

theorem vector_eq_zero_of_first_orderedNorm_zero {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℂ) (hZero : orderedNormAt x 1 = 0) : x = 0 := by
  funext j
  have hRank : (⟨0, hn⟩ : Fin n) ≤ (normOrderPerm x).symm j :=
    Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
  have hNorm := orderedNorm_antitone x hRank
  rw [orderedNorm_of_rank, ← orderedNormAt_eq x (by decide : 0 < 1) (by omega : 1 ≤ n),
    hZero] at hNorm
  exact norm_eq_zero.mp (le_antisymm hNorm (norm_nonneg _))

theorem sourceT0_or_T3_of_first_scale_zero {n d L : ℕ} (hp : 1 < steepStride d)
    (hn1 : 1 < firstSteepScale n d) (hFirst : firstSteepScale n d ≤ n)
    (hBefore : steepStartExponent (steepStride d) d L ≤
      steepEndExponent (steepStride d) (firstSteepScale n d))
    (x : Fin n → ℂ) (hNZ : x ≠ 0) (hZero : orderedNormAt x (firstSteepScale n d) = 0) :
    x ∈ sourceT0 n d L ∨ x ∈ sourceT3 n d L := by
  by_contra h
  have h0 : x ∉ sourceT0 n d L := fun hx => h (Or.inl hx)
  have h3 : x ∉ sourceT3 n d L := fun hx => h (Or.inr hx)
  let p := steepStride d
  let r := steepEndExponent p (firstSteepScale n d)
  let r0 := steepStartExponent p d L
  have hpPos : 0 < p := by omega
  have hEnd := steepEndExponent_bounds hp hn1
  have hPowerRn : p ^ r ≤ n := hEnd.1.le.trans hFirst
  have hTerminal := terminalSteepSize_bounds (by omega : 1 ≤ p) (by omega : 0 < firstSteepScale n d)
  have hTerminalLe : terminalSteepSize p (firstSteepScale n d) ≤ p ^ r := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by exact_mod_cast hpPos : (0 : ℝ) < p)).mpr
    have hUpper : firstSteepScale n d ≤ p ^ r * p := by
      simpa only [Nat.pow_succ] using hEnd.2
    exact_mod_cast hUpper
  have hLast := source_no_T0_jump x hBefore (le_refl r) h0 h3
  simp only [sourceSteepPairAt, lt_self_iff_false, if_false] at hLast
  rw [hZero, mul_zero] at hLast
  have hTerminalZero : orderedNormAt x (terminalSteepSize p (firstSteepScale n d)) = 0 :=
    le_antisymm hLast (orderedNormAt_nonneg x _)
  have hTopZero : orderedNormAt x (p ^ r) = 0 := by
    have hNorm := orderedNormAt_antitone x hTerminal.1 hTerminalLe hPowerRn
    rw [hTerminalZero] at hNorm
    exact le_antisymm hNorm (orderedNormAt_nonneg x _)
  have hStep : ∀ k < r, r0 ≤ k →
      orderedNormAt x (p ^ (k + 1)) = 0 → orderedNormAt x (p ^ k) = 0 := by
    intro k hk hLo hNext
    have hBound := source_no_T0_jump x hLo hk.le h0 h3
    have hkSource : k < steepEndExponent (steepStride d) (firstSteepScale n d) := hk
    simp only [sourceSteepPairAt, if_pos hkSource] at hBound
    rw [hNext, mul_zero] at hBound
    exact le_antisymm hBound (orderedNormAt_nonneg x _)
  have hStartZero : orderedNormAt x (p ^ r0) = 0 :=
    Nat.decreasingInduction' (P := fun k => orderedNormAt x (p ^ k) = 0) hStep hBefore hTopZero
  have hqPos : 0 < p ^ r0 := Nat.pow_pos hpPos
  have hFirstBound : orderedNormAt x 1 ≤ ((n : ℝ) / 1) ^ 3 * orderedNormAt x (p ^ r0) := by
    apply le_of_not_gt
    intro hx
    apply h3
    refine ⟨1, by decide, Nat.succ_le_iff.mpr hqPos, ?_⟩
    simpa only [Nat.cast_one] using hx
  rw [hStartZero, mul_zero] at hFirstBound
  have hFirstZero := le_antisymm hFirstBound (orderedNormAt_nonneg x 1)
  exact hNZ (vector_eq_zero_of_first_orderedNorm_zero (by omega : 0 < n) x hFirstZero)

end CircularLaw
