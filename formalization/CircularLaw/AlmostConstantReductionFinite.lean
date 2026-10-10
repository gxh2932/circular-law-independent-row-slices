import CircularLaw.AlmostConstantGeometry
import CircularLaw.SourceNoSteep

/-!
# Finite deterministic almost-constant reduction

This proves the manuscript's reduction from its actual coordinate count
and source steep classes. It treats a positive third-scale modulus and
the zero-tail case, without assuming any deterministic decomposition
theorem. Eventual compatibility of the ranks is proved separately.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem almostConstantRadius_bounds {d : ℕ} (hd : 6 ≤ d) :
    0 ≤ almostConstantRadius d ∧ almostConstantRadius d ≤ 1 / 20 ∧
      (d : ℝ) ^ 3 * almostConstantRadius d = 10 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hCube : (200 : ℝ) ≤ (d : ℝ) ^ 3 := by
    have h := Nat.pow_le_pow_left hd 3
    norm_num at h
    exact_mod_cast (by omega : 200 ≤ d ^ 3)
  unfold almostConstantRadius
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ (pow_pos hdR 3)).mpr
    linarith
  · field_simp

theorem almost_constant_reduction_finite {n d L : ℕ} (a₃ : ℝ) (hd : 6 ≤ d)
    (hp : 1 < steepStride d) (hn1 : 1 < firstSteepScale n d)
    (hRanks : firstSteepScale n d ≤ almostConstantRank n d ∧
      almostConstantRank n d ≤ thirdSteepScale n a₃)
    (hk : 0 < thirdSteepScale n a₃) (hHalf : 2 * thirdSteepScale n a₃ ≤ n)
    (hBefore : steepStartExponent (steepStride d) d L ≤
      steepEndExponent (steepStride d) (firstSteepScale n d))
    (x : Fin n → ℂ) (hNZ : x ≠ 0) (hB : x ∈ sourceAlmostConstant n d a₃)
    (hS : x ∉ sourceS n d a₃ 12) : x ∈ sourceShiftedSteepUnion n d L a₃ := by
  have hdPos : 0 < d := by omega
  have hkn : thirdSteepScale n a₃ ≤ n := by omega
  have h0n : almostConstantRank n d ≤ n := hRanks.2.trans hkn
  have hFirst : firstSteepScale n d ≤ n := hRanks.1.trans h0n
  have h0 : 0 < almostConstantRank n d := by omega
  have hRadius := almostConstantRadius_bounds hd
  obtain ⟨c, hMany⟩ := hB
  have hCenter := almost_constant_center_bounds hk hHalf x (almostConstantRadius d) c hMany
  have hTail := almost_constant_translated_tail hk hkn x (almostConstantRadius d) c hMany
  by_cases hPositive : 0 < orderedNormAt x (thirdSteepScale n a₃)
  · have hNorm0 := orderedNormAt_antitone x h0 hRanks.2 hkn
    have hPositive0 : 0 < orderedNormAt x (almostConstantRank n d) := hPositive.trans_le hNorm0
    have hLarge0 : 12 * orderedNormAt x (thirdSteepScale n a₃) <
        orderedNormAt x (almostConstantRank n d) := by
      apply lt_of_not_ge
      intro h
      exact hS ⟨hPositive0, h⟩
    let w : Fin n → ℂ := fun j => x j - c
    have hShift : orderedNormAt x (almostConstantRank n d) - ‖c‖ ≤
        orderedNormAt w (almostConstantRank n d) := by
      simpa only [sub_eq_add_neg, norm_neg] using
        (orderedNormAt_constant_shift x (-c) h0 h0n).2
    have hMonotone := orderedNormAt_antitone w (by omega : 0 < firstSteepScale n d) hRanks.1 h0n
    have hLarge : (11 - almostConstantRadius d) * orderedNormAt x (thirdSteepScale n a₃) <
        orderedNormAt w (firstSteepScale n d) := by nlinarith [hCenter.2]
    have hAllowed : ‖c‖ ≤ orderedNormAt w (firstSteepScale n d) / 10 := by
      nlinarith [hCenter.2, hRadius.2.1]
    have hTailScaled := mul_le_mul_of_nonneg_left hTail (pow_nonneg (Nat.cast_nonneg d) 3)
    have hGap : (d : ℝ) ^ 3 * orderedNormAt w (thirdSteepScale n a₃) <
        orderedNormAt w (firstSteepScale n d) := by
      calc
        _ ≤ (d : ℝ) ^ 3 * (almostConstantRadius d * orderedNormAt x (thirdSteepScale n a₃)) := hTailScaled
        _ = 10 * orderedNormAt x (thirdSteepScale n a₃) := by rw [← mul_assoc, hRadius.2.2]
        _ < _ := by nlinarith [hRadius.2.1]
    refine ⟨w, c, source_steep_union_of_large_gap hdPos a₃ w hGap, hAllowed, ?_⟩
    funext j
    exact (sub_add_cancel (x j) c).symm
  · have hZero : orderedNormAt x (thirdSteepScale n a₃) = 0 :=
      le_antisymm (le_of_not_gt hPositive) (orderedNormAt_nonneg x _)
    have hSteep : x ∈ sourceSteepUnion n d L a₃ := by
      by_cases hFirstPositive : 0 < orderedNormAt x (firstSteepScale n d)
      · apply source_steep_union_of_large_gap hdPos a₃ x
        simpa only [hZero, mul_zero] using hFirstPositive
      · have hFirstZero : orderedNormAt x (firstSteepScale n d) = 0 :=
          le_antisymm (le_of_not_gt hFirstPositive) (orderedNormAt_nonneg x _)
        rcases sourceT0_or_T3_of_first_scale_zero hp hn1 hFirst hBefore x hNZ hFirstZero with h0 | h3
        · exact Or.inl (Or.inl (Or.inl h0))
        · exact Or.inr h3
    refine ⟨x, 0, hSteep, ?_, ?_⟩
    · simp only [norm_zero]
      exact div_nonneg (orderedNormAt_nonneg x _) (by norm_num)
    · funext j
      exact (add_zero (x j)).symm

end CircularLaw
