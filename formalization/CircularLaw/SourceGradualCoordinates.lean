import CircularLaw.SourceCoordinateGrowth
import CircularLaw.SourceGradualNormalization
import CircularLaw.UniformSourceKernelConditions
import CircularLaw.AlmostConstantRanks

/-!
# Coordinate envelopes for the literal gradual class

The maximum-coordinate estimate is derived from the recursive no-jump
chain, the terminal ceiling, and the actual ceiling defining `n1`.
The tail estimate uses the literal `T2` exclusion. It applies to any
permutation sorting the original vector, including arbitrary tie choices.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem norm_le_first_orderedNormAt {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℂ) (j : Fin n) : ‖x j‖ ≤ orderedNormAt x 1 := by
  have hRank : (⟨0, hn⟩ : Fin n) ≤ (normOrderPerm x).symm j :=
    Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
  have h := orderedNorm_antitone x hRank
  rw [orderedNorm_of_rank, ← orderedNormAt_eq x (by decide : 0 < 1) (by omega : 1 ≤ n)] at h
  exact h

theorem norm_sorted_eq_orderedNorm {n : ℕ} (x : Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) (hσ : Antitone (fun i => ‖x (σ i)‖)) (j : Fin n) :
    ‖x (σ j)‖ = orderedNorm x j := by
  let f : Fin n → ℝ := fun i => ‖x i‖
  have hA : Antitone (f ∘ σ) := hσ
  have hB : Antitone (f ∘ normOrderPerm x) := orderedNorm_antitone x
  exact congrFun (Tuple.unique_antitone hA hB) j

theorem firstSteepScale_cubic_coefficient {n d : ℕ} (hd : 0 < d)
    (hDimension : (d : ℝ) * Real.sqrt d ≤ n) (hRoot : (32 : ℝ) ≤ Real.sqrt d) :
    4 * (d : ℝ) * (firstSteepScale n d : ℝ) ^ 3 * (d : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by
  have hDen : (0 : ℝ) < (d : ℝ) * Real.sqrt d := by positivity
  have hUpper := (le_div_iff₀ hDen).mp (firstSteepScale_upper hd hDimension)
  have hCube := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
    (firstSteepScale n d : ℝ) * ((d : ℝ) * Real.sqrt d)) hUpper 3
  have hIdentity : ((firstSteepScale n d : ℝ) * ((d : ℝ) * Real.sqrt d)) ^ 3 =
      Real.sqrt d * ((d : ℝ) ^ 4 * (firstSteepScale n d : ℝ) ^ 3) := by
    calc
      _ = (d : ℝ) ^ 3 * Real.sqrt d ^ 2 * Real.sqrt d *
          (firstSteepScale n d : ℝ) ^ 3 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg d)]; ring
  rw [hIdentity] at hCube
  have hScaled := mul_le_mul_of_nonneg_right hRoot
    (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4 * (firstSteepScale n d : ℝ) ^ 3)
  nlinarith

theorem source_gradual_first_modulus {n d L : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3)
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    orderedNormAt x 1 ≤ (n : ℝ) ^ 6 := by
  have hd : 0 < d := by have h := hConditions.degree_large; omega
  have hRanks := source_starting_rank_bounds hConditions.degree_large
    hConditions.dimension_fourth hConditions.dimension_root hL
    hConditions.stride_pos hConditions.stride_upper
  have hpPower : 1 < (steepStride d) ^ steepStartExponent (steepStride d) d L := by
    exact Nat.one_lt_pow (by omega : steepStartExponent (steepStride d) d L ≠ 0)
      hConditions.stride_pos
  have hn1 : 1 < firstSteepScale n d := hpPower.trans_le hRanks.2.1
  have h₀ : x ∉ sourceT0 n d L := fun h => hx.1 (Or.inl (Or.inl (Or.inl h)))
  have h₃ : x ∉ sourceT3 n d L := fun h => hx.1 (Or.inr h)
  have hFirst : orderedNormAt x (firstSteepScale n d) ≤ (d : ℝ) ^ 3 := by
    apply le_of_not_gt
    intro hBad
    apply hx.1
    apply source_steep_union_of_large_gap hd a₃ x
    simpa only [hx.2.2, mul_one] using hBad
  have hRoot : (32 : ℝ) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg (d : ℝ))).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    have hLarge := hConditions.degree_large
    exact_mod_cast (by omega : 32 ^ 2 ≤ d)
  have hCoefficient := firstSteepScale_cubic_coefficient hd hConditions.dimension_root hRoot
  calc
    _ ≤ 4 * (d : ℝ) * (n : ℝ) ^ 3 * (firstSteepScale n d : ℝ) ^ 3 *
        orderedNormAt x (firstSteepScale n d) :=
      source_initial_modulus_bound hConditions.stride_pos hn1 hRanks.2.2.1
        hRanks.2.2.2.2.le hCubic x h₀ h₃
    _ ≤ 4 * (d : ℝ) * (n : ℝ) ^ 3 * (firstSteepScale n d : ℝ) ^ 3 * (d : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = (n : ℝ) ^ 3 * (4 * (d : ℝ) * (firstSteepScale n d : ℝ) ^ 3 * (d : ℝ) ^ 3) := by ring
    _ ≤ (n : ℝ) ^ 3 * (n : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hCoefficient (by positivity)
    _ = _ := by ring

theorem source_gradual_second_modulus {n d L : ℕ} {a₃ : ℝ}
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    orderedNormAt x (secondSteepScale n d) ≤ Real.rpow (d : ℝ) (3 / 2) := by
  apply le_of_not_gt
  intro hBad
  apply hx.1
  refine Or.inl (Or.inr ⟨?_, ?_, ?_, ?_⟩)
  · exact fun h => hx.1 (Or.inl (Or.inl (Or.inl h)))
  · exact fun h => hx.1 (Or.inl (Or.inl (Or.inr h)))
  · exact fun h => hx.1 (Or.inr h)
  · simpa only [hx.2.2, mul_one] using hBad

theorem source_gradual_sorted_tail {n d L : ℕ} {a₃ : ℝ}
    (hk : 0 < secondSteepScale n d) (hkn : secondSteepScale n d ≤ n)
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃)
    (σ : Equiv.Perm (Fin n)) (hσ : Antitone (fun i => ‖x (σ i)‖))
    (j : Fin n) (hj : secondSteepScale n d ≤ j.val) :
    ‖x (σ j)‖ ≤ Real.rpow (d : ℝ) (3 / 2) := by
  rw [norm_sorted_eq_orderedNorm x σ hσ j]
  apply le_trans _ (source_gradual_second_modulus x hx)
  rw [orderedNormAt_eq x hk hkn]
  apply orderedNorm_antitone x
  apply Fin.le_iff_val_le_val.mpr
  change secondSteepScale n d - 1 ≤ j.val
  omega

end CircularLaw
