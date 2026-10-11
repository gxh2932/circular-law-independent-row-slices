import CircularLaw.SourceGradualCoordinates

/-!
# A polynomial envelope at the normal rank

The literal starting rank is at least `20*L/d`. Applying the weighted
no-jump chain at that rank bounds its modulus by `d^16` for normalized
gradual vectors. Ordered moduli at every later valid rank inherit the
same bound, including the manuscript's floor normal rank.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem source_gradual_firstSteep_modulus {n d L : ℕ} {a₃ : ℝ}
    (hd : 0 < d) (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    orderedNormAt x (firstSteepScale n d) ≤ (d : ℝ) ^ 3 := by
  apply le_of_not_gt
  intro hBad
  apply hx.1
  apply source_steep_union_of_large_gap hd a₃ x
  simpa only [hx.2.2, mul_one] using hBad

theorem source_starting_rank_dimension_bound {n d L : ℕ}
    (hd : 0 < d) (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L)
    (hp : 1 < steepStride d) :
    2 * (n : ℝ) ≤
      (((steepStride d) ^ steepStartExponent (steepStride d) d L : ℕ) : ℝ) *
        (d : ℝ) ^ 4 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hStart := (div_le_iff₀ hdR).mp (steepStartExponent_lower (d := d) (L := L) hp)
  have hDimension := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ) ^ 3)).mp
    (kernelCodimension_bounds hd hn hL).1
  have hScaled := mul_le_mul_of_nonneg_right hStart (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 3)
  have hLPos : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  nlinarith only [hScaled, hDimension,
    mul_nonneg hLPos (pow_nonneg hdR.le 3)]

theorem source_gradual_starting_modulus {n d L : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3)
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    orderedNormAt x ((steepStride d) ^ steepStartExponent (steepStride d) d L) ≤
      (d : ℝ) ^ 16 := by
  let s := (steepStride d) ^ steepStartExponent (steepStride d) d L
  let r := steepEndExponent (steepStride d) (firstSteepScale n d)
  have hd : 0 < d := by have h := hConditions.degree_large; omega
  have hCubicDimension : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans
      hConditions.dimension_fourth
  have hRanks := source_starting_rank_bounds hConditions.degree_large
    hConditions.dimension_fourth hConditions.dimension_root hL
    hConditions.stride_pos hConditions.stride_upper
  have hSPos : 0 < s := Nat.pow_pos (by have h := hConditions.stride_pos; omega)
  have hSReal : (0 : ℝ) < s := by exact_mod_cast hSPos
  have hSOne : 1 < s := Nat.one_lt_pow (by omega :
      steepStartExponent (steepStride d) d L ≠ 0) hConditions.stride_pos
  have hn1 : 1 < firstSteepScale n d := hSOne.trans_le hRanks.2.1
  have h₀ : x ∉ sourceT0 n d L := fun h => hx.1 (Or.inl (Or.inl (Or.inl h)))
  have h₃ : x ∉ sourceT3 n d L := fun h => hx.1 (Or.inr h)
  have hChain := source_weighted_no_jump_chain hConditions.stride_pos hn1
    hRanks.2.2.1 hRanks.2.2.2.2.le hCubic x h₀ h₃
    (steepStartExponent (steepStride d) d L) le_rfl hRanks.2.2.2.2.le
  have hEnd : (steepStride d) ^ r ≤ n :=
    (steepEndExponent_bounds hConditions.stride_pos hn1).1.le.trans hRanks.2.2.1
  have hEndReal : (((steepStride d) ^ r : ℕ) : ℝ) ≤ n := by exact_mod_cast hEnd
  have hEndCube := pow_le_pow_left₀ (Nat.cast_nonneg ((steepStride d) ^ r)) hEndReal 3
  have hFirst := source_gradual_firstSteep_modulus hd x hx
  have hWeighted : (s : ℝ) ^ 3 * orderedNormAt x s ≤ 4 * (d : ℝ) ^ 4 * (n : ℝ) ^ 3 := by
    calc
      _ ≤ 4 * (d : ℝ) * (((steepStride d) ^ r : ℕ) : ℝ) ^ 3 *
          orderedNormAt x (firstSteepScale n d) := hChain
      _ ≤ 4 * (d : ℝ) * (((steepStride d) ^ r : ℕ) : ℝ) ^ 3 * (d : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hFirst (by positivity)
      _ ≤ 4 * (d : ℝ) * (n : ℝ) ^ 3 * (d : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEndCube (by positivity)) (by positivity)
      _ = _ := by ring
  have hDimension := source_starting_rank_dimension_bound hd hCubicDimension hL hConditions.stride_pos
  have hNCube := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)) hDimension 3
  have hScaled := mul_le_mul_of_nonneg_left hNCube (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4)
  have hBudget : 4 * (d : ℝ) ^ 4 * (n : ℝ) ^ 3 ≤ (s : ℝ) ^ 3 * (d : ℝ) ^ 16 := by
    dsimp only [s] at *
    nlinarith only [hScaled, mul_nonneg (pow_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) 4)
      (pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 3)]
  exact le_of_mul_le_mul_left (hWeighted.trans hBudget) (pow_pos hSReal 3)

theorem source_gradual_later_rank_modulus {n d L q : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3)
    (hRank : (steepStride d) ^ steepStartExponent (steepStride d) d L ≤ q)
    (hqn : q ≤ n) (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    orderedNormAt x q ≤ (d : ℝ) ^ 16 := by
  have hStartPos : 0 < (steepStride d) ^ steepStartExponent (steepStride d) d L :=
    Nat.pow_pos (by have h := hConditions.stride_pos; omega)
  exact (orderedNormAt_antitone x hStartPos hRank hqn).trans
    (source_gradual_starting_modulus hConditions hL hCubic x hx)

theorem eventually_source_normal_rank_modulus_uniform {C a : ℝ}
    (hC : 0 < C) (ha : 0 < a) (haOne : a ≤ 1) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
        0 < sourceNormalRank a L ∧ sourceNormalRank a L ≤ n ∧
          ∀ a₃ : ℝ, ∀ x ∈ sourceGradual n d L a₃,
            orderedNormAt x (sourceNormalRank a L) ≤ (d : ℝ) ^ 16 := by
  have hCast : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hRoot := (Real.tendsto_sqrt_atTop.comp hCast).eventually_ge_atTop (8 / a)
  have hSize := hCast.eventually_ge_atTop (1 / a)
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC eventually_steepStride_cubic,
    eventually_degree_property_uniform hC hRoot,
    eventually_degree_property_uniform hC hSize] with n hConditions hCubic hRoot hSize
  intro d hBand L hL
  have hCon := hConditions d hBand.1 hBand.2
  have hd : 0 < d := by have h := hCon.degree_large; omega
  have hRanks := source_starting_rank_bounds hCon.degree_large hCon.dimension_fourth
    hCon.dimension_root hL hCon.stride_pos hCon.stride_upper
  have hLReal : 2 * (d : ℝ) ≤ L := by
    exact_mod_cast kernelCodimension_large_lower hd hCon.dimension_fourth hL
  have hDScaled := (div_le_iff₀ ha).mp (hSize d hBand.1)
  have hLScaled := mul_le_mul_of_nonneg_left hLReal ha.le
  have hNormal := source_starting_rank_le_normal ha hd hCon.stride_pos hRanks.1
    hCon.stride_upper (hRoot d hBand.1) (by nlinarith : 2 ≤ a * (L : ℝ))
  have hCubicDimension : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  have hLn : L ≤ n := (kernelCodimension_quotient_bounds hd hCubicDimension hL).2.1.trans
    (Nat.div_le_self n (d ^ 3))
  have hqn := sourceNormalRank_le_dimension ha.le haOne hLn
  refine ⟨(Nat.pow_pos (by have h := hCon.stride_pos; omega :
    0 < steepStride d)).trans_le hNormal, hqn, ?_⟩
  intro a₃ x hx
  exact source_gradual_later_rank_modulus hCon hL (hCubic d hBand.1) hNormal hqn x hx

end CircularLaw
