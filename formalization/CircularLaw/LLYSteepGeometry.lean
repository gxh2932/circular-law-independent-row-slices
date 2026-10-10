import CircularLaw.AlmostConstantGeometry

/-!
# Ordered jumps and a proved norm bound for the LLY gradual class

The first jump chain retains its terminal rank and the dense n1=1 case.
The second and third gaps are the source d^(3/4) and factor-four gaps.
A direct maximum-coordinate estimate gives a coarser explicit norm
constant; the sharper source norm constants are not assumed here.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def llyFirstRank (ℓ k i : ℕ) : ℕ := min (ℓ ^ i) k

def llyFirstSteep {n : ℕ} (d ℓ r k : ℕ) : Set (Fin n → ℂ) :=
  {x | ∃ i ∈ Finset.range (r + 1),
    6 * (d : ℝ) * orderedNormAt x (llyFirstRank ℓ k (i + 1)) <
      orderedNormAt x (llyFirstRank ℓ k i)}

def llySecondSteep {n : ℕ} (d ℓ r k₁ k₂ : ℕ) : Set (Fin n → ℂ) :=
  {x | x ∉ llyFirstSteep d ℓ r k₁ ∧
    (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt x k₂ < orderedNormAt x k₁}

def llyThirdSteep {n : ℕ} (d ℓ r k₁ k₂ k₃ : ℕ) : Set (Fin n → ℂ) :=
  {x | x ∉ llyFirstSteep d ℓ r k₁ ∧ x ∉ llySecondSteep d ℓ r k₁ k₂ ∧
    4 * orderedNormAt x k₃ < orderedNormAt x k₂}

def llySteepUnion {n : ℕ} (d ℓ r k₁ k₂ k₃ : ℕ) : Set (Fin n → ℂ) :=
  llyFirstSteep d ℓ r k₁ ∪ llySecondSteep d ℓ r k₁ k₂ ∪ llyThirdSteep d ℓ r k₁ k₂ k₃

def llyGradualNormConstant (n d r k₁ : ℕ) : ℝ :=
  4 * Real.sqrt n * (if k₁ = 1 then 1 else (6 * (d : ℝ)) ^ (r + 1)) *
    (d : ℝ) ^ (3 / 4 : ℝ)

theorem lly_first_rank_zero {ℓ k : ℕ} (hk : 0 < k) : llyFirstRank ℓ k 0 = 1 := by
  simp only [llyFirstRank, pow_zero, min_eq_left (by omega : 1 ≤ k)]

theorem lly_first_rank_terminal {ℓ r k : ℕ} (hFit : k ≤ ℓ ^ (r + 1)) :
    llyFirstRank ℓ k (r + 1) = k := min_eq_right hFit

theorem lly_not_first_steep_chain {n d ℓ r k : ℕ} (hk : 0 < k)
    (hFit : k ≤ ℓ ^ (r + 1)) (x : Fin n → ℂ) (hx : x ∉ llyFirstSteep d ℓ r k) :
    orderedNormAt x 1 ≤ (6 * (d : ℝ)) ^ (r + 1) * orderedNormAt x k := by
  have hChain : ∀ j : ℕ, j ≤ r + 1 →
      orderedNormAt x (llyFirstRank ℓ k 0) ≤
        (6 * (d : ℝ)) ^ j * orderedNormAt x (llyFirstRank ℓ k j) := by
    intro j
    induction j with
    | zero => intro _; simp only [pow_zero, one_mul, le_refl]
    | succ j ih =>
      intro hj
      have hStep : orderedNormAt x (llyFirstRank ℓ k j) ≤
          6 * (d : ℝ) * orderedNormAt x (llyFirstRank ℓ k (j + 1)) := by
        apply le_of_not_gt
        intro h
        exact hx ⟨j, Finset.mem_range.mpr (by omega), h⟩
      calc
        _ ≤ (6 * (d : ℝ)) ^ j * orderedNormAt x (llyFirstRank ℓ k j) := ih (by omega)
        _ ≤ (6 * (d : ℝ)) ^ j * (6 * d * orderedNormAt x (llyFirstRank ℓ k (j + 1))) :=
          mul_le_mul_of_nonneg_left hStep (by positivity)
        _ = _ := by rw [pow_succ]; ring
  simpa only [lly_first_rank_zero hk, lly_first_rank_terminal hFit] using hChain (r + 1) le_rfl

theorem lly_gradual_ordered_gaps {n d ℓ r k₁ k₂ k₃ : ℕ} (x : Fin n → ℂ)
    (hx : x ∉ llySteepUnion d ℓ r k₁ k₂ k₃) :
    x ∉ llyFirstSteep d ℓ r k₁ ∧
      orderedNormAt x k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt x k₂ ∧
      orderedNormAt x k₂ ≤ 4 * orderedNormAt x k₃ := by
  have hFirst : x ∉ llyFirstSteep d ℓ r k₁ := fun h => hx (Or.inl (Or.inl h))
  have hSecond : x ∉ llySecondSteep d ℓ r k₁ k₂ := fun h => hx (Or.inl (Or.inr h))
  have hThird : x ∉ llyThirdSteep d ℓ r k₁ k₂ k₃ := fun h => hx (Or.inr h)
  refine ⟨hFirst, le_of_not_gt (fun h => hSecond ⟨hFirst, h⟩),
    le_of_not_gt (fun h => hThird ⟨hFirst, hSecond, h⟩)⟩

theorem coordinate_norm_le_first_ordered {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) (j : Fin n) :
    ‖x j‖ ≤ orderedNormAt x 1 := by
  rw [orderedNormAt_eq x (by omega) (by omega)]
  have h := orderedNorm_antitone x (show (⟨0, hn⟩ : Fin n) ≤ (normOrderPerm x).symm j from
    Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
  simpa only [Nat.sub_self, orderedNorm_of_rank] using h

theorem euclidean_norm_le_first_ordered {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖x‖ ≤ Real.sqrt n * orderedNormAt (fun j => x j) 1 := by
  have hSq : ‖x‖ ^ 2 ≤ (n : ℝ) * (orderedNormAt (fun j => x j) 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply (Finset.sum_le_sum (fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (coordinate_norm_le_first_ordered hn _ j) 2)).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply (sq_le_sq₀ (norm_nonneg x) (mul_nonneg (Real.sqrt_nonneg _) (orderedNormAt_nonneg _ _))).mp
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] using hSq

theorem lly_gradual_norm_bound {n d ℓ r k₁ k₂ k₃ : ℕ} (hn : 0 < n) (hk₁ : 0 < k₁)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (x : EuclideanSpace ℂ (Fin n))
    (hx : (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃) :
    ‖x‖ ≤ llyGradualNormConstant n d r k₁ * orderedNormAt (fun j => x j) k₃ := by
  have hGaps := lly_gradual_ordered_gaps (fun j => x j) hx
  have hFirst : orderedNormAt (fun j => x j) 1 ≤
      (if k₁ = 1 then 1 else (6 * (d : ℝ)) ^ (r + 1)) * orderedNormAt (fun j => x j) k₁ := by
    split_ifs with hOne
    · simp only [hOne, one_mul, le_refl]
    · exact lly_not_first_steep_chain hk₁ hFit _ hGaps.1
  apply (euclidean_norm_le_first_ordered hn x).trans
  calc
    _ ≤ Real.sqrt n * ((if k₁ = 1 then 1 else (6 * (d : ℝ)) ^ (r + 1)) *
        ((d : ℝ) ^ (3 / 4 : ℝ) * (4 * orderedNormAt (fun j => x j) k₃))) := by
      gcongr
      exact hFirst.trans (mul_le_mul_of_nonneg_left
        (hGaps.2.1.trans (mul_le_mul_of_nonneg_left hGaps.2.2 (Real.rpow_nonneg (Nat.cast_nonneg d) _)))
        (by split_ifs <;> positivity))
    _ = _ := by unfold llyGradualNormConstant; ring

theorem lly_gradual_norm_constant_pos {n d r k₁ : ℕ} (hn : 0 < n) (hd : 0 < d) :
    0 < llyGradualNormConstant n d r k₁ := by
  unfold llyGradualNormConstant
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  split_ifs <;> positivity

end CircularLaw
