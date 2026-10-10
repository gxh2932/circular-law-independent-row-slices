import CircularLaw.LLYSteepGeometry

/-!
# Least-jump geometry for the first LLY steep class

The clipped terminal rank is retained. The first large jump is selected
from the actual ordered coordinates, and all earlier gaps give a checked
norm constant. No sharper source norm constant is assumed.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem lly_first_rank_pos {ℓ k : ℕ} (hℓ : 0 < ℓ) (hk : 0 < k) (i : ℕ) :
    0 < llyFirstRank ℓ k i := by
  exact lt_min (pow_pos hℓ i) hk

theorem lly_first_rank_le (ℓ k i : ℕ) : llyFirstRank ℓ k i ≤ k := min_le_right _ _

theorem lly_first_rank_mono {ℓ k : ℕ} (hℓ : 0 < ℓ) {i j : ℕ} (hij : i ≤ j) :
    llyFirstRank ℓ k i ≤ llyFirstRank ℓ k j := by
  exact min_le_min_right k (pow_le_pow_right' (by omega : 1 ≤ ℓ) hij)

theorem lly_first_rank_ratio {ℓ k : ℕ} (hℓ : 0 < ℓ) (i : ℕ) :
    llyFirstRank ℓ k (i + 1) ≤ ℓ * llyFirstRank ℓ k i := by
  unfold llyFirstRank
  by_cases h : ℓ ^ i ≤ k
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans_eq (by rw [pow_succ, Nat.mul_comm])
  · rw [min_eq_right (by omega : k ≤ ℓ ^ i)]
    exact (min_le_right _ _).trans (Nat.le_mul_of_pos_left k hℓ)

theorem lly_first_steep_rank_one_empty {n d ℓ r : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) :
    (llyFirstSteep d ℓ r 1 : Set (Fin n → ℂ)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, _, hJump⟩ := hx
  have hRank : ∀ j, llyFirstRank ℓ 1 j = 1 := fun j =>
    min_eq_right (by have h := pow_pos hℓ j; omega)
  rw [hRank i, hRank (i + 1)] at hJump
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hScaled := mul_le_mul_of_nonneg_right hdR (orderedNormAt_nonneg x 1)
  nlinarith [orderedNormAt_nonneg x 1]

theorem lly_first_scale_count {ℓ r k n : ℕ} (hℓ : 2 ≤ ℓ) (hRank : ℓ ^ r < k) (hkn : k ≤ n) :
    r + 1 ≤ n := by
  have hGrowth : ∀ i : ℕ, i + 1 ≤ ℓ ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ]
      nlinarith
  have h := hGrowth r
  omega

def llyFirstSteepNormConstant (n d r : ℕ) : ℝ := Real.sqrt n * (6 * (d : ℝ)) ^ r

theorem lly_first_steep_norm_constant_pos {n d r : ℕ} (hn : 0 < n) (hd : 0 < d) :
    0 < llyFirstSteepNormConstant n d r := by
  unfold llyFirstSteepNormConstant
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem lly_first_jump_norm_bound {n d ℓ r k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hk : 0 < k) (x : EuclideanSpace ℂ (Fin n))
    (hx : (fun j => x j) ∈ llyFirstSteep d ℓ r k) :
    ∃ i ∈ Finset.range (r + 1),
      6 * (d : ℝ) * orderedNormAt (fun j => x j) (llyFirstRank ℓ k (i + 1)) <
        orderedNormAt (fun j => x j) (llyFirstRank ℓ k i) ∧
      ‖x‖ ≤ llyFirstSteepNormConstant n d r *
        orderedNormAt (fun j => x j) (llyFirstRank ℓ k i) := by
  let P := fun i => i ∈ Finset.range (r + 1) ∧
    6 * (d : ℝ) * orderedNormAt (fun j => x j) (llyFirstRank ℓ k (i + 1)) <
      orderedNormAt (fun j => x j) (llyFirstRank ℓ k i)
  have hExists : ∃ i, P i := hx
  let i := Nat.find hExists
  have hi : P i := Nat.find_spec hExists
  have hEarlier : ∀ j < i,
      orderedNormAt (fun j => x j) (llyFirstRank ℓ k j) ≤
        6 * (d : ℝ) * orderedNormAt (fun j => x j) (llyFirstRank ℓ k (j + 1)) := by
    intro j hj
    apply le_of_not_gt
    intro hJump
    exact Nat.find_min hExists hj ⟨Finset.mem_range.mpr
      (by have h := Finset.mem_range.mp hi.1; omega), hJump⟩
  have hChain : ∀ j ≤ i,
      orderedNormAt (fun j => x j) (llyFirstRank ℓ k 0) ≤
        (6 * (d : ℝ)) ^ j * orderedNormAt (fun j => x j) (llyFirstRank ℓ k j) := by
    intro j
    induction j with
    | zero => intro _; simp only [pow_zero, one_mul, le_refl]
    | succ j ih =>
      intro hj
      calc
        _ ≤ (6 * (d : ℝ)) ^ j * orderedNormAt (fun j => x j) (llyFirstRank ℓ k j) := ih (by omega)
        _ ≤ (6 * (d : ℝ)) ^ j *
            (6 * (d : ℝ) * orderedNormAt (fun j => x j) (llyFirstRank ℓ k (j + 1))) :=
          mul_le_mul_of_nonneg_left (hEarlier j (by omega)) (by positivity)
        _ = _ := by rw [pow_succ]; ring
  have hPower : (6 * (d : ℝ)) ^ i ≤ (6 * (d : ℝ)) ^ r := by
    have h : (1 : ℝ) ≤ d := by exact_mod_cast hd
    apply pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 6 * d)
    have h := Finset.mem_range.mp hi.1
    omega
  refine ⟨i, hi.1, hi.2, ?_⟩
  apply (euclidean_norm_le_first_ordered hn x).trans
  have hTop := hChain i le_rfl
  rw [lly_first_rank_zero hk] at hTop
  unfold llyFirstSteepNormConstant
  calc
    _ ≤ Real.sqrt n * ((6 * (d : ℝ)) ^ i *
        orderedNormAt (fun j => x j) (llyFirstRank ℓ k i)) :=
      mul_le_mul_of_nonneg_left hTop (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt n * ((6 * (d : ℝ)) ^ r *
        orderedNormAt (fun j => x j) (llyFirstRank ℓ k i)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hPower (orderedNormAt_nonneg _ _)) (Real.sqrt_nonneg _)
    _ = _ := by ring

end CircularLaw
