import CircularLaw.BernoulliSquareSmallExpansionProbability

/-!
# Summing the changing exposure seed

Each quotient j/B occurs at most B times. This bounds the whole
exposure schedule by one geometric series, uniformly in its length.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem quotient_range_fiber_card_le {B : ℕ} (hB : 0 < B) (L i : ℕ) :
    ((Finset.range L).filter (fun j => j / B = i)).card ≤ B := by
  let F := (Finset.range L).filter (fun j => j / B = i)
  have hInj : Set.InjOn (fun j : ℕ => j % B) (F : Set ℕ) := by
    intro a ha b hb hab
    change a % B = b % B at hab
    have haQ := (Finset.mem_filter.mp
      (show a ∈ (Finset.range L).filter (fun j => j / B = i) from ha)).2
    have hbQ := (Finset.mem_filter.mp
      (show b ∈ (Finset.range L).filter (fun j => j / B = i) from hb)).2
    have haEq := Nat.mod_add_div a B
    have hbEq := Nat.mod_add_div b B
    rw [haQ] at haEq
    rw [hbQ] at hbEq
    rw [hab] at haEq
    omega
  have hSubset : F.image (fun j => j % B) ⊆ Finset.range B := by
    intro j hj
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (Nat.mod_lt a hB)
  calc
    _ = (F.image (fun j => j % B)).card := (Finset.card_image_of_injOn hInj).symm
    _ ≤ (Finset.range B).card := Finset.card_le_card hSubset
    _ = B := Finset.card_range B

theorem blocked_geometric_sum_le {B : ℕ} (hB : 0 < B) {q : ℝ}
    (hq : 0 ≤ q) (hqHalf : q ≤ 1 / 2) (L : ℕ) :
    (∑ j ∈ Finset.range L, q ^ (j / B + 1)) ≤ 2 * B * q := by
  have hMap : ∀ j ∈ Finset.range L, j / B ∈ Finset.range (L + 1) := by
    intro j hj
    have hJ := Finset.mem_range.mp hj
    have hDiv := Nat.div_le_self j B
    exact Finset.mem_range.mpr (by omega)
  have hFiber (i : ℕ) :
      (∑ j ∈ (Finset.range L).filter (fun j => j / B = i), q ^ (j / B + 1)) ≤
        (B : ℝ) * q ^ (i + 1) := by
    calc
      _ = (∑ _j ∈ (Finset.range L).filter (fun j => j / B = i), q ^ (i + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [(Finset.mem_filter.mp hj).2]
      _ = (((Finset.range L).filter (fun j => j / B = i)).card : ℝ) * q ^ (i + 1) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast quotient_range_fiber_card_le hB L i)
        (pow_nonneg hq _)
  calc
    _ = ∑ i ∈ Finset.range (L + 1),
        ∑ j ∈ (Finset.range L).filter (fun j => j / B = i), q ^ (j / B + 1) :=
      (Finset.sum_fiberwise_of_maps_to hMap (fun j => q ^ (j / B + 1))).symm
    _ ≤ ∑ i ∈ Finset.range (L + 1), (B : ℝ) * q ^ (i + 1) :=
      Finset.sum_le_sum (fun i _ => hFiber i)
    _ = ((B : ℝ) * q) * ∑ i ∈ Finset.range (L + 1), q ^ i := by
      simp_rw [pow_succ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (geometric_nonnegative_powers_sum_le_two hq hqHalf (L + 1))
        (mul_nonneg (Nat.cast_nonneg B) hq)
      nlinarith

theorem source_expansion_seed_exponential_sum_le {d : ℝ}
    (hd : 16 ≤ d) (L : ℕ) :
    (∑ j ∈ Finset.range L, Real.exp (-d * ((j / 32768 + 1 : ℕ) : ℝ) / 16)) ≤
      65536 * Real.exp (-d / 16) := by
  have hHalf : Real.exp (-d / 16) ≤ 1 / 2 := by
    apply (Real.exp_le_exp.mpr (by linarith : -d / 16 ≤ -1)).trans
    exact Real.exp_neg_one_lt_half.le
  have hPoint (j : ℕ) : Real.exp (-d * ((j / 32768 + 1 : ℕ) : ℝ) / 16) =
      (Real.exp (-d / 16)) ^ (j / 32768 + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [hPoint]
  simpa only [Nat.cast_ofNat, show (2 : ℝ) * 32768 = 65536 by norm_num] using
    blocked_geometric_sum_le (by norm_num : (0 : ℕ) < 32768) (Real.exp_pos _).le hHalf L

theorem shifted_source_expansion_seed_exponential_sum_le {d : ℝ}
    (hd : 16 ≤ d) (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), Real.exp (-d * (((j - 1) / 32768 + 1 : ℕ) : ℝ) / 16)) ≤
      65537 * Real.exp (-d / 16) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_sub, Nat.zero_div, zero_add, Nat.cast_one, mul_one, Nat.add_sub_cancel]
  have h := source_expansion_seed_exponential_sum_le hd L
  linarith

end CircularLaw
