import CircularLaw.LLYSteepGeometry

/-!
# Summing the first-jump scale costs without a global maximum cap

The geometric first ranks make the total weighted grid cost linear
in the terminal rank. This is needed for the second steep class:
charging its largest coordinate cap to every first-prefix coordinate
would leave an extra scale-count factor that cannot be absorbed.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def llyGeometricScaleCost (ℓ r c : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1), ℓ ^ i * (r + c - i)

def llyFirstNetScaleCost (ℓ r k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1), (llyFirstRank ℓ k (i + 1) - 1) * (r + 2 - i)

theorem lly_geometric_scale_cost_succ (ℓ r : ℕ) :
    llyGeometricScaleCost ℓ (r + 1) 1 = ℓ * llyGeometricScaleCost ℓ r 1 + (r + 2) := by
  unfold llyGeometricScaleCost
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.sub_zero, one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show r + 1 + 1 - (i + 1) = r + 1 - i by omega, pow_succ]
  ring

theorem lly_geometric_scale_cost_one_strong {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (r : ℕ) :
    llyGeometricScaleCost ℓ r 1 + (r + 3) ≤ 4 * ℓ ^ r := by
  induction r with
  | zero => simp [llyGeometricScaleCost]
  | succ r ih =>
    rw [lly_geometric_scale_cost_succ, pow_succ]
    have hScaled := Nat.mul_le_mul_left ℓ ih
    have hStride := Nat.mul_le_mul_right (r + 3) hℓ
    nlinarith

theorem lly_geometric_prefix_sum {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (r : ℕ) :
    (∑ i ∈ Finset.range (r + 1), ℓ ^ i) ≤ 2 * ℓ ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hStride := Nat.mul_le_mul_right (ℓ ^ r) hℓ
    nlinarith

theorem lly_geometric_scale_cost_bound {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (r : ℕ) {c : ℕ} (hc : 1 ≤ c) :
    llyGeometricScaleCost ℓ r c ≤ 2 * (c + 1) * ℓ ^ r := by
  have hIdentity : llyGeometricScaleCost ℓ r c = llyGeometricScaleCost ℓ r 1 +
      (c - 1) * (∑ i ∈ Finset.range (r + 1), ℓ ^ i) := by
    unfold llyGeometricScaleCost
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hiR : i ≤ r := by have h := Finset.mem_range.mp hi; omega
    rw [show r + c - i = (r + 1 - i) + (c - 1) by omega]
    ring
  rw [hIdentity]
  have hFirst := lly_geometric_scale_cost_one_strong hℓ r
  have hOther := Nat.mul_le_mul_left (c - 1) (lly_geometric_prefix_sum hℓ r)
  have hcEq : c - 1 + 1 = c := by omega
  nlinarith

theorem lly_first_net_scale_cost_bound {ℓ r k : ℕ} (hℓ : 2 ≤ ℓ) (hRank : ℓ ^ r ≤ k) :
    llyFirstNetScaleCost ℓ r k ≤ 10 * k := by
  cases r with
  | zero =>
    simp only [llyFirstNetScaleCost, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
      Nat.sub_zero]
    have hFirst : llyFirstRank ℓ k 1 - 1 ≤ k :=
      (Nat.sub_le _ _).trans (min_le_right _ _)
    nlinarith
  | succ r =>
    unfold llyFirstNetScaleCost
    rw [Finset.sum_range_succ]
    have hSum : (∑ i ∈ Finset.range (r + 1),
        (llyFirstRank ℓ k (i + 1) - 1) * (r + 1 + 2 - i)) ≤
          ℓ * llyGeometricScaleCost ℓ r 3 := by
      unfold llyGeometricScaleCost
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hFirst : llyFirstRank ℓ k (i + 1) - 1 ≤ ℓ ^ (i + 1) :=
        (Nat.sub_le _ _).trans (min_le_left _ _)
      have hScaled := Nat.mul_le_mul_right (r + 1 + 2 - i) hFirst
      convert hScaled using 1
      rw [pow_succ]
      ring
    have hLast : llyFirstRank ℓ k (r + 1 + 1) - 1 ≤ k :=
      (Nat.sub_le _ _).trans (min_le_right _ _)
    have hCost := Nat.mul_le_mul_left ℓ
      (lly_geometric_scale_cost_bound hℓ r (by norm_num : 1 ≤ (3 : ℕ)))
    rw [show r + 1 + 2 - (r + 1) = 2 by omega]
    rw [pow_succ] at hRank
    nlinarith

theorem lly_first_net_scale_cost_rank_one {ℓ r : ℕ} (hℓ : 0 < ℓ) :
    llyFirstNetScaleCost ℓ r 1 = 0 := by
  unfold llyFirstNetScaleCost
  apply Finset.sum_eq_zero
  intro i _
  have hPower : 1 ≤ ℓ ^ (i + 1) := by have h := pow_pos hℓ (i + 1); omega
  simp only [llyFirstRank, min_eq_right hPower, Nat.sub_self, zero_mul]

end CircularLaw
