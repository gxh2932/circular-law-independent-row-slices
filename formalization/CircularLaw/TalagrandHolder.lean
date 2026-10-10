import CircularLaw.TalagrandFiniteProduct

/-!
# Weighted Holder interpolation for the Talagrand recursion

The interpolation parameter includes both endpoints. The finite weighted
Holder bound is proved by normalizing the two sums and applying weighted
AM-GM pointwise; the exponential version applies to the actual product law.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

variable {β : Type*} [Fintype β]

theorem weighted_holder_interpolation {ρ f g : β → ℝ} (hρ : ∀ x, 0 ≤ ρ x)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hA : 0 < ∑ x, ρ x * f x) (hB : 0 < ∑ x, ρ x * g x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ x, ρ x * (f x ^ a * g x ^ (1 - a))) ≤
      (∑ x, ρ x * f x) ^ a * (∑ x, ρ x * g x) ^ (1 - a) := by
  let A := ∑ x, ρ x * f x
  let B := ∑ x, ρ x * g x
  have hAn : A ≠ 0 := hA.ne'
  have hBn : B ≠ 0 := hB.ne'
  have hNormalized : (∑ x, ρ x * ((f x / A) ^ a * (g x / B) ^ (1 - a))) ≤ 1 := by
    calc
      _ ≤ ∑ x, ρ x * (a * (f x / A) + (1 - a) * (g x / B)) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left
          (Real.geom_mean_le_arith_mean2_weighted ha (sub_nonneg.mpr ha1)
            (div_nonneg (hf x) hA.le) (div_nonneg (hg x) hB.le) (by ring)) (hρ x)
      _ = ∑ x, ((a / A) * (ρ x * f x) + ((1 - a) / B) * (ρ x * g x)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = (a / A) * A + ((1 - a) / B) * B := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = a * A / A + (1 - a) * B / B := by ring
      _ = 1 := by simp [hAn, hBn]
  have hDenom : 0 < A ^ a * B ^ (1 - a) := mul_pos
    (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)
  have hIdentity : (∑ x, ρ x * ((f x / A) ^ a * (g x / B) ^ (1 - a))) =
      (∑ x, ρ x * (f x ^ a * g x ^ (1 - a))) / (A ^ a * B ^ (1 - a)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    rw [Real.div_rpow (hf x) hA.le, Real.div_rpow (hg x) hB.le, div_mul_div_comm]
    ring
  rw [hIdentity] at hNormalized
  simpa only [one_mul] using (div_le_iff₀ hDenom).mp hNormalized

variable {α : Type*} [Fintype α] {n : ℕ}

theorem finiteProductExpectation_exp_interpolation {μ : Fin n → α → ℝ}
    (hμ : ∀ i t, 0 ≤ μ i t) (hNorm : ∀ i, ∑ t, μ i t = 1)
    {f g : (Fin n → α) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    finiteProductExpectation μ (fun x => Real.exp (a * f x + (1 - a) * g x)) ≤
      finiteProductExpectation μ (fun x => Real.exp (f x)) ^ a *
        finiteProductExpectation μ (fun x => Real.exp (g x)) ^ (1 - a) := by
  have hA := lt_of_lt_of_le zero_lt_one (finiteProductExpectation_exp_ge_one hμ hNorm hf)
  have hB := lt_of_lt_of_le zero_lt_one (finiteProductExpectation_exp_ge_one hμ hNorm hg)
  have h := weighted_holder_interpolation (finiteProductWeight_nonneg hμ)
    (fun x => (Real.exp_pos (f x)).le) (fun x => (Real.exp_pos (g x)).le) hA hB ha ha1
  simpa only [finiteProductExpectation, Real.exp_add, mul_comm a, mul_comm (1 - a),
    Real.exp_mul] using h

end CircularLaw
