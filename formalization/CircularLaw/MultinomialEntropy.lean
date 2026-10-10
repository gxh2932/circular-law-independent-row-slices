import CircularLaw.EntropyCancellation
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Multinomial coefficients and histogram entropy

The weighted multinomial theorem gives the exact entropy upper bound for
factorial ratios. Zero-sized bins are allowed. This is the second inequality
in the manuscript's equation `eq:factorial-entropy`.
-/

noncomputable section
open Classical
open scoped BigOperators Nat

namespace CircularLaw

def multinomialEntropyExponent {ι : Type*} (S : Finset ι) (m : ι → ℕ) : ℝ :=
  -(∑ i ∈ S, (m i : ℝ) * Real.log ((m i : ℝ) / (∑ j ∈ S, m j : ℕ)))

theorem multinomial_weighted_term_le {ι : Type*} (S : Finset ι) (m : ι → ℕ) (p : ι → ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i) (hSupport : ∀ i, m i ≠ 0 → i ∈ S) :
    (Nat.multinomial S m : ℝ) * (∏ i ∈ S, p i ^ m i) ≤
      (∑ i ∈ S, p i) ^ (∑ i ∈ S, m i) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  apply Finset.single_le_sum
    (f := fun k : ι → ℕ => (Nat.multinomial S k : ℝ) * ∏ i ∈ S, p i ^ k i)
    (a := m)
  · intro f _
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i hi => pow_nonneg (hp i hi) _))
  · exact Finset.mem_piAntidiag.mpr ⟨rfl, hSupport⟩

theorem multinomial_normalized_weight_product {ι : Type*} (S : Finset ι) (m : ι → ℕ)
    (hN : 0 < ∑ i ∈ S, m i) :
    (∏ i ∈ S, ((m i : ℝ) / (∑ j ∈ S, m j : ℕ)) ^ m i) =
      Real.exp (-multinomialEntropyExponent S m) := by
  have hNR : (0 : ℝ) < (∑ i ∈ S, m i : ℕ) := by exact_mod_cast hN
  have hPoint : ∀ i ∈ S,
      ((m i : ℝ) / (∑ j ∈ S, m j : ℕ)) ^ m i =
        Real.exp ((m i : ℝ) * Real.log ((m i : ℝ) / (∑ j ∈ S, m j : ℕ))) := by
    intro i _
    by_cases hm : m i = 0
    · simp only [hm, Nat.cast_zero, pow_zero, zero_mul, Real.exp_zero]
    · have hmR : (0 : ℝ) < m i := by exact_mod_cast Nat.pos_of_ne_zero hm
      rw [Real.exp_nat_mul, Real.exp_log (div_pos hmR hNR)]
  calc
    _ = ∏ i ∈ S, Real.exp ((m i : ℝ) * Real.log ((m i : ℝ) / (∑ j ∈ S, m j : ℕ))) :=
      Finset.prod_congr rfl hPoint
    _ = Real.exp (-multinomialEntropyExponent S m) := by
      rw [← Real.exp_sum]
      simp only [multinomialEntropyExponent, neg_neg]

theorem multinomial_le_entropy_positive {ι : Type*} (S : Finset ι) (m : ι → ℕ)
    (hN : 0 < ∑ i ∈ S, m i) (hSupport : ∀ i, m i ≠ 0 → i ∈ S) :
    (Nat.multinomial S m : ℝ) ≤ Real.exp (multinomialEntropyExponent S m) := by
  have hNR : (0 : ℝ) < (∑ i ∈ S, m i : ℕ) := by exact_mod_cast hN
  have hMass : (∑ i ∈ S, (m i : ℝ) / (∑ j ∈ S, m j : ℕ)) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, div_self hNR.ne']
  have hTerm := multinomial_weighted_term_le S m
    (fun i => (m i : ℝ) / (∑ j ∈ S, m j : ℕ))
    (fun i _ => div_nonneg (Nat.cast_nonneg _) hNR.le) hSupport
  rw [hMass, one_pow, multinomial_normalized_weight_product S m hN] at hTerm
  calc
    (Nat.multinomial S m : ℝ) =
        ((Nat.multinomial S m : ℝ) * Real.exp (-multinomialEntropyExponent S m)) *
          Real.exp (multinomialEntropyExponent S m) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ 1 * Real.exp (multinomialEntropyExponent S m) :=
      mul_le_mul_of_nonneg_right hTerm (Real.exp_nonneg _)
    _ = _ := one_mul _

theorem multinomial_le_entropy {ι : Type*} (S : Finset ι) (m : ι → ℕ)
    (hSupport : ∀ i, m i ≠ 0 → i ∈ S) :
    (Nat.multinomial S m : ℝ) ≤ Real.exp (multinomialEntropyExponent S m) := by
  by_cases hN : (∑ i ∈ S, m i) = 0
  · have hm : ∀ i ∈ S, m i = 0 := Finset.sum_eq_zero_iff.mp hN
    have hProd : (∏ i ∈ S, (m i)!) = 1 :=
      Finset.prod_eq_one (fun i hi => by rw [hm i hi]; rfl)
    have hMult : Nat.multinomial S m = 1 := by
      simp only [Nat.multinomial, hN, Nat.factorial_zero, hProd, Nat.div_one]
    have hEntropy : multinomialEntropyExponent S m = 0 := by
      dsimp [multinomialEntropyExponent]
      rw [show (∑ i ∈ S, (m i : ℝ) * Real.log ((m i : ℝ) / (∑ j ∈ S, m j : ℕ))) = 0 by
        apply Finset.sum_eq_zero
        intro i hi
        simp only [hm i hi, Nat.cast_zero, zero_mul]]
      exact neg_zero
    simp only [hMult, Nat.cast_one, hEntropy, Real.exp_zero, le_refl]
  · exact multinomial_le_entropy_positive S m (Nat.pos_of_ne_zero hN) hSupport

theorem multinomial_cast_factorial_ratio {ι : Type*} (S : Finset ι) (m : ι → ℕ) :
    (Nat.multinomial S m : ℝ) =
      ((∑ i ∈ S, m i)! : ℝ) / (∏ i ∈ S, ((m i)! : ℝ)) := by
  have hProd : (0 : ℝ) < ∏ i ∈ S, ((m i)! : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos (m i))
  apply (eq_div_iff hProd.ne').mpr
  have hSpec : (∏ i ∈ S, ((m i)! : ℝ)) * (Nat.multinomial S m : ℝ) = ((∑ i ∈ S, m i)! : ℝ) := by
    exact_mod_cast Nat.multinomial_spec S m
  rwa [mul_comm] at hSpec

theorem factorial_ratio_le_entropy {ι : Type*} (S : Finset ι) (m : ι → ℕ)
    (hSupport : ∀ i, m i ≠ 0 → i ∈ S) :
    ((∑ i ∈ S, m i)! : ℝ) / (∏ i ∈ S, ((m i)! : ℝ)) ≤
      Real.exp (multinomialEntropyExponent S m) := by
  rw [← multinomial_cast_factorial_ratio]
  exact multinomial_le_entropy S m hSupport

end CircularLaw
