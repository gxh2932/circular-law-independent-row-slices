import CircularLaw.MaxWeight
import CircularLaw.Hypergeometric

/-!
# Dispersion from two separated probability tails

The two ordered rectangles of independent coordinates both contribute.
This proves the factor `2*p*q*gap` for the exact finite-coordinate law,
including integer-valued dyadic weight orders and coincident cutoffs.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem pairDispersion_two_tails {α : Type*} [Fintype α] (B : α → ℝ)
    (b₁ b₂ : ℝ) :
    2 * uniformProbability (fun a => B a ≤ b₁) * uniformProbability (fun a => b₂ ≤ B a) *
      (b₂ - b₁) ≤ pairDispersion B := by
  have hPoint (p : α × α) :
      (b₂ - b₁) *
        ((if B p.1 ≤ b₁ then (1 : ℝ) else 0) * (if b₂ ≤ B p.2 then (1 : ℝ) else 0) +
          (if b₂ ≤ B p.1 then (1 : ℝ) else 0) * (if B p.2 ≤ b₁ then (1 : ℝ) else 0)) ≤
        |B p.1 - B p.2| := by
    split_ifs <;> linarith [le_abs_self (B p.1 - B p.2), neg_le_abs (B p.1 - B p.2)]
  have h := finiteMean_mono hPoint
  rw [finiteMean_const_mul, finiteMean_add,
    finiteMean_prod (fun a => if B a ≤ b₁ then (1 : ℝ) else 0)
      (fun a => if b₂ ≤ B a then (1 : ℝ) else 0),
    finiteMean_prod (fun a => if b₂ ≤ B a then (1 : ℝ) else 0)
      (fun a => if B a ≤ b₁ then (1 : ℝ) else 0)] at h
  simp only [finiteMean_indicator] at h
  change (b₂ - b₁) *
    (uniformProbability (fun a => B a ≤ b₁) * uniformProbability (fun a => b₂ ≤ B a) +
      uniformProbability (fun a => b₂ ≤ B a) * uniformProbability (fun a => B a ≤ b₁)) ≤
    pairDispersion B at h
  nlinarith only [h]

theorem pairDispersion_two_tail_bound {α : Type*} [Fintype α] (B : α → ℝ)
    {b₁ b₂ p q g : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hg : 0 ≤ g)
    (hLow : p ≤ uniformProbability (fun a => B a ≤ b₁))
    (hHigh : q ≤ uniformProbability (fun a => b₂ ≤ B a)) (hGap : g ≤ b₂ - b₁) :
    2 * p * q * g ≤ pairDispersion B := by
  have hProb := mul_le_mul hLow hHigh hq (uniformProbability_nonneg _)
  have hBoth := mul_le_mul hProb hGap hg ((mul_nonneg hp hq).trans hProb)
  have hScaled := mul_le_mul_of_nonneg_left hBoth (by norm_num : (0 : ℝ) ≤ 2)
  have hResult := pairDispersion_two_tails B b₁ b₂
  nlinarith only [hScaled, hResult]

theorem pairDispersion_integer_two_tail_bound {α : Type*} [Fintype α] (B : α → ℤ)
    {b₁ b₂ : ℤ} {p q g : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hg : 0 ≤ g)
    (hLow : p ≤ uniformProbability (fun a => B a ≤ b₁))
    (hHigh : q ≤ uniformProbability (fun a => b₂ ≤ B a)) (hGap : g ≤ (b₂ : ℝ) - b₁) :
    2 * p * q * g ≤ pairDispersion (fun a => (B a : ℝ)) := by
  exact pairDispersion_two_tail_bound (fun a => (B a : ℝ))
    hp hq hg (by simpa only [Int.cast_le] using hLow)
    (by simpa only [Int.cast_le] using hHigh) hGap

end CircularLaw
