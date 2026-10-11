import CircularLaw.CanonicalClassCardinality

/-!
# Entropy cancellation for the actual coordinate-multiset classes

The checked class cardinality and canonical factorial entropy bounds combine
without an assumed encoding or compression estimate. Multiplying by the
actual inverse truncated weights leaves precisely the source height/weight
product used in the structural class sum.
-/

noncomputable section
open Classical
open scoped BigOperators Nat

namespace CircularLaw

theorem orderedCanonicalClassIn_dispersion_cancel {n : ℕ} (hn : 0 < n)
    (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (δ : ℝ) {d : ℕ} (hd : 0 < d)
    {c K : ℝ} (hc : 0 < c) (hK : (n : ℝ) / 2 ≤ K) :
    (Nat.card (CoordinateMultisetClassIn A y) : ℝ) *
        Real.exp (-c * K * pairDispersion (fun a =>
          dyadicWeight (truncatedProfileWeight (orderedCanonicalRowProfile y δ) d
            ((orderedCanonicalRowProfile y δ).part a)))) ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) *
        (∏ q, ((orderedCanonicalRowProfile y δ).height q : ℝ) ^
          profilePartSize (orderedCanonicalRowProfile y δ) q) := by
  let P := orderedCanonicalRowProfile y δ
  let H : ℝ := ∏ q, (P.height q : ℝ) ^ profilePartSize P q
  let R : ℝ := ((n)! : ℝ) / ∏ q, ((profilePartSize P q)! : ℝ)
  let E : ℝ := Real.exp (-c * K * pairDispersion (fun a =>
    dyadicWeight (truncatedProfileWeight P d (P.part a))))
  have hH : 0 ≤ H := Finset.prod_nonneg (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _)
  have hCount : (Nat.card (CoordinateMultisetClassIn A y) : ℝ) ≤ R * H :=
    orderedCanonicalClassIn_cardinality A y δ
  have hEntropy : R * E ≤ Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) :=
    orderedCanonical_factorial_dispersion_cancel hn y δ hd hc hK
  change (Nat.card (CoordinateMultisetClassIn A y) : ℝ) * E ≤
    Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) * H
  calc
    _ ≤ (R * H) * E := mul_le_mul_of_nonneg_right hCount (Real.exp_pos _).le
    _ = (R * E) * H := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hEntropy hH

theorem orderedCanonicalClassIn_weighted_dispersion {n : ℕ} (hn : 0 < n)
    (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (δ : ℝ) {d : ℕ} (hd : 0 < d)
    {c K : ℝ} (hc : 0 < c) (hK : (n : ℝ) / 2 ≤ K) :
    (Nat.card (CoordinateMultisetClassIn A y) : ℝ) *
        (∏ q, (truncatedProfileWeight (orderedCanonicalRowProfile y δ) d q ^
          profilePartSize (orderedCanonicalRowProfile y δ) q)⁻¹) *
        Real.exp (-c * K * pairDispersion (fun a =>
          dyadicWeight (truncatedProfileWeight (orderedCanonicalRowProfile y δ) d
            ((orderedCanonicalRowProfile y δ).part a)))) ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) *
        (∏ q, ((orderedCanonicalRowProfile y δ).height q /
          truncatedProfileWeight (orderedCanonicalRowProfile y δ) d q) ^
          profilePartSize (orderedCanonicalRowProfile y δ) q) := by
  let P := orderedCanonicalRowProfile y δ
  let H : ℝ := ∏ q, (P.height q : ℝ) ^ profilePartSize P q
  let W : ℝ := ∏ q, (truncatedProfileWeight P d q ^ profilePartSize P q)⁻¹
  let E : ℝ := Real.exp (-c * K * pairDispersion (fun a =>
    dyadicWeight (truncatedProfileWeight P d (P.part a))))
  have hW : 0 ≤ W := Finset.prod_nonneg (fun q _ =>
    inv_nonneg.mpr (pow_nonneg (truncatedProfileWeight_pos P hd q).le _))
  have hProduct : H * W = ∏ q,
      ((P.height q : ℝ) / truncatedProfileWeight P d q) ^ profilePartSize P q := by
    rw [show H * W = (∏ q, (P.height q : ℝ) ^ profilePartSize P q) *
      (∏ q, (truncatedProfileWeight P d q ^ profilePartSize P q)⁻¹) from rfl,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q _
    rw [div_pow, div_eq_mul_inv]
  have hEntropy : (Nat.card (CoordinateMultisetClassIn A y) : ℝ) * E ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) * H :=
    orderedCanonicalClassIn_dispersion_cancel hn A y δ hd hc hK
  change (Nat.card (CoordinateMultisetClassIn A y) : ℝ) * W * E ≤ _
  calc
    _ = ((Nat.card (CoordinateMultisetClassIn A y) : ℝ) * E) * W := by ring
    _ ≤ (Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) * H) * W :=
      mul_le_mul_of_nonneg_right hEntropy hW
    _ = _ := by rw [mul_assoc, hProduct]

end CircularLaw
