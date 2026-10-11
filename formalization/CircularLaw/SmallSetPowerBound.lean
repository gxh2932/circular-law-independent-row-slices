import CircularLaw.SmallSetEntropy
import Mathlib.Data.Nat.Choose.Bounds

/-!
# A power bound for all small coordinate supports

The family is the union of its exact-cardinality pieces. Bounding each
binomial coefficient by a power and summing the powers gives (n+1)^s.
This has no extra cost when the allowed support is empty.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem smallCoordinateSets_eq_biUnion (n s : ℕ) :
    smallCoordinateSets n s = (Finset.range (s + 1)).biUnion
      (fun t => (Finset.univ : Finset (Fin n)).powersetCard t) := by
  ext J
  simp only [mem_smallCoordinateSets, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · intro h
    exact ⟨J.card, by omega, rfl⟩
  · rintro ⟨t, ht, hJ⟩
    omega

theorem sum_natural_powers_le (n s : ℕ) :
    (∑ i ∈ Finset.range (s + 1), n ^ i) ≤ (n + 1) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, pow_succ, pow_succ]
    have hPower := Nat.mul_le_mul_left n (Nat.pow_le_pow_left (Nat.le_succ n) s)
    nlinarith

theorem smallCoordinateSets_card_power (n s : ℕ) :
    (smallCoordinateSets n s).card ≤ (n + 1) ^ s := by
  rw [smallCoordinateSets_eq_biUnion]
  apply Finset.card_biUnion_le.trans
  calc
    _ = ∑ i ∈ Finset.range (s + 1), n.choose i := by
      simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i ∈ Finset.range (s + 1), n ^ i :=
      Finset.sum_le_sum (fun i _ => Nat.choose_le_pow n i)
    _ ≤ _ := sum_natural_powers_le n s

end CircularLaw
