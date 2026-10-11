import CircularLaw.CanonicalRow

/-!
# Single-summand bounds for constructed spread parts

Both spread-branch hypotheses are verified for the source construction,
using its actual heights, balanced level counts, and selected separated
values. These are inputs to the remaining sum-concentration imports.
-/

noncomputable section

namespace CircularLaw

theorem canonical_spread_part_atom {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ)
    (hPart : (spreadPart y j δ).Nonempty) (z : ℂ) :
    uniformProbability (fun i : {i : Fin n // i ∈ spreadPart y j δ} => y i.val = z) ≤
      4 / (((spreadValueSet y j δ).card : ℝ) + 3) := by
  haveI : Nonempty {i : Fin n // i ∈ spreadPart y j δ} := hPart.to_subtype
  simpa only [partLevel, Fintype.card_coe] using balanced_complex_atom_bound
    (α := {i : Fin n // i ∈ spreadPart y j δ})
    (β := {z : ℂ // z ∈ spreadValueSet y j δ})
    (partLevel y j (spreadValueSet y j δ)) (fun a => a.val) Subtype.val_injective
    (partLevel_balanced y j _ (spreadValueSet_subset y j δ)) z

theorem canonical_spread_part_atom_le_five_sixths {n d k : ℕ}
    (hd : 65536 ≤ d) (hk : 0 < k) (y : Fin n → ℂ) (j : ℕ)
    (hPart : (spreadPart y j ((d : ℝ) / (k : ℝ))).Nonempty) (z : ℂ) :
    uniformProbability (fun i : {i : Fin n // i ∈ spreadPart y j ((d : ℝ) / (k : ℝ))} =>
      ‖y i.val - z‖ ≤ Real.sqrt (d : ℝ) / (k : ℝ)) ≤ 5 / 6 := by
  have hδ : 0 < (d : ℝ) / (k : ℝ) := by
    apply div_pos
    · exact_mod_cast (by omega : 0 < d)
    · exact_mod_cast hk
  have hh : (2 : ℝ) ≤ (spreadValueSet y j ((d : ℝ) / (k : ℝ))).card :=
    by exact_mod_cast spreadPart_height_ge_two y j hδ hPart
  exact spread_atom_le_five_sixths
    (fun i : {i : Fin n // i ∈ spreadPart y j ((d : ℝ) / (k : ℝ))} => y i.val) hd hk hh
    (fun a b hab => spreadPart_values_separated y j _ a.property b.property hab)
    (canonical_spread_part_atom y j _ hPart) z

theorem canonical_spread_part_atom_le_half {n d k Q : ℕ}
    (hd : 65536 ≤ d) (hk : 0 < k) (y : Fin n → ℂ) (j : ℕ)
    (hPart : (spreadPart y j ((d : ℝ) / (k : ℝ))).Nonempty)
    (hh : (32 : ℝ) < (spreadValueSet y j ((d : ℝ) / (k : ℝ))).card)
    {τ : ℝ} (hτ : 0 ≤ τ) (hQ : Q ≤ d)
    (hsmall : τ ^ 2 ≤ ((spreadValueSet y j ((d : ℝ) / (k : ℝ))).card : ℝ) *
      Real.sqrt (Q : ℝ)) (z : ℂ) :
    uniformProbability (fun i : {i : Fin n // i ∈ spreadPart y j ((d : ℝ) / (k : ℝ))} =>
      ‖y i.val - z‖ ≤ τ * Real.sqrt (2 * (d : ℝ)) / (k : ℝ)) ≤ 1 / 2 := by
  have hhPos : (0 : ℝ) < (spreadValueSet y j ((d : ℝ) / (k : ℝ))).card := by linarith
  apply spread_atom_le_half
    (fun i : {i : Fin n // i ∈ spreadPart y j ((d : ℝ) / (k : ℝ))} => y i.val)
    hd hk hh hτ hQ hsmall
    (fun a b hab => spreadPart_values_separated y j _ a.property b.property hab) _ z
  intro w
  exact (canonical_spread_part_atom y j _ hPart w).trans
    (div_le_div_of_nonneg_left (by norm_num) hhPos (by linarith))

end CircularLaw
