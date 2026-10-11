import CircularLaw.SpreadBlock
import CircularLaw.CanonicalSpread

/-!
# Checked sum estimates for the canonical spread parts

The generic spread estimate is specialized to the constructed separated
values and balanced counts, then transported to the exact profile fiber.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

theorem canonical_spread_part_small_ball {n d k m : ℕ}
    (hd : 65536 ≤ d) (hk : 0 < k) (hm : 1 ≤ m) (hmd : m ≤ d)
    (y : Fin n → ℂ) (j : ℕ)
    (hPart : (spreadPart y j ((d : ℝ) / (k : ℝ))).Nonempty)
    {τ : ℝ} (hτ : 1 ≤ τ) (z : ℂ) :
    uniformProbability (fun x : Fin m →
      {i : Fin n // i ∈ spreadPart y j ((d : ℝ) / (k : ℝ))} =>
        ‖(∑ a, y (x a).val) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) ≤
      spreadBlockConstant * τ ^ 2 *
        (((spreadValueSet y j ((d : ℝ) / (k : ℝ))).card : ℝ) * Real.sqrt (m : ℝ))⁻¹ := by
  haveI : Nonempty {i : Fin n // i ∈ spreadPart y j ((d : ℝ) / (k : ℝ))} := hPart.to_subtype
  have hδ : 0 < (d : ℝ) / (k : ℝ) := by
    apply div_pos
    · exact_mod_cast (show 0 < d by omega)
    · exact_mod_cast hk
  apply spread_uniform_block_small_ball
    (fun i : {i : Fin n // i ∈ spreadPart y j ((d : ℝ) / (k : ℝ))} => y i.val)
    hd hk hm hmd
    (by exact_mod_cast spreadPart_height_ge_two y j hδ hPart) hτ
    (fun a b hab => spreadPart_values_separated y j _ a.property b.property hab)
  exact canonical_spread_part_atom y j _ hPart

def canonicalSpreadFiberEquiv {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (q : CanonicalLabel y δ) (hq : q.val.1 = true) :
    {i : Fin n // (canonicalRowProfile y δ).part i = q} ≃
      {i : Fin n // i ∈ spreadPart y q.val.2.val δ} :=
  Equiv.subtypeEquivRight (fun i => by
    simpa only [taggedPart, taggedValues, hq, ↓reduceIte, spreadPart] using
      canonicalCoordinateLabel_eq_iff y δ i q)

theorem canonical_spread_profile_block_small_ball {n k m d : ℕ}
    (hd : 65536 ≤ d) (hk : 0 < k) (hm : 1 ≤ m) (hmd : m ≤ d)
    (y : Fin n → ℂ) (q : CanonicalLabel y ((d : ℝ) / (k : ℝ))) (hq : q.val.1 = true)
    {τ : ℝ} (hτ : 1 ≤ τ) (z : ℂ) :
    uniformProbability (fun x : Fin m →
      {i : Fin n // (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part i = q} =>
        ‖(∑ a, y (x a).val) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) ≤
      spreadBlockConstant * τ ^ 2 *
        (((canonicalRowProfile y ((d : ℝ) / (k : ℝ))).height q : ℝ) * Real.sqrt (m : ℝ))⁻¹ := by
  let δ := (d : ℝ) / (k : ℝ)
  let e := Equiv.piCongrRight (fun _ : Fin m => canonicalSpreadFiberEquiv y δ q hq)
  have hReindex := uniformProbability_reindex e (fun x =>
    ‖(∑ a : Fin m, y (x a).val) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ))
  change uniformProbability (fun x : Fin m →
    {i : Fin n // (canonicalRowProfile y δ).part i = q} =>
      ‖(∑ a, y (x a).val) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) = _ at hReindex
  rw [hReindex]
  have hPart : (spreadPart y q.val.2.val δ).Nonempty := by
    simpa only [taggedPart, taggedValues, hq, ↓reduceIte, spreadPart] using q.property
  have hBound := canonical_spread_part_small_ball hd hk hm hmd y q.val.2.val hPart hτ z
  simpa only [canonicalRowProfile, taggedValues, hq, ↓reduceIte] using hBound

end CircularLaw
