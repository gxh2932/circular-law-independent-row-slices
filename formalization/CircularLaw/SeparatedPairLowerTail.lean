import CircularLaw.UniformInjectionConcentration
import CircularLaw.PairedCountSwap
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exponential lower tail for the literal separated-pair count

The exact mean lower bound and transposition bound are combined on the
actual uniform injection law. The resulting failure bound is
exp(-delta^2*d/64), with no assumed pair-count estimate.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem separated_pair_count_lower_tail {n d : ℕ} (hd : 0 < d) (hSize : 2 * d ≤ n)
    (y : Fin n → ℂ) {δ ρ : ℝ} (hδ : 0 ≤ δ) (hρ : 0 < ρ)
    (hLevel : ∀ c : ℂ, ((Finset.univ.filter (fun j => ‖y j - c‖ ≤ ρ)).card : ℝ) ≤
      (1 - δ) * n) :
    uniformProbability (fun e : Fin d ⊕ Fin d ↪ Fin n =>
      ((pairedSeparatedCoordinates y ρ e).card : ℝ) < δ * d / 2) ≤
        Real.exp (-δ ^ 2 * d / 64) := by
  let p : Fin d ⊕ Fin d ≃ Fin (d + d) := finSumFinEquiv
  let transport := embeddingDomainTransportEquiv (γ := Fin n) p
  let g : (Fin d ⊕ Fin d ↪ Fin n) → ℝ := fun e => pairedSeparatedCount y ρ e
  let f : (Fin (d + d) ↪ Fin n) → ℝ := fun e => g (transport e)
  have hMean : δ * d ≤ finiteMean f := by
    rw [show f = fun e => g (transport e) from rfl, finiteMean_reindex]
    simpa only [g, paired_separated_count_eq_card] using separated_pair_count_mean_ge hSize y hρ hLevel
  have hSwap : ∀ e : Fin (d + d) ↪ Fin n, ∀ a b : Fin n,
      |f e - f (e.trans (Equiv.swap a b).toEmbedding)| ≤ (2 : ℝ) := by
    intro e a b
    exact paired_separated_count_swap_bound y ρ (p.toEmbedding.trans e) a b
  have hTail := uniform_injection_lower_tail (m := d + d) (n := n) (by omega) f
    (by norm_num : (0 : ℝ) ≤ 2) hSwap (show 0 ≤ δ * d / 2 by positivity)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hExponent : -(δ * (d : ℝ) / 2) ^ 2 / (2 * ((d + d : ℕ) : ℝ) * (2 : ℝ) ^ 2) =
      -δ ^ 2 * d / 64 := by
    push_cast
    field_simp
    ring
  rw [hExponent] at hTail
  rw [← uniformProbability_reindex transport
    (fun e => ((pairedSeparatedCoordinates y ρ e).card : ℝ) < δ * d / 2)]
  apply (uniformProbability_mono (fun e he => ?_)).trans hTail
  rw [← paired_separated_count_eq_card] at he
  change g (transport e) < δ * d / 2 at he
  dsimp only [f]
  linarith

theorem source_nonalmost_separated_pair_lower_tail {n d : ℕ}
    (hd : 0 < d) (hSize : 2 * d ≤ n) {δ ρ : ℝ} (hδ : 0 ≤ δ) (hρ : 0 < ρ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : sourceNonAlmostConstant δ ρ x) :
    uniformProbability (fun e : Fin d ⊕ Fin d ↪ Fin n =>
      ((pairedSeparatedCoordinates (fun j => x j) (ρ / Real.sqrt n) e).card : ℝ) < δ * d / 2) ≤
        Real.exp (-δ ^ 2 * d / 64) :=
  separated_pair_count_lower_tail hd hSize _ hδ
    (div_pos hρ (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n)))) hx

end CircularLaw
