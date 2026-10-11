import CircularLaw.BlockPairOccupancy

/-!
# A relative lower tail for pairs crossing separated blocks

The high-block occupancy has mean mu = d*|L|/n. Conditional on its
actual selected positions, the low block gives another exact occupancy
tail. Averaging the two bounds yields failure at most 2*exp(-mu/48)
below mu/8 separated pairs, without a coordinate independence premise.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem paired_block_coordinates_relative_lower_tail {n d : ℕ} (hn : 0 < n)
    (hSize : 2 * d ≤ n) (L R : Finset (Fin n)) (hR : 3 * (n : ℝ) / 4 ≤ R.card) :
    uniformProbability (fun e : Fin d ⊕ Fin d ↪ Fin n =>
      ((pairedBlockCoordinates L R e).card : ℝ) ≤ ((d : ℝ) / n) * L.card / 8) ≤
        2 * Real.exp (-(((d : ℝ) / n) * L.card) / 48) := by
  letI : Nonempty (Fin d ⊕ Fin d ↪ Fin n) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_sum, Fintype.card_fin] using (by omega : d + d ≤ n))
  let μ := ((d : ℝ) / n) * L.card
  let f := fun e : Fin d ⊕ Fin d ↪ Fin n => Function.Embedding.inl.trans e
  let E := fun e : Fin d ⊕ Fin d ↪ Fin n => ((pairedBlockCoordinates L R e).card : ℝ) ≤ μ / 8
  let w := fun u : Fin d ↪ Fin n => Real.exp (-μ / 48) +
    if (embeddingHitCount u L : ℝ) ≤ μ / 2 then (1 : ℝ) else 0
  have hFiber : ∀ u : Fin d ↪ Fin n, Nonempty {e // f e = u} →
      uniformProbability (fun e : {e // f e = u} => E e.val) ≤ w u := by
    intro u _
    by_cases hLow : (embeddingHitCount u L : ℝ) ≤ μ / 2
    · dsimp only [w]
      rw [if_pos hLow]
      exact (uniformProbability_le_one _).trans (by linarith [Real.exp_pos (-μ / 48)])
    · dsimp only [w]
      rw [if_neg hLow, add_zero]
      have hHigh : μ / 2 < (embeddingHitCount u L : ℝ) := lt_of_not_ge hLow
      apply (uniformProbability_mono ?_).trans
        ((paired_block_conditional_lower_tail hn hSize L R hR u).trans ?_)
      · intro e he
        change ((pairedBlockCoordinates L R e.val).card : ℝ) ≤ μ / 8 at he
        linarith
      · apply Real.exp_le_exp.mpr
        linarith
  have hBound := uniformProbability_le_fiberwise f E w hFiber
  have hWeight : (fun e : Fin d ⊕ Fin d ↪ Fin n => w (f e)) =
      (fun e => Real.exp (-μ / 48) +
        if (embeddingHitCount (Function.Embedding.inl.trans e) L : ℝ) ≤ μ / 2 then (1 : ℝ) else 0) := rfl
  rw [hWeight, finiteMean_add, finiteMean_const, finiteMean_indicator,
    uniform_sum_embedding_restriction (a := d) (b := d) (by omega)
      (fun u : Fin d ↪ Fin n => (embeddingHitCount u L : ℝ) ≤ μ / 2)] at hBound
  have hFirst := uniform_fin_embedding_occupancy_relative_lower_tail hn (by omega : d ≤ n) L
  have hμ : 0 ≤ μ := by dsimp only [μ]; positivity
  have hRates : Real.exp (-μ / 12) ≤ Real.exp (-μ / 48) := Real.exp_le_exp.mpr (by linarith)
  dsimp only [E] at hBound
  dsimp only [μ] at hRates
  linarith

theorem paired_separated_block_count_relative_lower_tail {n d : ℕ} (hn : 0 < n)
    (hSize : 2 * d ≤ n) (L R : Finset (Fin n)) (hR : 3 * (n : ℝ) / 4 ≤ R.card)
    (y : Fin n → ℂ) (ρ : ℝ)
    (hSep : ∀ l ∈ L, ∀ j ∈ R, ρ ≤ dist (y l) (y j)) :
    uniformProbability (fun e : Fin d ⊕ Fin d ↪ Fin n =>
      ((pairedSeparatedCoordinates y ρ e).card : ℝ) ≤ ((d : ℝ) / n) * L.card / 8) ≤
        2 * Real.exp (-(((d : ℝ) / n) * L.card) / 48) := by
  apply (uniformProbability_mono ?_).trans
    (paired_block_coordinates_relative_lower_tail hn hSize L R hR)
  intro e he
  have hSubset : pairedBlockCoordinates L R e ⊆ pairedSeparatedCoordinates y ρ e := by
    intro j hj
    obtain ⟨_, hjL, hjR⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [dist_eq_norm, norm_sub_rev] using hSep _ hjL _ hjR
  exact (by exact_mod_cast Finset.card_le_card hSubset :
    ((pairedBlockCoordinates L R e).card : ℝ) ≤ (pairedSeparatedCoordinates y ρ e).card).trans he

end CircularLaw
