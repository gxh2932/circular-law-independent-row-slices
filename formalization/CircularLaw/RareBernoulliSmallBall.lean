import CircularLaw.RareBernoulliAtoms

/-!
# A small-ball bound that retains rare Bernoulli selections

When m*p is at most one half, every ball of radius rho/3 misses either
the zero-selection atom or all single-selection atoms. Their exact
masses give an exclusion probability of at least m*p/2.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_cube_rare_linear_form_small_ball {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hRare : (Fintype.card ι : ℝ) * p ≤ 1 / 2)
    (a : ι → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hLarge : ∀ i, ρ ≤ ‖a i‖) (z : ℂ) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖(∑ i, weightedBernoulliValue (a i) (x i)) - z‖ ≤ ρ / 3} ≤
        1 - (Fintype.card ι : ℝ) * p / 2 := by
  let μ := bernoulliCubeLaw ι p hp
  let E : Set (ι → Bool) := {x | ‖(∑ i, weightedBernoulliValue (a i) (x i)) - z‖ ≤ ρ / 3}
  by_cases hCenter : ‖z‖ ≤ ρ / 3
  · have hDisjoint : E ⊆ (bernoulliSingleSelections ι : Set (ι → Bool))ᶜ := by
      intro x hx hxOne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxOne
      change ‖(∑ j, weightedBernoulliValue (a j) (bernoulliSingleSelection i j)) - z‖ ≤ ρ / 3 at hx
      rw [weighted_bernoulli_single_selection] at hx
      have hTriangle := norm_le_norm_sub_add (a i) z
      nlinarith [hLarge i]
    have hBound := measureReal_mono (μ := μ) hDisjoint
    rw [probReal_compl_eq_one_sub (Set.toFinite _).measurableSet,
      bernoulli_cube_single_selections_real] at hBound
    have hTail := bernoulli_zero_selection_probability_lower p hp (Fintype.card ι - 1)
    have hPrev : ((Fintype.card ι - 1 : ℕ) : ℝ) * p ≤ (Fintype.card ι : ℝ) * p :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le (Fintype.card ι) 1) p.coe_nonneg
    have hTailHalf : 1 / 2 ≤ (1 - (p : ℝ)) ^ (Fintype.card ι - 1) := by linarith
    have hMass := mul_le_mul_of_nonneg_left hTailHalf
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)) p.coe_nonneg)
    change μ.real E ≤ _
    linarith
  · have hDisjoint : E ⊆ ({fun _ : ι => false} : Set (ι → Bool))ᶜ := by
      intro x hx hxZero
      have hxEq : x = fun _ : ι => false := hxZero
      rw [hxEq] at hx
      change ‖(∑ i, weightedBernoulliValue (a i) false) - z‖ ≤ ρ / 3 at hx
      rw [weighted_bernoulli_zero_selection, zero_sub, norm_neg] at hx
      exact hCenter hx
    have hBound := measureReal_mono (μ := μ) hDisjoint
    rw [probReal_compl_eq_one_sub (measurableSet_singleton _), bernoulli_cube_zero_atom_real] at hBound
    have hZero := bernoulli_zero_selection_probability_lower p hp (Fintype.card ι)
    change μ.real E ≤ _
    linarith

end CircularLaw
