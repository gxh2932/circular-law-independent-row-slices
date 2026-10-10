import CircularLaw.NormHeavyModerateMass

/-!
# Exhaustive heavy-case cover and the oriented level budget

All five cases cover every pair with a heavy scale product and a
larger left coordinate fiber. Their checked bounds give a constant
budget for the actual normalized matrix edge costs. The opposite
fiber ordering is assembled in `NormHeavySquare` for square matrices.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem real_five_indicator_cover {w : ℝ} (hw : 0 ≤ w) (p₁ p₂ p₃ p₄ p₅ : Prop)
    (hCover : p₁ ∨ p₂ ∨ p₃ ∨ p₄ ∨ p₅) :
    w ≤ (if p₁ then w else 0) + (if p₂ then w else 0) + (if p₃ then w else 0) +
      (if p₄ then w else 0) + (if p₅ then w else 0) := by
  have hIte : ∀ p : Prop, (0 : ℝ) ≤ if p then w else 0 := by
    intro p
    split_ifs
    · exact hw
    · exact le_rfl
  rcases hCover with h | h | h | h | h
  all_goals simp only [if_pos h]
  all_goals linarith [hIte p₁, hIte p₂, hIte p₃, hIte p₄, hIte p₅]

theorem normHeavySelectedSum_cover_five {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (P p₁ p₂ p₃ p₄ p₅ : ℕ → ℕ → Prop)
    (hCover : ∀ k ∈ normCoordinateLevels n x, ∀ l ∈ normCoordinateLevels n y,
      P k l → p₁ k l ∨ p₂ k l ∨ p₃ k l ∨ p₄ k l ∨ p₅ k l) :
    normHeavySelectedSum C N M x y P ≤ normHeavySelectedSum C N M x y p₁ +
      normHeavySelectedSum C N M x y p₂ + normHeavySelectedSum C N M x y p₃ +
      normHeavySelectedSum C N M x y p₄ + normHeavySelectedSum C N M x y p₅ := by
  unfold normHeavySelectedSum
  calc
    _ ≤ ∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y,
        ((if p₁ k l then normHeavyLevelWeight C N M x y k l else 0) +
         (if p₂ k l then normHeavyLevelWeight C N M x y k l else 0) +
         (if p₃ k l then normHeavyLevelWeight C N M x y k l else 0) +
         (if p₄ k l then normHeavyLevelWeight C N M x y k l else 0) +
         (if p₅ k l then normHeavyLevelWeight C N M x y k l else 0)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      have hWeight := normHeavyLevelWeight_nonneg hn hC hN M hM x y hk hl
      by_cases hP : P k l
      · rw [if_pos hP]
        exact real_five_indicator_cover hWeight _ _ _ _ _ (hCover k hk l hl hP)
      · rw [if_neg hP]
        have hIte : ∀ p : Prop, (0 : ℝ) ≤ if p then normHeavyLevelWeight C N M x y k l else 0 := by
          intro p
          split_ifs
          · exact hWeight
          · exact le_rfl
        linarith [hIte (p₁ k l), hIte (p₂ k l), hIte (p₃ k l), hIte (p₄ k l), hIte (p₅ k l)]
    _ = _ := by simp only [Finset.sum_add_distrib]

theorem normHeavy_oriented_pair_cases {m n : ℕ} (hn : 0 < n) (C N cap : ℝ)
    (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hOriented : normHeavyOrientedPair n N x y k l) :
    (normHeavyOrientedPair n N x y k l ∧ normHeavyScaledRatio C N M x y k l ≤ cap) ∨
    (normHeavyOrientedPair n N x y k l ∧ (2 : ℝ) ^ k ≤ (2 : ℝ) ^ l / Real.sqrt N) ∨
    (True ∧ normHeavyLargeRatioPair C N cap M x y k l) ∨
    (True ∧ normHeavyModerateMassPair C N cap M x y k l) ∨
    (True ∧ normHeavySmallMassPair C N M x y k l) := by
  by_cases hSmall : normHeavyScaledRatio C N M x y k l ≤ cap
  · exact Or.inl ⟨hOriented, hSmall⟩
  by_cases hDegree : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ l / Real.sqrt N
  · exact Or.inr (Or.inl ⟨hOriented, hDegree⟩)
  have hScaled := lt_of_not_ge hSmall
  have hLevel := lt_of_not_ge hDegree
  by_cases hLarge : normHeavyEntropyArgument n x k < (normHeavyEdgeRatio C N M x y k l) ^ 4
  · right; right; left
    exact ⟨True.intro, hOriented, hScaled, hLevel, hLarge⟩
  have hFourth := le_of_not_gt hLarge
  by_cases hInv : 1 / normCoordinateMass n x k ≤ 4 * ((2 : ℝ) ^ k) ^ 2
  · right; right; right; left
    exact ⟨True.intro, hOriented, hScaled, hFourth, hInv⟩
  · right; right; right; right
    have hMass := normCoordinateMass_pos hn x hk
    have hSmallMass := (lt_div_iff₀ hMass).mp (lt_of_not_ge hInv)
    exact ⟨True.intro, hOriented, hFourth, by nlinarith [hSmallMass]⟩

theorem normHeavy_oriented_sum_bound {m n : ℕ} (hn : 0 < n) (hm : m ≤ n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hColumn : ∀ j, (∑ i, M i j) ≤ N) (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (hx : (∑ i, (x i) ^ 2) ≤ 1) (hy : (∑ j, (y j) ^ 2) ≤ 1) :
    normHeavySelectedSum C N M x y (normHeavyOrientedPair n N x y) ≤
      25 * cap + 10 / C + 40 * kappa₂ / C + 80 * kappa₂ / (C * cap * Real.log cap) + 10 := by
  have hCover := normHeavySelectedSum_cover_five hn hC hN M hM x y (normHeavyOrientedPair n N x y)
    (fun k l => normHeavyOrientedPair n N x y k l ∧ normHeavyScaledRatio C N M x y k l ≤ cap)
    (fun k l => normHeavyOrientedPair n N x y k l ∧ (2 : ℝ) ^ k ≤ (2 : ℝ) ^ l / Real.sqrt N)
    (fun k l => True ∧ normHeavyLargeRatioPair C N cap M x y k l)
    (fun k l => True ∧ normHeavyModerateMassPair C N cap M x y k l)
    (fun k l => True ∧ normHeavySmallMassPair C N M x y k l)
    (fun _ hk _ _ hO => normHeavy_oriented_pair_cases hn C N cap M x y hk hO)
  have hFirst := normHeavy_small_scaled_sum hn hm C N M x y hx hy
    (lt_trans (by norm_num : (0 : ℝ) < 1) hCap).le (normHeavyOrientedPair n N x y)
  have hSecond := normHeavy_degree_sum hn hC hN M hM hColumn x y hy (normHeavyOrientedPair n N x y)
  have hThird := normHeavy_large_ratio_sum hn hm hC hN hCap hKappa M hM hDP x y hx (fun _ _ => True)
  have hFourth := normHeavy_moderate_mass_sum hn hm hC hN hCap hKappa M hM hDP x y hx (fun _ _ => True)
  have hFifth := normHeavy_small_mass_sum hn C N M x y hy (fun _ _ => True)
  linarith

end CircularLaw
