import CircularLaw.SmallValueCutoff

/-!
# Upper bounds for small-value tests from one ordered quantile
-/

noncomputable section
open Classical
open scoped NNReal BigOperators

namespace CircularLaw

theorem ordered_small_value_test_mean_le_tail_fraction {n : ℕ}
    (s : Fin n → ℝ≥0) (hs : Antitone s) (f : ℝ≥0 → ℝ)
    (hBound : ∀ t, 0 ≤ f t ∧ f t ≤ 1) {R : ℝ}
    (hZero : ∀ t : ℝ≥0, R ≤ (t : ℝ) → f t = 0)
    (j : Fin n) (hLower : R ≤ (s j : ℝ)) :
    empiricalNonnegativeMean s f ≤ (n - j.val : ℕ) / (n : ℝ) := by
  have hFilter : (Finset.univ : Finset (Fin n)).filter (fun i => j ≤ i) = Finset.Ici j := by
    ext i
    simp
  have hSum : (∑ i, f (s i)) ≤ (n - j.val : ℕ) := by
    calc
      _ ≤ ∑ i : Fin n, if j ≤ i then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : j ≤ i
        · rw [if_pos hi]
          exact (hBound _).2
        · rw [if_neg hi]
          have hOrder : (s j : ℝ) ≤ (s i : ℝ) := by exact_mod_cast hs (le_of_not_ge hi)
          rw [hZero _ (hLower.trans hOrder)]
      _ = _ := by simp only [← Finset.sum_filter, hFilter, Finset.sum_const,
        Fin.card_Ici, nsmul_eq_mul, mul_one]
  simpa only [empiricalNonnegativeMean, finiteMean, Fintype.card_fin] using
    div_le_div_of_nonneg_right hSum (Nat.cast_nonneg n)

end CircularLaw
