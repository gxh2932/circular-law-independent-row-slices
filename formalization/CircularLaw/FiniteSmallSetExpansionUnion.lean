import CircularLaw.BernoulliSmallSetFamilyExpansion

/-!
# Summing cardinality expansion failures with a finite measure

Exponential failure bounds at each positive cardinality imply one
uniform event for every small set above the seed size. The geometric
sum preserves the cardinality bound's prefactor.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem small_set_cardinality_failure_to_uniform
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {N C k : ℕ} (hk : 0 < k) (p : ℝ≥0) {d K : ℝ}
    (hd : Real.exp 64 ≤ d) (hK : 0 ≤ K)
    (V : α → Finset (Fin C) → ℝ)
    (hFixed : ∀ ell : ℕ, 0 < ell → (ell : ℝ) * p ≤ 1 / 2 →
      μ.real {x | ∃ S : Finset (Fin C), S.card = ell ∧ V x S < sourceGraphExpansion N d ell} ≤
        K * Real.exp (-d * ell / 16)) :
    μ.real {x | ∃ S : Finset (Fin C), k ≤ S.card ∧ (S.card : ℝ) * p ≤ 1 / 2 ∧
      V x S < sourceGraphExpansion N d S.card} ≤ 2 * K * Real.exp (-d * k / 16) := by
  let E := fun j : ℕ => {x : α | ∃ S : Finset (Fin C), S.card = k + j ∧
    (S.card : ℝ) * p ≤ 1 / 2 ∧ V x S < sourceGraphExpansion N d S.card}
  have hBound (j : ℕ) : μ.real (E j) ≤ K * Real.exp (-d * ((k + j : ℕ) : ℝ) / 16) := by
    by_cases hSmall : ((k + j : ℕ) : ℝ) * p ≤ 1 / 2
    · have hSubset : E j ⊆ {x : α | ∃ S : Finset (Fin C), S.card = k + j ∧
          V x S < sourceGraphExpansion N d ((k + j : ℕ) : ℝ)} := by
        rintro x ⟨S, hS, _, hBad⟩
        exact ⟨S, hS, by simpa only [hS] using hBad⟩
      exact (measureReal_mono hSubset (measure_ne_top _ _)).trans (hFixed (k + j) (by omega) hSmall)
    · have hEmpty : E j = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨S, hS, hSize, _⟩
        exact hSmall (by simpa only [hS] using hSize)
      rw [hEmpty, measureReal_empty]
      positivity
  have hSubset : {x : α | ∃ S : Finset (Fin C), k ≤ S.card ∧ (S.card : ℝ) * p ≤ 1 / 2 ∧
      V x S < sourceGraphExpansion N d S.card} ⊆ ⋃ j ∈ Finset.range (C + 1), E j := by
    rintro x ⟨S, hLower, hSmall, hBad⟩
    have hUpper : S.card ≤ C := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    exact Set.mem_iUnion.mpr ⟨S.card - k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),
      S, by omega, hSmall, hBad⟩⟩
  have hPoint (j : ℕ) : K * Real.exp (-d * ((k + j : ℕ) : ℝ) / 16) =
      (K * Real.exp (-d * k / 16)) * (Real.exp (-d / 16)) ^ j := by
    rw [← Real.exp_nat_mul]
    have hExponent : -d * ((k + j : ℕ) : ℝ) / 16 = -d * k / 16 + (j : ℝ) * (-d / 16) := by
      push_cast
      ring
    rw [hExponent, Real.exp_add]
    ring
  have hHalf : Real.exp (-d / 16) ≤ 1 / 2 := by
    apply (Real.exp_le_exp.mpr (by linarith [large_expansion_degree_exp_lower.trans hd] : -d / 16 ≤ -1)).trans
    exact Real.exp_neg_one_lt_half.le
  calc
    _ ≤ μ.real (⋃ j ∈ Finset.range (C + 1), E j) := measureReal_mono hSubset (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range (C + 1), μ.real (E j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (C + 1), K * Real.exp (-d * ((k + j : ℕ) : ℝ) / 16) :=
      Finset.sum_le_sum (fun j _ => hBound j)
    _ = (K * Real.exp (-d * k / 16)) *
        ∑ j ∈ Finset.range (C + 1), (Real.exp (-d / 16)) ^ j := by
      simp_rw [hPoint]
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (geometric_nonnegative_powers_sum_le_two (Real.exp_pos _).le hHalf (C + 1))
        (mul_nonneg hK (Real.exp_pos (-d * k / 16)).le)
      nlinarith

end CircularLaw
