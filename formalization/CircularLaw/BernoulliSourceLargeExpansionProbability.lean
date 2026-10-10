import CircularLaw.BernoulliSourceLargeSetExpansion

/-!
# One actual Bernoulli event for the full larger-set source range

Summing the cardinality failures gives an ambient-size prefactor. This
bound applies to every diagonal embedding of the actual exposure law,
with at least three quarters of the ambient rows and no extra ambient
columns.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_source_large_set_expansion_failure
    {N M C : ℕ} (hN : 0 < N) (hCN : C ≤ N) (hRows : 3 * (N : ℝ) / 4 ≤ M)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2)
    (e : Fin M ↪ Fin C) {d β : ℝ} (hDegree : d = (N : ℝ) * p)
    (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliCubeLaw (Fin M × Fin C) p hp).real {x | ∃ S : Finset (Fin C),
      1 / 2 ≤ (S.card : ℝ) * p ∧ (S.card : ℝ) ≤ sourceGraphTerminalScale N d ∧
        ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
          sourceGraphExpansion N d S.card} ≤ (N : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  let E := fun j : ℕ => {x : Fin M × Fin C → Bool | ∃ S : Finset (Fin C), S.card = j + 1 ∧
    1 / 2 ≤ (S.card : ℝ) * p ∧ (S.card : ℝ) ≤ sourceGraphTerminalScale N d ∧
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
        sourceGraphExpansion N d S.card}
  have hFixed (j : ℕ) : (bernoulliCubeLaw (Fin M × Fin C) p hp).real (E j) ≤
      Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
    by_cases hLarge : 1 / 2 ≤ ((j + 1 : ℕ) : ℝ) * p
    · by_cases hRange : ((j + 1 : ℕ) : ℝ) ≤ sourceGraphTerminalScale N d
      · have hSubset : E j ⊆ {x : Fin M × Fin C → Bool | ∃ S : Finset (Fin C), S.card = j + 1 ∧
          ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
            sourceGraphExpansion N d ((j + 1 : ℕ) : ℝ)} := by
          rintro x ⟨S, hS, _, _, hBad⟩
          exact ⟨S, hS, by simpa only [hS] using hBad⟩
        exact (measureReal_mono hSubset (measure_ne_top _ _)).trans
          (bernoulli_source_large_set_cardinality_expansion_failure hN hCN (by omega) hRows p hp hHalf
            e hDegree hd hLarge hRange hβ hβOne)
      · have hEmpty : E j = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro x ⟨S, hS, _, hSize, _⟩
          exact hRange (by simpa only [hS] using hSize)
        rw [hEmpty, measureReal_empty]
        exact (Real.exp_pos _).le
    · have hEmpty : E j = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨S, hS, hSize, _, _⟩
        exact hLarge (by simpa only [hS] using hSize)
      rw [hEmpty, measureReal_empty]
      exact (Real.exp_pos _).le
  have hSubset : {x : Fin M × Fin C → Bool | ∃ S : Finset (Fin C),
      1 / 2 ≤ (S.card : ℝ) * p ∧ (S.card : ℝ) ≤ sourceGraphTerminalScale N d ∧
        ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
          sourceGraphExpansion N d S.card} ⊆ ⋃ j ∈ Finset.range C, E j := by
    rintro x ⟨S, hLarge, hRange, hBad⟩
    have hPos : 0 < S.card := by
      by_contra h
      have hZero : S.card = 0 := by omega
      simp only [hZero, Nat.cast_zero, zero_mul] at hLarge
      norm_num at hLarge
    have hUpper : S.card ≤ C := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    exact Set.mem_iUnion.mpr ⟨S.card - 1, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),
      S, by omega, hLarge, hRange, hBad⟩⟩
  calc
    _ ≤ (bernoulliCubeLaw (Fin M × Fin C) p hp).real (⋃ j ∈ Finset.range C, E j) :=
      measureReal_mono hSubset (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range C, (bernoulliCubeLaw (Fin M × Fin C) p hp).real (E j) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range C, Real.exp (-(N : ℝ) / (64 * Real.log d)) :=
      Finset.sum_le_sum (fun j _ => hFixed j)
    _ = (C : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hCN) (Real.exp_pos _).le

end CircularLaw
