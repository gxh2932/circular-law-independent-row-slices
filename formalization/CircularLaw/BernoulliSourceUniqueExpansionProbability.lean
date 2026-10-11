import CircularLaw.BernoulliExposureSmallExpansionProbability
import CircularLaw.BernoulliSourceLargeExpansionProbability
import CircularLaw.SourceGraphGap

/-!
# Actual Bernoulli unique expansion over the entire source range

The small and larger set estimates give the actual graph expansion
budget for each square or one-column rectangular exposure law. The
ambient normalization and the source terminal scale are unchanged.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem matrix_unique_expansion_budget_failure_iff
    {ρ ι : Type*} [Fintype ρ] (A : Matrix ρ ι ℂ) (e : ρ ↪ ι)
    (β n d k u : ℝ) :
    ¬ MatrixUniqueExpansionBudget A e β n d k u ↔
      ∃ S : Finset ι, k ≤ (S.card : ℝ) ∧ (S.card : ℝ) ≤ u ∧
        ((matrixUniqueNeighbourhood A e β S).card : ℝ) < sourceGraphExpansion n d S.card := by
  simp only [MatrixUniqueExpansionBudget, not_forall, not_le, exists_prop]

theorem matrix_unique_expansion_failure_subset_split
    {Ω ρ ι : Type*} [Fintype ρ] (A : Ω → Matrix ρ ι ℂ) (e : ρ ↪ ι)
    (p : ℝ≥0) (β n d : ℝ) (k : ℕ) :
    {x | ¬ MatrixUniqueExpansionBudget (A x) e β n d k (sourceGraphTerminalScale n d)} ⊆
      {x | ∃ S : Finset ι, k ≤ S.card ∧ (S.card : ℝ) * p ≤ 1 / 2 ∧
        ((matrixUniqueNeighbourhood (A x) e β S).card : ℝ) < sourceGraphExpansion n d S.card} ∪
      {x | ∃ S : Finset ι, 1 / 2 ≤ (S.card : ℝ) * p ∧
        (S.card : ℝ) ≤ sourceGraphTerminalScale n d ∧
          ((matrixUniqueNeighbourhood (A x) e β S).card : ℝ) < sourceGraphExpansion n d S.card} := by
  intro x hx
  obtain ⟨S, hSeed, hRange, hBad⟩ :=
    (matrix_unique_expansion_budget_failure_iff (A x) e β n d k (sourceGraphTerminalScale n d)).mp hx
  have hSeedNat : k ≤ S.card := by exact_mod_cast hSeed
  by_cases hSmall : (S.card : ℝ) * p ≤ 1 / 2
  · exact Or.inl ⟨S, hSeedNat, hSmall, hBad⟩
  · exact Or.inr ⟨S, (lt_of_not_ge hSmall).le, hRange, hBad⟩

theorem bernoulli_ambient_square_source_unique_expansion_failure
    {N M k : ℕ} (hN : 0 < N) (hMN : M ≤ N) (hk : 0 < k)
    (hRows : 3 * (N : ℝ) / 4 ≤ M)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw M p hp).real {x | ¬ MatrixUniqueExpansionBudget
      (bernoulliSquareMatrix x) (Function.Embedding.refl _) β N d k (sourceGraphTerminalScale N d)} ≤
      2 * Real.exp (-d * k / 16) + (N : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  have hdSmall : Real.exp 64 ≤ d := (Real.exp_le_exp.mpr (by norm_num : (64 : ℝ) ≤ 1024)).trans hd
  have hSmall := bernoulli_ambient_square_small_set_expansion_failure hN hMN hk hRows p hp hDegree
    hdSmall hβ hβOne
  have hLarge := bernoulli_source_large_set_expansion_failure hN hMN hRows p hp hHalf
    (Function.Embedding.refl (Fin M)) hDegree hd hβ hβOne
  apply (measureReal_mono (matrix_unique_expansion_failure_subset_split
    bernoulliSquareMatrix (Function.Embedding.refl _) p β N d k) (measure_ne_top _ _)).trans
  exact (measureReal_union_le _ _).trans (add_le_add hSmall hLarge)

theorem bernoulli_ambient_rectangular_source_unique_expansion_failure
    {N M k : ℕ} (hN : 0 < N) (hCN : M + 1 ≤ N) (hk : 0 < k)
    (hRows : 3 * (N : ℝ) / 4 ≤ M)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliCubeLaw (Fin M × Fin (M + 1)) p hp).real {x | ¬ MatrixUniqueExpansionBudget
      (bernoulliRectangularMatrix x) Fin.castSuccEmb β N d k (sourceGraphTerminalScale N d)} ≤
      4 * Real.exp (-d * k / 16) + (N : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  have hdSmall : Real.exp 64 ≤ d := (Real.exp_le_exp.mpr (by norm_num : (64 : ℝ) ≤ 1024)).trans hd
  have hSmall := bernoulli_ambient_rectangular_small_set_expansion_failure hN (by omega) hk hRows p hp
    hDegree hdSmall hβ hβOne
  have hLarge := bernoulli_source_large_set_expansion_failure hN hCN hRows p hp hHalf
    Fin.castSuccEmb hDegree hd hβ hβOne
  apply (measureReal_mono (matrix_unique_expansion_failure_subset_split
    bernoulliRectangularMatrix Fin.castSuccEmb p β N d k) (measure_ne_top _ _)).trans
  exact (measureReal_union_le _ _).trans (add_le_add hSmall hLarge)

end CircularLaw
