import CircularLaw.BernoulliLargeSetMean
import CircularLaw.SourceLargeSetExpansionBounds

/-!
# Actual larger-set expansion at the source ambient threshold

The fixed-set failure is at most exp(-N/(32*log d)). Counting all
column sets of one size costs half that exponent. The arguments use
the actual rectangular entry law and an arbitrary diagonal embedding.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem source_graph_terminal_probability_range {N ell : ℕ} (hN : 0 < N)
    (p : ℝ≥0) {d : ℝ} (hDegree : d = (N : ℝ) * p) (hd : 0 < d)
    (hRange : (ell : ℝ) ≤ sourceGraphTerminalScale N d) :
    (ell : ℝ) * p ≤ Real.log (Real.log d) / 2 := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have h := mul_le_mul_of_nonneg_right hRange p.coe_nonneg
  have hEq : sourceGraphTerminalScale N d * p = Real.log (Real.log d) / 2 := by
    dsimp only [sourceGraphTerminalScale]
    rw [hDegree]
    have hpPos : 0 < (p : ℝ) := by nlinarith
    field_simp
  rwa [hEq] at h

theorem source_graph_large_probability_size_lower {N ell : ℕ} (hN : 0 < N)
    (p : ℝ≥0) {d : ℝ} (hDegree : d = (N : ℝ) * p) (hd : 0 < d)
    (hLarge : 1 / 2 ≤ (ell : ℝ) * p) :
    (N : ℝ) / (2 * d) ≤ ell := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  apply (div_le_iff₀ (by positivity : 0 < 2 * d)).mpr
  have h := mul_le_mul_of_nonneg_left hLarge hn.le
  rw [hDegree]
  nlinarith

theorem bernoulli_source_large_set_mean_lower
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] {N : ℕ}
    (hN : 0 < N) (hRows : 3 * (N : ℝ) / 4 ≤ Fintype.card ρ)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2)
    (e : ρ ↪ ι) (S : Finset ι) {d : ℝ} (hDegree : d = (N : ℝ) * p)
    (hd : Real.exp 1024 ≤ d) (hLarge : 1 / 2 ≤ (S.card : ℝ) * p)
    (hRange : (S.card : ℝ) ≤ sourceGraphTerminalScale N d) :
    (N : ℝ) / (4 * Real.log d) ≤ bernoulliUniqueNeighbourhoodMean p e S := by
  obtain ⟨hLargeD, hLogD, hSource⟩ := large_set_expansion_degree_range hd
  have hdp : 0 < d := by linarith
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  exact bernoulli_large_set_ambient_mean_lower hN hRows p hp hHalf e S (by linarith) hLarge
    (source_graph_terminal_probability_range hN p hDegree hdp hRange)
    (hRange.trans (source_graph_terminal_range hn hSource).2.1)

theorem bernoulli_source_large_set_fixed_expansion_failure
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] {N : ℕ}
    (hN : 0 < N) (hRows : 3 * (N : ℝ) / 4 ≤ Fintype.card ρ)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2)
    (e : ρ ↪ ι) (S : Finset ι) {d β : ℝ} (hDegree : d = (N : ℝ) * p)
    (hd : Real.exp 1024 ≤ d) (hLarge : 1 / 2 ≤ (S.card : ℝ) * p)
    (hRange : (S.card : ℝ) ≤ sourceGraphTerminalScale N d)
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliCubeLaw (ρ × ι) p hp).real {x |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
        sourceGraphExpansion N d S.card} ≤ Real.exp (-(N : ℝ) / (32 * Real.log d)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have he : 0 < (S.card : ℝ) := by
    by_contra h
    have hCard : S.card = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt h) (Nat.cast_nonneg S.card))
    simp only [hCard, Nat.cast_zero, zero_mul] at hLarge
    norm_num at hLarge
  have hMean := bernoulli_source_large_set_mean_lower hN hRows p hp hHalf e S hDegree hd hLarge hRange
  have hThreshold := source_graph_large_set_threshold_upper hn he hd hRange
  have hHalfMean : sourceGraphExpansion N d S.card ≤ bernoulliUniqueNeighbourhoodMean p e S / 2 := by
    have hEq : (N : ℝ) / (8 * Real.log d) = ((N : ℝ) / (4 * Real.log d)) / 2 := by field_simp; norm_num
    rw [hEq] at hThreshold
    linarith
  have hSubset : {x : ρ × ι → Bool |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
        sourceGraphExpansion N d S.card} ⊆ {x |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) ≤
        sourceGraphExpansion N d S.card} := by
    intro x hx
    change ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
      sourceGraphExpansion N d S.card at hx
    exact hx.le
  apply ((measureReal_mono hSubset (measure_ne_top _ _)).trans
    (bernoulli_unique_neighbourhood_half_mean_lower_tail p hp e S hβ hβOne hHalfMean)).trans
  apply Real.exp_le_exp.mpr
  have hEq : -(N : ℝ) / (32 * Real.log d) = -((N : ℝ) / (4 * Real.log d)) / 8 := by field_simp; norm_num
  rw [hEq]
  linarith

theorem bernoulli_source_large_set_cardinality_expansion_failure
    {N M C ell : ℕ} (hN : 0 < N) (hCN : C ≤ N) (hell : 0 < ell)
    (hRows : 3 * (N : ℝ) / 4 ≤ M)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2)
    (e : Fin M ↪ Fin C) {d β : ℝ} (hDegree : d = (N : ℝ) * p)
    (hd : Real.exp 1024 ≤ d) (hLarge : 1 / 2 ≤ (ell : ℝ) * p)
    (hRange : (ell : ℝ) ≤ sourceGraphTerminalScale N d)
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliCubeLaw (Fin M × Fin C) p hp).real {x | ∃ S : Finset (Fin C), S.card = ell ∧
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
        sourceGraphExpansion N d ell} ≤ Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  by_cases hellC : ell ≤ C
  · let F := (Finset.univ : Finset (Fin C)).powersetCard ell
    let E := fun S : Finset (Fin C) => {x : Fin M × Fin C → Bool |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
        sourceGraphExpansion N d ell}
    have hFixed (S : Finset (Fin C)) (hS : S ∈ F) :
        (bernoulliCubeLaw (Fin M × Fin C) p hp).real (E S) ≤ Real.exp (-(N : ℝ) / (32 * Real.log d)) := by
      have hSc := (Finset.mem_powersetCard.mp hS).2
      have h := bernoulli_source_large_set_fixed_expansion_failure hN
        (by simpa only [Fintype.card_fin] using hRows) p hp hHalf e S hDegree hd
        (by simpa only [hSc] using hLarge) (by simpa only [hSc] using hRange) hβ hβOne
      simpa only [hSc] using h
    have hEvent : {x : Fin M × Fin C → Bool | ∃ S : Finset (Fin C), S.card = ell ∧ x ∈ E S} =
        ⋃ S ∈ F, E S := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨S, hSc, hx⟩
        exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hSc⟩, hx⟩
      · rintro ⟨S, hS, hx⟩
        exact ⟨S, (Finset.mem_powersetCard.mp hS).2, hx⟩
    have hn : 0 < (N : ℝ) := by exact_mod_cast hN
    have he : 0 < (ell : ℝ) := by exact_mod_cast hell
    have hdp : 0 < d := by linarith [(large_set_expansion_degree_range hd).1]
    have hEntropy := source_graph_large_set_entropy_upper hn he hd
      (source_graph_large_probability_size_lower hN p hDegree hdp hLarge) hRange
    change (bernoulliCubeLaw (Fin M × Fin C) p hp).real {x | ∃ S, S.card = ell ∧ x ∈ E S} ≤ _
    rw [hEvent]
    calc
      _ ≤ ∑ S ∈ F, (bernoulliCubeLaw (Fin M × Fin C) p hp).real (E S) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _S ∈ F, Real.exp (-(N : ℝ) / (32 * Real.log d)) := Finset.sum_le_sum hFixed
      _ = (C.choose ell : ℝ) * Real.exp (-(N : ℝ) / (32 * Real.log d)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, F, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin]
      _ ≤ Real.exp ((ell : ℝ) * (1 + Real.log ((N : ℝ) / ell))) *
          Real.exp (-(N : ℝ) / (32 * Real.log d)) :=
        mul_le_mul_of_nonneg_right (choose_le_ambient_log_entropy hCN hell hellC) (Real.exp_pos _).le
      _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hEq : -(N : ℝ) / (32 * Real.log d) = -2 * ((N : ℝ) / (64 * Real.log d)) := by field_simp; norm_num
        rw [hEq, neg_div]
        linarith
  · have hEmpty : {x : Fin M × Fin C → Bool | ∃ S : Finset (Fin C), S.card = ell ∧
        ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
          sourceGraphExpansion N d ell} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨S, hS, _⟩
      have hCard : S.card ≤ C := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
      omega
    rw [hEmpty, measureReal_empty]
    exact (Real.exp_pos _).le

end CircularLaw
