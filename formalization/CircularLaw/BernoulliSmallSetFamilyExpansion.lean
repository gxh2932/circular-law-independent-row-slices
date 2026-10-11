import CircularLaw.BernoulliRectangularColumnSets

/-!
# Counting a fixed family of ambiently normalized small column sets

An image family is indexed by subsets of the exposed rows. Its column
set size and diagonal-row size can differ; the counting bound keeps
that distinction, including the empty diagonal subset.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_small_set_family_expansion_failure
    {N M C ell q : ℕ} (hN : 0 < N) (hMN : M ≤ N) (hell : 0 < ell)
    (hRows : 3 * (N : ℝ) / 4 ≤ M) (hq : q ≤ ell)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : 2 ≤ d)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) (hL : 1 ≤ Real.log ((N : ℝ) / ell))
    (hβ : 0 < β) (hβOne : β ≤ 1) (e : Fin M ↪ Fin C)
    (f : Finset (Fin M) → Finset (Fin C))
    (hCard : ∀ T, T.card = q → (f T).card = ell)
    (hInside : ∀ T, T.card = q → (bernoulliUniqueInsideRows e (f T)).card = q) :
    (bernoulliCubeLaw (Fin M × Fin C) p hp).real {x |
      ∃ T : Finset (Fin M), T.card = q ∧
        ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β (f T)).card : ℝ) <
          sourceGraphExpansion N d ell} ≤
      Real.exp ((ell : ℝ) * (2 + Real.log (d + 1) + d / Real.log ((N : ℝ) / ell) - d / 8)) := by
  by_cases hqM : q ≤ M
  · let F := (Finset.univ : Finset (Fin M)).powersetCard q
    let E := fun T : Finset (Fin M) => {x : Fin M × Fin C → Bool |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β (f T)).card : ℝ) <
        sourceGraphExpansion N d ell}
    let Q := (ell : ℝ) * (d / Real.log ((N : ℝ) / ell)) +
      (q : ℝ) * (Real.log (d + 1) - Real.log ((N : ℝ) / ell)) - d * ell / 8
    have hFixed (T : Finset (Fin M)) (hT : T ∈ F) :
        (bernoulliCubeLaw (Fin M × Fin C) p hp).real (E T) ≤ Real.exp Q := by
      have hTc := (Finset.mem_powersetCard.mp hT).2
      have h := bernoulli_ambient_small_set_fixed_expansion_failure hN hell
        (by simpa only [Fintype.card_fin] using hRows) p hp hDegree hd hSmall hL
        hβ hβOne e (f T) (hCard T hTc)
      simpa only [hInside T hTc] using h
    have hEvent : {x : Fin M × Fin C → Bool | ∃ T : Finset (Fin M), T.card = q ∧ x ∈ E T} =
        ⋃ T ∈ F, E T := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨T, hTc, hx⟩
        exact ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTc⟩, hx⟩
      · rintro ⟨T, hT, hx⟩
        exact ⟨T, (Finset.mem_powersetCard.mp hT).2, hx⟩
    change (bernoulliCubeLaw (Fin M × Fin C) p hp).real {x | ∃ T, T.card = q ∧ x ∈ E T} ≤ _
    rw [hEvent]
    calc
      _ ≤ ∑ T ∈ F, (bernoulliCubeLaw (Fin M × Fin C) p hp).real (E T) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _T ∈ F, Real.exp Q := Finset.sum_le_sum hFixed
      _ = (M.choose q : ℝ) * Real.exp Q := by
        simp only [Finset.sum_const, nsmul_eq_mul, F, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := small_set_subset_entropy_cancellation hN hMN hell hq hqM (by linarith)
  · have hEmpty : {x : Fin M × Fin C → Bool | ∃ T : Finset (Fin M), T.card = q ∧
        ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β (f T)).card : ℝ) <
          sourceGraphExpansion N d ell} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨T, hT, _⟩
      have hBound : T.card ≤ M := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
      omega
    rw [hEmpty, measureReal_empty]
    exact (Real.exp_pos _).le

theorem ambient_small_set_log_ratio_source_range {N ell : ℕ}
    (hN : 0 < N) (hell : 0 < ell) (p : ℝ≥0) {d : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 64 ≤ d)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) :
    64 ≤ Real.log ((N : ℝ) / ell) := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdLarge := large_expansion_degree_exp_lower.trans hd
  have hdPos : 0 < d := by linarith
  have hRatio : 2 * d ≤ (N : ℝ) / ell := by
    apply (le_div_iff₀ he).mpr
    have h := mul_le_mul_of_nonneg_left hSmall hn.le
    rw [hDegree]
    nlinarith
  have hLogD : 64 ≤ Real.log d := by
    have h := Real.log_le_log (Real.exp_pos 64) hd
    simpa only [Real.log_exp] using h
  exact hLogD.trans (Real.log_le_log hdPos (by linarith))

theorem bernoulli_small_set_family_expansion_source_range
    {N M C ell q : ℕ} (hN : 0 < N) (hMN : M ≤ N) (hell : 0 < ell)
    (hRows : 3 * (N : ℝ) / 4 ≤ M) (hq : q ≤ ell)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 64 ≤ d)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) (hβ : 0 < β) (hβOne : β ≤ 1)
    (e : Fin M ↪ Fin C) (f : Finset (Fin M) → Finset (Fin C))
    (hCard : ∀ T, T.card = q → (f T).card = ell)
    (hInside : ∀ T, T.card = q → (bernoulliUniqueInsideRows e (f T)).card = q) :
    (bernoulliCubeLaw (Fin M × Fin C) p hp).real {x |
      ∃ T : Finset (Fin M), T.card = q ∧
        ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β (f T)).card : ℝ) <
          sourceGraphExpansion N d ell} ≤ Real.exp (-d * ell / 16) := by
  have hL := ambient_small_set_log_ratio_source_range hN hell p hDegree hd hSmall
  have hdLarge := large_expansion_degree_exp_lower.trans hd
  apply (bernoulli_small_set_family_expansion_failure hN hMN hell hRows hq p hp hDegree
    (by linarith) hSmall (by linarith) hβ hβOne e f hCard hInside).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (ambient_small_set_expansion_entropy_coefficient hdLarge hL)
    (Nat.cast_nonneg ell)
  nlinarith

end CircularLaw
