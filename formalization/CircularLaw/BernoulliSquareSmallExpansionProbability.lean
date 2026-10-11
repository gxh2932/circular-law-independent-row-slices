import CircularLaw.BernoulliSquareSmallSetExpansion

/-!
# Actual square Bernoulli expansion throughout the small-set range

For sufficiently large effective degree, every set of size at least k
and with |S|*p at most one half has the source unique expansion, outside
one event of probability at most 2*exp(-d*k/16).
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem large_expansion_degree_exp_lower : (65536 : ℝ) ≤ Real.exp 64 := by
  have hBase : (17 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hPower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 17) hBase 4
  rw [show (64 : ℝ) = (4 : ℕ) * 16 by norm_num, Real.exp_nat_mul]
  norm_num at hPower
  linarith

theorem bernoulli_square_small_cardinality_expansion_source_range
    {N ell : ℕ} (hN : 0 < N) (hell : 0 < ell) (hellN : ell ≤ N)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ} (hDegree : d = (N : ℝ) * p)
    (hd : Real.exp 64 ≤ d) (hSmall : (ell : ℝ) * p ≤ 1 / 2)
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x | ∃ S : Finset (Fin N), S.card = ell ∧
      ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
        sourceGraphExpansion N d ell} ≤ Real.exp (-d * ell / 16) := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdLarge : 65536 ≤ d := large_expansion_degree_exp_lower.trans hd
  have hdPos : 0 < d := by linarith
  have hRatio : 2 * d ≤ (N : ℝ) / ell := by
    apply (le_div_iff₀ he).mpr
    have h := mul_le_mul_of_nonneg_left hSmall hn.le
    rw [hDegree]
    nlinarith
  have hLogD : 64 ≤ Real.log d := by
    have h := Real.log_le_log (Real.exp_pos 64) hd
    simpa only [Real.log_exp] using h
  have hLogRatio : Real.log d ≤ Real.log ((N : ℝ) / ell) :=
    Real.log_le_log hdPos (by linarith)
  exact bernoulli_square_small_set_cardinality_expansion_exponential_failure hN hell hellN p hp
    hDegree hdLarge hSmall (hLogD.trans hLogRatio) hβ hβOne

theorem geometric_nonnegative_powers_sum_le_two {q : ℝ}
    (hq : 0 ≤ q) (hqHalf : q ≤ 1 / 2) (L : ℕ) :
    (∑ j ∈ Finset.range L, q ^ j) ≤ 2 := by
  have hSharp : ∀ m : ℕ, (∑ j ∈ Finset.range m, q ^ j) ≤ 2 - 2 * q ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hPower := mul_le_mul_of_nonneg_left hqHalf (pow_nonneg hq m)
      linarith
  exact (hSharp L).trans (sub_le_self _ (by positivity))

theorem bernoulli_square_small_set_expansion_failure
    {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ} (hDegree : d = (N : ℝ) * p)
    (hd : Real.exp 64 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x | ∃ S : Finset (Fin N), k ≤ S.card ∧
      (S.card : ℝ) * p ≤ 1 / 2 ∧
      ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
        sourceGraphExpansion N d S.card} ≤ 2 * Real.exp (-d * k / 16) := by
  let E := fun j : ℕ => {x : BernoulliSquareSample N | ∃ S : Finset (Fin N), S.card = k + j ∧
    (S.card : ℝ) * p ≤ 1 / 2 ∧
    ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
      sourceGraphExpansion N d S.card}
  have hFixed (j : ℕ) : (bernoulliSquareMatrixLaw N p hp).real (E j) ≤
      Real.exp (-d * ((k + j : ℕ) : ℝ) / 16) := by
    by_cases hCard : k + j ≤ N
    · by_cases hSmall : ((k + j : ℕ) : ℝ) * p ≤ 1 / 2
      · have hSubset : E j ⊆ {x : BernoulliSquareSample N | ∃ S : Finset (Fin N), S.card = k + j ∧
          ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
            sourceGraphExpansion N d ((k + j : ℕ) : ℝ)} := by
          rintro x ⟨S, hS, _, hBad⟩
          exact ⟨S, hS, by simpa only [hS] using hBad⟩
        exact (measureReal_mono hSubset (measure_ne_top _ _)).trans
          (bernoulli_square_small_cardinality_expansion_source_range hN (by omega) hCard p hp hDegree
            hd hSmall hβ hβOne)
      · have hEmpty : E j = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro x ⟨S, hS, hSize, _⟩
          exact hSmall (by simpa only [hS] using hSize)
        rw [hEmpty, measureReal_empty]
        exact (Real.exp_pos _).le
    · have hEmpty : E j = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨S, hS, _, _⟩
        have hUpper : S.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
        omega
      rw [hEmpty, measureReal_empty]
      exact (Real.exp_pos _).le
  have hSubset : {x : BernoulliSquareSample N | ∃ S : Finset (Fin N), k ≤ S.card ∧
      (S.card : ℝ) * p ≤ 1 / 2 ∧
      ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
        sourceGraphExpansion N d S.card} ⊆ ⋃ j ∈ Finset.range (N + 1), E j := by
    rintro x ⟨S, hLower, hSmall, hBad⟩
    have hUpper : S.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    refine Set.mem_iUnion.mpr ⟨S.card - k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),
      S, by omega, hSmall, hBad⟩⟩
  have hPoint (j : ℕ) : Real.exp (-d * ((k + j : ℕ) : ℝ) / 16) =
      Real.exp (-d * k / 16) * (Real.exp (-d / 16)) ^ j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hHalf : Real.exp (-d / 16) ≤ 1 / 2 := by
    apply (Real.exp_le_exp.mpr (by linarith [large_expansion_degree_exp_lower.trans hd] : -d / 16 ≤ -1)).trans
    exact Real.exp_neg_one_lt_half.le
  calc
    _ ≤ (bernoulliSquareMatrixLaw N p hp).real (⋃ j ∈ Finset.range (N + 1), E j) :=
      measureReal_mono hSubset (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range (N + 1), (bernoulliSquareMatrixLaw N p hp).real (E j) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1), Real.exp (-d * ((k + j : ℕ) : ℝ) / 16) :=
      Finset.sum_le_sum (fun j _ => hFixed j)
    _ = Real.exp (-d * k / 16) * ∑ j ∈ Finset.range (N + 1), (Real.exp (-d / 16)) ^ j := by
      simp_rw [hPoint]
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (geometric_nonnegative_powers_sum_le_two (Real.exp_pos _).le hHalf (N + 1))
        (Real.exp_pos (-d * k / 16)).le
      simpa only [mul_comm] using h

end CircularLaw
