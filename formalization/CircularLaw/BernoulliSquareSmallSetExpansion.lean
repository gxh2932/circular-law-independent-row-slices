import CircularLaw.BernoulliUniqueSmallSetFactors
import CircularLaw.ColumnDegreeEntropyBounds
import CircularLaw.NormalizedLogPowerSums

/-!
# Square Bernoulli expansion for a fixed small-set cardinality

The diagonal-row factor cancels the subset entropy. The resulting bound
is uniform over every column set of the specified cardinality under the
actual square law, with the numerical range kept explicit.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_unique_inside_rows_identity {ι : Type*} [Fintype ι] (S : Finset ι) :
    bernoulliUniqueInsideRows (Function.Embedding.refl ι) S = S := by
  ext j
  simp [bernoulliUniqueInsideRows]

theorem bernoulli_square_small_set_fixed_expansion_failure
    {N ell : ℕ} (hN : 0 < N) (hell : 0 < ell) (hellN : ell ≤ N)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ} (hDegree : d = (N : ℝ) * p) (hd : 1 ≤ d)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) (hL : 1 ≤ Real.log ((N : ℝ) / ell))
    (hβ : 0 < β) (hβOne : β ≤ 1) (S : Finset (Fin N)) (hS : S.card = ell) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
        sourceGraphExpansion N d ell} ≤
      Real.exp ((ell : ℝ) * (Real.log (d + 1) - Real.log ((N : ℝ) / ell) +
        d / Real.log ((N : ℝ) / ell) - d / 8)) := by
  let L := Real.log ((N : ℝ) / ell)
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have he : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hLp : 0 < L := by dsimp [L]; linarith
  have hRatio : 0 < (N : ℝ) / ell := div_pos hn he
  have hExp : Real.exp (-L) ≤ 1 / 2 := by
    apply (Real.exp_le_exp.mpr (by dsimp [L]; linarith : -L ≤ -1)).trans
    exact Real.exp_neg_one_lt_half.le
  have hExpEq : Real.exp (-L) = (ell : ℝ) / N := by
    rw [Real.exp_neg, Real.exp_log hRatio, inv_div]
  have hOutside : ((N - ell : ℕ) : ℝ) * ((ell : ℝ) * p) ≥ d * ell / 2 := by
    have heN : (ell : ℝ) ≤ (N : ℝ) / 2 := by
      have hScaled := mul_le_mul_of_nonneg_left hd he.le
      rw [hDegree] at hScaled
      have hMean := mul_le_mul_of_nonneg_left hSmall hn.le
      nlinarith
    rw [Nat.cast_sub hellN, hDegree]
    have h := mul_le_mul_of_nonneg_right (by linarith : (N : ℝ) / 2 ≤ N - ell)
      (mul_nonneg he.le p.coe_nonneg)
    nlinarith
  have hFactorEq : (ell : ℝ) * p + Real.exp (-L) = Real.exp (Real.log (d + 1) - L) := by
    rw [hExpEq, Real.exp_sub, Real.exp_log (by linarith : 0 < d + 1), Real.exp_log hRatio, hDegree]
    field_simp
  have hTail := bernoulli_unique_neighbourhood_small_set_lower_tail p hp
    (Function.Embedding.refl (Fin N)) S hβ hβOne hLp.le
    (by simpa only [hS] using hSmall) hExp (sourceGraphExpansion N d ell)
  simp only [bernoulli_unique_inside_rows_identity, hS, Fintype.card_fin] at hTail
  have hSubset : {x : BernoulliSquareSample N |
      ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
        sourceGraphExpansion N d ell} ⊆
      {x | ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x)
        (Function.Embedding.refl _) β S).card : ℝ) ≤ sourceGraphExpansion N d ell} := by
    intro x hx
    change ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x)
      (Function.Embedding.refl _) β S).card : ℝ) < sourceGraphExpansion N d ell at hx
    exact hx.le
  apply ((measureReal_mono hSubset (measure_ne_top _ _)).trans hTail).trans
  rw [hFactorEq, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hThreshold : L * sourceGraphExpansion N d ell = (ell : ℝ) * (d / L) := by
    dsimp [sourceGraphExpansion, L]
    field_simp
  rw [hThreshold]
  dsimp only [L]
  nlinarith

theorem bernoulli_square_small_set_cardinality_expansion_failure
    {N ell : ℕ} (hN : 0 < N) (hell : 0 < ell) (hellN : ell ≤ N)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ} (hDegree : d = (N : ℝ) * p) (hd : 1 ≤ d)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) (hL : 1 ≤ Real.log ((N : ℝ) / ell))
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x | ∃ S : Finset (Fin N), S.card = ell ∧
      ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
        sourceGraphExpansion N d ell} ≤
      Real.exp ((ell : ℝ) * (1 + Real.log (d + 1) + d / Real.log ((N : ℝ) / ell) - d / 8)) := by
  let F := (Finset.univ : Finset (Fin N)).powersetCard ell
  let E := fun S : Finset (Fin N) => {x : BernoulliSquareSample N |
    ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
      sourceGraphExpansion N d ell}
  let Q := (ell : ℝ) * (Real.log (d + 1) - Real.log ((N : ℝ) / ell) +
    d / Real.log ((N : ℝ) / ell) - d / 8)
  have hFixed (S : Finset (Fin N)) (hS : S ∈ F) :
      (bernoulliSquareMatrixLaw N p hp).real (E S) ≤ Real.exp Q :=
    bernoulli_square_small_set_fixed_expansion_failure hN hell hellN p hp hDegree hd hSmall hL
      hβ hβOne S (Finset.mem_powersetCard.mp hS).2
  have hEvent : {x : BernoulliSquareSample N | ∃ S : Finset (Fin N), S.card = ell ∧ x ∈ E S} =
      ⋃ S ∈ F, E S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨S, hCard, hx⟩
      exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hCard⟩, hx⟩
    · rintro ⟨S, hS, hx⟩
      exact ⟨S, (Finset.mem_powersetCard.mp hS).2, hx⟩
  change (bernoulliSquareMatrixLaw N p hp).real {x | ∃ S, S.card = ell ∧ x ∈ E S} ≤ _
  rw [hEvent]
  calc
    _ ≤ ∑ S ∈ F, (bernoulliSquareMatrixLaw N p hp).real (E S) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _S ∈ F, Real.exp Q := Finset.sum_le_sum hFixed
    _ = (N.choose ell : ℝ) * Real.exp Q := by
      simp only [Finset.sum_const, nsmul_eq_mul, F, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]
    _ ≤ Real.exp ((ell : ℝ) * (1 + Real.log ((N : ℝ) / ell))) * Real.exp Q :=
      mul_le_mul_of_nonneg_right (choose_le_ambient_log_entropy le_rfl hell hellN) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [Q]; ring

theorem small_set_expansion_log_degree_bound {d : ℝ} (hd : 65536 ≤ d) :
    1 + Real.log (d + 1) ≤ d / 64 := by
  have hdOne : 1 ≤ d := by linarith
  have hdPos : 0 < d := by linarith
  have hLog := log_nat_power_le_sqrt hdOne (by norm_num : (0 : ℕ) < 1)
  norm_num only [pow_one, Nat.cast_one, mul_one] at hLog
  have hLogPlus : Real.log (d + 1) ≤ Real.log 2 + Real.log d := by
    have h := Real.log_le_log (by linarith : 0 < d + 1) (by linarith : d + 1 ≤ 2 * d)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hdPos.ne'] at h
  have hRoot : 256 ≤ Real.sqrt d := by
    have h := Real.sqrt_le_sqrt hd
    norm_num at h
    exact h
  have hSquare := Real.sq_sqrt hdPos.le
  nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2),
    sq_nonneg (Real.sqrt d - 128)]

theorem small_set_expansion_entropy_coefficient {d L : ℝ}
    (hd : 65536 ≤ d) (hL : 64 ≤ L) :
    1 + Real.log (d + 1) + d / L - d / 8 ≤ -d / 16 := by
  have hLog := small_set_expansion_log_degree_bound hd
  have hDiv : d / L ≤ d / 64 := div_le_div_of_nonneg_left (by linarith)
    (by norm_num : (0 : ℝ) < 64) hL
  linarith

theorem bernoulli_square_small_set_cardinality_expansion_exponential_failure
    {N ell : ℕ} (hN : 0 < N) (hell : 0 < ell) (hellN : ell ≤ N)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ} (hDegree : d = (N : ℝ) * p) (hd : 65536 ≤ d)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) (hL : 64 ≤ Real.log ((N : ℝ) / ell))
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x | ∃ S : Finset (Fin N), S.card = ell ∧
      ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
        sourceGraphExpansion N d ell} ≤ Real.exp (-d * ell / 16) := by
  apply (bernoulli_square_small_set_cardinality_expansion_failure hN hell hellN p hp hDegree
    (by linarith) hSmall (by linarith) hβ hβOne).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (small_set_expansion_entropy_coefficient hd hL) (Nat.cast_nonneg ell)
  nlinarith

end CircularLaw
