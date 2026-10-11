import CircularLaw.BernoulliColumnSubsetCounts
import CircularLaw.ColumnDegreeEntropyBounds

/-!
# The actual Bernoulli uniform column-degree budget

Every column subset satisfies the graph degree budget with constant eight,
except on an event of probability at most N^(-3). The rectangular row and
column cardinalities may be smaller than the ambient N. The final bound
also applies to the actual sparse square law, retaining its parameter.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal Matrix

namespace CircularLaw

theorem bernoulli_column_subset_cardinality_failure_bound
    {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) {N ell : ℕ} (hRows : Fintype.card ρ ≤ N)
    (hCols : Fintype.card ι ≤ N) (hell : 0 < ell) (hellCols : ell ≤ Fintype.card ι)
    {d : ℝ} (hd : 1 ≤ d) (hDegree : d = (N : ℝ) * p) :
    (bernoulliCubeLaw (ρ × ι) p hp).real {x | ∃ T : Finset ι, T.card = ell ∧
      8 * (ell : ℝ) * (d + Real.log ((N : ℝ) / ell)) <
        ∑ j ∈ T, ((matrixColumnSupport (bernoulliRectangularMatrix x) j).card : ℝ)} ≤
      Real.exp (-3 * Real.log (N : ℝ)) * Real.exp (-2 * d * ell) := by
  let S := (Finset.univ : Finset ι).powersetCard ell
  let U := (ell : ℝ) * d * (Real.exp 1 - 1) - 8 * ell * (d + Real.log ((N : ℝ) / ell))
  let E := fun T : Finset ι => {x : ρ × ι → Bool |
    8 * (ell : ℝ) * (d + Real.log ((N : ℝ) / ell)) <
      ∑ j ∈ T, ((matrixColumnSupport (bernoulliRectangularMatrix x) j).card : ℝ)}
  have hFixed (T : Finset ι) (hT : T ∈ S) :
      (bernoulliCubeLaw (ρ × ι) p hp).real (E T) ≤ Real.exp U := by
    have hCard : T.card = ell := (Finset.mem_powersetCard.mp hT).2
    have hThreshold := bernoulli_column_subset_count_upper_tail (ρ := ρ) p hp T (by norm_num : (0 : ℝ) ≤ 1)
      (8 * (ell : ℝ) * (d + Real.log ((N : ℝ) / ell)))
    rw [hCard, one_mul] at hThreshold
    have hEvent : E T ⊆ {x : ρ × ι → Bool |
        8 * (ell : ℝ) * (d + Real.log ((N : ℝ) / ell)) ≤
          ∑ j ∈ T, ((matrixColumnSupport (bernoulliRectangularMatrix x) j).card : ℝ)} := by
      intro x hx
      change 8 * (ell : ℝ) * (d + Real.log ((N : ℝ) / ell)) <
        ∑ j ∈ T, ((matrixColumnSupport (bernoulliRectangularMatrix x) j).card : ℝ) at hx
      exact hx.le
    apply ((measureReal_mono (μ := bernoulliCubeLaw (ρ × ι) p hp) hEvent).trans hThreshold).trans
    apply Real.exp_le_exp.mpr
    have hMean : (Fintype.card ρ : ℝ) * ell * p ≤ (ell : ℝ) * d := by
      rw [hDegree]
      have h := mul_le_mul_of_nonneg_right (by exact_mod_cast hRows : (Fintype.card ρ : ℝ) ≤ N)
        (mul_nonneg (Nat.cast_nonneg ell) p.coe_nonneg)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    have hExp : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
    exact sub_le_sub_right (mul_le_mul_of_nonneg_right hMean hExp) _
  have hEventEq : {x : ρ × ι → Bool | ∃ T : Finset ι, T.card = ell ∧ x ∈ E T} =
      ⋃ T ∈ S, E T := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨T, hCard, hx⟩
      exact ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hCard⟩, hx⟩
    · rintro ⟨T, hT, hx⟩
      exact ⟨T, (Finset.mem_powersetCard.mp hT).2, hx⟩
  change (bernoulliCubeLaw (ρ × ι) p hp).real {x | ∃ T, T.card = ell ∧ x ∈ E T} ≤ _
  rw [hEventEq]
  calc
    _ ≤ ∑ T ∈ S, (bernoulliCubeLaw (ρ × ι) p hp).real (E T) := measureReal_biUnion_finset_le S E
    _ ≤ ∑ T ∈ S, Real.exp U := Finset.sum_le_sum (fun T hT => hFixed T hT)
    _ = (Fintype.card ι |>.choose ell : ℝ) * Real.exp U := by
      simp only [Finset.sum_const, nsmul_eq_mul, S, Finset.card_powersetCard, Finset.card_univ]
    _ ≤ Real.exp ((ell : ℝ) * (1 + Real.log ((N : ℝ) / ell))) * Real.exp U :=
      mul_le_mul_of_nonneg_right (choose_le_ambient_log_entropy hCols hell hellCols) (Real.exp_pos U).le
    _ = Real.exp ((ell : ℝ) * (1 + Real.log ((N : ℝ) / ell)) + U) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-3 * Real.log (N : ℝ) - 2 * d * ell) := by
      apply Real.exp_le_exp.mpr
      dsimp [U]
      linarith [column_degree_entropy_exponent_le hell (hellCols.trans hCols) hd]
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; congr 1; congr 1; ring

theorem exp_negative_three_log_eq_inv_cube {N : ℕ} (hN : 0 < N) :
    Real.exp (-3 * Real.log (N : ℝ)) = ((N : ℝ)⁻¹) ^ 3 := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [show -3 * Real.log (N : ℝ) = (3 : ℕ) * (-Real.log (N : ℝ)) by push_cast; ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log hn]

theorem bernoulli_rectangular_column_degree_budget_failure
    {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (hRows : Fintype.card ρ ≤ N) (hCols : Fintype.card ι ≤ N)
    {d : ℝ} (hd : 1 ≤ d) (hDegree : d = (N : ℝ) * p) :
    (bernoulliCubeLaw (ρ × ι) p hp).real {x |
      ¬ MatrixColumnDegreeBudget (bernoulliRectangularMatrix x) 8 N d} ≤ ((N : ℝ)⁻¹) ^ 3 := by
  let E := fun j : ℕ => {x : ρ × ι → Bool | ∃ T : Finset ι, T.card = j + 1 ∧
    8 * ((j + 1 : ℕ) : ℝ) * (d + Real.log ((N : ℝ) / (j + 1 : ℕ))) <
      ∑ k ∈ T, ((matrixColumnSupport (bernoulliRectangularMatrix x) k).card : ℝ)}
  have hSubset : {x : ρ × ι → Bool | ¬ MatrixColumnDegreeBudget (bernoulliRectangularMatrix x) 8 N d} ⊆
      ⋃ j ∈ Finset.range (Fintype.card ι), E j := by
    intro x hx
    obtain ⟨T, hFailure⟩ := not_forall.mp hx
    have hStrict := lt_of_not_ge hFailure
    have hCardPos : 0 < T.card := by
      by_contra hNot
      have hEmpty : T = ∅ := Finset.card_eq_zero.mp (by omega)
      simp only [hEmpty, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul,
        lt_self_iff_false] at hStrict
    have hCardUpper : T.card ≤ Fintype.card ι := Finset.card_le_univ T
    have hRange : T.card - 1 ∈ Finset.range (Fintype.card ι) := Finset.mem_range.mpr (by omega)
    refine Set.mem_iUnion.mpr ⟨T.card - 1, Set.mem_iUnion.mpr ⟨hRange, T, by omega, ?_⟩⟩
    have hRank : T.card - 1 + 1 = T.card := by omega
    change 8 * ((T.card - 1 + 1 : ℕ) : ℝ) * (d + Real.log ((N : ℝ) / (T.card - 1 + 1 : ℕ))) < _
    simpa only [hRank] using hStrict
  have hBound : (bernoulliCubeLaw (ρ × ι) p hp).real {x |
      ¬ MatrixColumnDegreeBudget (bernoulliRectangularMatrix x) 8 N d} ≤ Real.exp (-3 * Real.log (N : ℝ)) := by
    calc
      _ ≤ (bernoulliCubeLaw (ρ × ι) p hp).real (⋃ j ∈ Finset.range (Fintype.card ι), E j) :=
        measureReal_mono hSubset (measure_ne_top _ _)
      _ ≤ ∑ j ∈ Finset.range (Fintype.card ι), (bernoulliCubeLaw (ρ × ι) p hp).real (E j) :=
        measureReal_biUnion_finset_le _ E
      _ ≤ ∑ j ∈ Finset.range (Fintype.card ι),
          Real.exp (-3 * Real.log (N : ℝ)) * Real.exp (-2 * d * ((j + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact bernoulli_column_subset_cardinality_failure_bound p hp hRows hCols (by omega)
          (by simpa only [Finset.mem_range] using hj) hd hDegree
      _ = Real.exp (-3 * Real.log (N : ℝ)) *
          (∑ j ∈ Finset.range (Fintype.card ι), Real.exp (-2 * d * ((j + 1 : ℕ) : ℝ))) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (sum_positive_degree_exponentials_le_one hd (Fintype.card ι)) (Real.exp_pos _).le
  simpa only [exp_negative_three_log_eq_inv_cube hN] using hBound

theorem bernoulli_square_column_degree_budget_failure {N : ℕ} (hN : 0 < N)
    (p : ℝ≥0) (hp : p ≤ 1) (hd : 1 ≤ (N : ℝ) * p) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ MatrixColumnDegreeBudget (bernoulliSquareMatrix x) 8 N ((N : ℝ) * p)} ≤ ((N : ℝ)⁻¹) ^ 3 := by
  simpa only [bernoulliSquareMatrixLaw, bernoulli_rectangular_square_eq] using
    bernoulli_rectangular_column_degree_budget_failure p hp hN
      (by simp : Fintype.card (Fin N) ≤ N) (by simp : Fintype.card (Fin N) ≤ N) hd rfl

theorem sparse_bernoulli_column_degree_budget_failure {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d) (hdN : d ≤ N) :
    (sparseBernoulliMatrixLaw N d).real {x |
      ¬ MatrixColumnDegreeBudget (bernoulliSquareMatrix x) 8 N d} ≤ ((N : ℝ)⁻¹) ^ 3 := by
  rw [sparseBernoulliMatrixLaw_eq hN hdN]
  have hDegree : (d : ℝ) = (N : ℝ) * rowBernoulliParameter N d := by
    rw [rowBernoulliParameter_coe]
    field_simp
  rw [hDegree]
  exact bernoulli_square_column_degree_budget_failure hN _ _ (by rw [← hDegree]; exact_mod_cast hd)

end CircularLaw
