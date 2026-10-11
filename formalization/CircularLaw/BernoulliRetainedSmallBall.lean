import CircularLaw.BernoulliRowSmallBall
import CircularLaw.BernoulliLLYRowAction
import CircularLaw.OrderedAdjointSmallBall

/-!
# Small balls for the actual retained shifted Bernoulli matrix

Restriction of the independent entry law gives the exact retained-row law.
The shift is absorbed into each deterministic scalar center. Ordered gaps
supply a large coefficient family after every constant vector shift.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_retained_action_probability_eq {n : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (I : Finset (Fin n)) (ζ : ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (T : ℝ) :
    (bernoulliSquareMatrixLaw n p hp).real {sample |
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ ^ 2 ≤ T} =
    (bernoulliCubeLaw (I × Fin n) p hp).real {sample |
      (∑ i : I, ‖(∑ j, weightedBernoulliValue (x j) (sample (i, j))) - ζ * x i.val‖ ^ 2) ≤ T} := by
  let e : I × Fin n ↪ Fin n × Fin n :=
    ⟨fun a => (a.1.val, a.2), by
      intro a b h
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst h
      · exact congrArg (fun x : Fin n × Fin n => x.2) h⟩
  have hLaw := finite_law_event_real
    (measurable_of_countable (fun x : BernoulliSquareSample n => fun a => x (e a)))
    (bernoulli_cube_law_restrict p hp e)
    (fun sample : I × Fin n → Bool =>
      (∑ i : I, ‖(∑ j, weightedBernoulliValue (x j) (sample (i, j))) - ζ * x i.val‖ ^ 2) ≤ T)
  simpa only [bernoulliSquareMatrixLaw, EuclideanSpace.norm_sq_eq,
    retained_shifted_bernoulli_apply_eq_full, shifted_bernoulli_matrix_apply_eq_row_form,
    e, Function.Embedding.coeFn_mk] using hLaw

theorem bernoulli_retained_rare_small_ball {n d : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (I S : Finset (Fin n))
    (hRare : (S.card : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (x : EuclideanSpace ℂ (Fin n)) {t : ℝ} (ht : 0 < t)
    (hLarge : ∀ j ∈ S, t ≤ ‖x j‖) (ζ : ℂ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ ^ 2 ≤
        t ^ 2 * ((S.card : ℝ) * ((d : ℝ) / n)) * I.card / 72} ≤
      Real.exp (-((S.card : ℝ) * ((d : ℝ) / n)) * I.card / 8) := by
  rw [sparseBernoulliMatrixLaw_eq hn hdn, bernoulli_retained_action_probability_eq]
  simpa only [rowBernoulliParameter_coe, Fintype.card_coe] using
    bernoulli_entries_rare_subset_norm_small_ball (ρ := I)
      (rowBernoulliParameter n d) (rowBernoulliParameter_le_one hn hdn)
      (fun j => x j) S (by simpa only [rowBernoulliParameter_coe] using hRare)
      ht hLarge (fun i => ζ * x i.val)

theorem bernoulli_retained_large_small_ball {n d : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (I S : Finset (Fin n)) (hS : S.Nonempty)
    (x : EuclideanSpace ℂ (Fin n)) {t τ : ℝ} (ht : 0 < t)
    (hLarge : ∀ j ∈ S, t ≤ ‖x j‖) (hτ : 1 ≤ τ) (ζ : ℂ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ ^ 2 ≤
        τ ^ 2 * t ^ 2 * I.card} ≤
      (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
        Real.sqrt ((S.card : ℝ) * ((d : ℝ) / n))) * τ ^ 2) ^ I.card := by
  have hn : 0 < n := by omega
  let p := rowBernoulliParameter n d
  have hp := rowBernoulliParameter_le_one hn (show d ≤ n by omega)
  have hpR : (p : ℝ) = (d : ℝ) / n := rowBernoulliParameter_coe n d
  have hpPos : 0 < (p : ℝ) := by rw [hpR]; positivity
  have hHalf : (p : ℝ) ≤ 1 / 2 := by
    rw [hpR]
    apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    have hDegreeR : 2 * (d : ℝ) ≤ n := by exact_mod_cast hDegree
    linarith
  rw [sparseBernoulliMatrixLaw_eq hn (show d ≤ n by omega),
    bernoulli_retained_action_probability_eq]
  simpa only [hpR, Fintype.card_coe] using bernoulli_entries_large_subset_norm_small_ball
    (ρ := I) p hp hpPos hHalf (fun j => x j) S hS ht hLarge hτ (fun i => ζ * x i.val)

theorem ordered_gap_large_shifted_coefficients {n rank tail : ℕ}
    (hRank : 0 < rank) (hFit : tail + rank ≤ n)
    (y : Fin n → ℂ) (c : ℂ) {t : ℝ}
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      2 * t + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) :
    ∃ S : Finset (Fin n), S.card = rank ∧ ∀ j ∈ S, t ≤ ‖y j + c‖ := by
  let L := orderedRankBlock (normOrderPerm y) 0
    (show 0 + 1 * rank ≤ n by omega) (0 : Fin 1)
  let R := orderedRankBlock (normOrderPerm y) tail
    (show tail + 1 * rank ≤ n by omega) (0 : Fin 1)
  have hL : L.card = rank := orderedRankBlock_card _ _ _ _
  have hR : R.card = rank := orderedRankBlock_card _ _ _ _
  apply separated_blocks_large_shifted_coefficients L R hL hR y c
  intro i hi j hj
  exact norm_ordered_blocks_separated y tail ⟨rank - 1, by omega⟩
    (by omega : 1 * rank ≤ n) (by omega : tail + 1 * rank ≤ n)
    (by change 1 * rank ≤ rank - 1 + 1; omega)
    hGap (0 : Fin 1) i hi j hj

theorem bernoulli_retained_ordered_rare_small_ball {n d rank tail : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (hRank : 0 < rank)
    (hFit : tail + rank ≤ n) (I : Finset (Fin n))
    (hRare : (rank : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (y : Fin n → ℂ) (c ζ : ℂ) {t : ℝ} (ht : 0 < t)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      2 * t + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
        (WithLp.toLp 2 (fun j => y j + c))‖ ^ 2 ≤
          t ^ 2 * ((rank : ℝ) * ((d : ℝ) / n)) * I.card / 72} ≤
      Real.exp (-((rank : ℝ) * ((d : ℝ) / n)) * I.card / 8) := by
  obtain ⟨S, hCard, hLarge⟩ := ordered_gap_large_shifted_coefficients hRank hFit y c hGap
  simpa only [hCard] using bernoulli_retained_rare_small_ball hn hdn I S
    (by simpa only [hCard] using hRare) (WithLp.toLp 2 (fun j => y j + c)) ht hLarge ζ

theorem bernoulli_retained_ordered_large_small_ball {n d rank tail : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hRank : 0 < rank)
    (hFit : tail + rank ≤ n) (I : Finset (Fin n))
    (y : Fin n → ℂ) (c ζ : ℂ) {t τ : ℝ} (ht : 0 < t) (hτ : 1 ≤ τ)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      2 * t + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
        (WithLp.toLp 2 (fun j => y j + c))‖ ^ 2 ≤ τ ^ 2 * t ^ 2 * I.card} ≤
      (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
        Real.sqrt ((rank : ℝ) * ((d : ℝ) / n))) * τ ^ 2) ^ I.card := by
  obtain ⟨S, hCard, hLarge⟩ := ordered_gap_large_shifted_coefficients hRank hFit y c hGap
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  simpa only [hCard] using bernoulli_retained_large_small_ball hd hDegree I S hS
    (WithLp.toLp 2 (fun j => y j + c)) ht hLarge hτ ζ

end CircularLaw
