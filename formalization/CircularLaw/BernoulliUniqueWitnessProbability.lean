import CircularLaw.FiniteProductEventLowerTail
import CircularLaw.BernoulliUniformRowLoad
import CircularLaw.BernoulliRowPatterns
import CircularLaw.RareBernoulliAtoms
import CircularLaw.LLYFirstWitnessProbability

/-!
# Unique selected-coordinate witnesses under the actual Bernoulli law

The witness coordinate belongs to L and every other selected coordinate
in J is zero. Exact disjoint pattern probabilities and the retained-row
product law give the lower tail used by the first steep class.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def bernoulliUniqueRowWitness {n : ℕ} (L J : Finset (Fin n)) (row : Fin n → Bool) : Prop :=
  ∃ j ∈ L, BernoulliRowSingle J j row

theorem bernoulli_row_single_iff_support_inter {n : ℕ}
    (J : Finset (Fin n)) (j : Fin n) (hj : j ∈ J) (row : Fin n → Bool) :
    BernoulliRowSingle J j row ↔ bernoulliSupport row ∩ J = {j} := by
  constructor
  · rintro ⟨hTrue, hFalse⟩
    ext k
    simp only [Finset.mem_inter, bernoulliSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hkTrue, hkJ⟩
      by_contra hkj
      have hkFalse := hFalse k hkJ hkj
      rw [hkFalse] at hkTrue
      exact Bool.false_ne_true hkTrue
    · intro hkj
      subst k
      exact ⟨hTrue, hj⟩
  · intro hInter
    have hjInter : j ∈ bernoulliSupport row ∩ J := by rw [hInter]; simp
    have hTrue : row j = true := by
      simpa only [bernoulliSupport, Finset.mem_filter, Finset.mem_univ, true_and] using
        (Finset.mem_inter.mp hjInter).1
    refine ⟨hTrue, ?_⟩
    intro k hkJ hkj
    cases hk : row k
    · rfl
    · have hkInter : k ∈ bernoulliSupport row ∩ J :=
        Finset.mem_inter.mpr ⟨by simp [bernoulliSupport, hk], hkJ⟩
      rw [hInter] at hkInter
      exact False.elim (hkj (Finset.mem_singleton.mp hkInter))

theorem bernoulli_unique_row_witness_probability {n : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (L J : Finset (Fin n)) (hLJ : L ⊆ J) :
    (bernoulliCubeLaw (Fin n) p hp).real {row | bernoulliUniqueRowWitness L J row} =
      (L.card : ℝ) * p * (1 - (p : ℝ)) ^ (J.card - 1) := by
  let E := fun j : Fin n => {row : Fin n → Bool | BernoulliRowSingle J j row}
  have hEvent : {row : Fin n → Bool | bernoulliUniqueRowWitness L J row} = ⋃ j ∈ L, E j := by
    ext row
    simp only [Set.mem_setOf_eq, bernoulliUniqueRowWitness, Set.mem_iUnion, E, exists_prop]
  have hDisjoint : Set.PairwiseDisjoint (L : Set (Fin n)) E := by
    intro i _ j hj hij
    apply Set.disjoint_left.mpr
    intro row hri hrj
    have hTrue : row j = true := hrj.1
    have hFalse : row j = false := hri.2 j (hLJ hj) (Ne.symm hij)
    rw [hFalse] at hTrue
    exact Bool.false_ne_true hTrue
  rw [hEvent, measureReal_biUnion_finset hDisjoint
    (fun j _ => (Set.to_countable (E j)).measurableSet) (fun _ _ => measure_ne_top _ _)]
  calc
    _ = ∑ _j ∈ L, (p : ℝ) * (1 - (p : ℝ)) ^ (J.card - 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact bernoulli_row_single_probability p hp J (hLJ hj)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem bernoulli_retained_few_events_probability {n : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (I : Finset (Fin n)) (E : (Fin n → Bool) → Prop) (T : ℝ)
    (hMean : (4 / 5 : ℝ) * T ≤ (I.card : ℝ) * (bernoulliCubeLaw (Fin n) p hp).real {row | E row}) :
    (bernoulliSquareMatrixLaw n p hp).real {sample |
      (bernoulliRetainedEventCount I E sample : ℝ) < T / 2} ≤ Real.exp (-uniqueWitnessRate * T) := by
  let e : I × Fin n ↪ Fin n × Fin n :=
    ⟨fun a => (a.1.val, a.2), by
      intro a b h
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst h
      · exact congrArg (fun x : Fin n × Fin n => x.2) h⟩
  have hRestrict := finite_law_event_real
    (measurable_of_countable (fun x : BernoulliSquareSample n => fun a => x (e a)))
    (bernoulli_cube_law_restrict p hp e)
    (fun x : I × Fin n → Bool =>
      (coordinateEventCount (fun _ : I => E) (Function.curry x) : ℝ) < T / 2)
  have hCurry := finite_law_event_real
    (bernoulli_row_product_measure_preserving (ρ := I) (ι := Fin n) p hp).measurable
    (bernoulli_row_product_map (ρ := I) (ι := Fin n) p hp)
    (fun rows : I → Fin n → Bool => (coordinateEventCount (fun _ : I => E) rows : ℝ) < T / 2)
  have hMean' : (4 / 5 : ℝ) * T ≤
      ∑ _i : I, (bernoulliCubeLaw (Fin n) p hp).real {row | E row} := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] using hMean
  have hProb := finite_product_event_lower_tail_four_fifths
    (fun _ : I => bernoulliCubeLaw (Fin n) p hp) (fun _ : I => E) T hMean'
  simpa only [bernoulliSquareMatrixLaw, bernoulli_retained_event_count_eq_coordinates,
    Function.curry, e, Function.Embedding.coeFn_mk] using
    hRestrict.trans hCurry |>.le.trans hProb

theorem bernoulli_eligible_unique_witness_failure {n d : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (I L J : Finset (Fin n)) (hLJ : L ⊆ J)
    (hI : (99 / 100 : ℝ) * n ≤ I.card) (hSmall : 16 * d * J.card ≤ n) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      (bernoulliRetainedEventCount (I \ J) (bernoulliUniqueRowWitness L J) sample : ℝ) <
        (d : ℝ) * L.card / 2} ≤ Real.exp (-uniqueWitnessRate * d * L.card) := by
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  let p := rowBernoulliParameter n d
  have hp := rowBernoulliParameter_le_one hnPos hdn
  have hpR : (p : ℝ) = (d : ℝ) / n := rowBernoulliParameter_coe n d
  have hRows : (9 / 10 : ℝ) * n ≤ ((I \ J).card : ℝ) := by
    have h := eligible_witness_rows_card I J hI rfl
      (lly_small_unique_witness_loss hn hd hSmall).1
    simpa only [Fintype.card_coe] using h
  have hSmallR : (16 : ℝ) * d * J.card ≤ n := by exact_mod_cast hSmall
  have hLoad : (J.card : ℝ) * p ≤ 1 / 16 := by
    rw [hpR, ← mul_div_assoc]
    apply (div_le_iff₀ hnR).mpr
    nlinarith only [hSmallR]
  have hExponent : ((J.card - 1 : ℕ) : ℝ) * p ≤ 1 / 16 :=
    (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.sub_le J.card 1 : ((J.card - 1 : ℕ) : ℝ) ≤ J.card) p.coe_nonneg).trans hLoad
  have hFactor : (9 / 10 : ℝ) ≤ (1 - (p : ℝ)) ^ (J.card - 1) := by
    have h := bernoulli_zero_selection_probability_lower p hp (J.card - 1)
    linarith only [h, hExponent]
  have hProb : (9 / 10 : ℝ) * ((L.card : ℝ) * p) ≤
      (bernoulliCubeLaw (Fin n) p hp).real {row | bernoulliUniqueRowWitness L J row} := by
    rw [bernoulli_unique_row_witness_probability p hp L J hLJ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hFactor
      (mul_nonneg (Nat.cast_nonneg L.card) p.coe_nonneg)
  have hMean : (4 / 5 : ℝ) * ((d : ℝ) * L.card) ≤
      ((I \ J).card : ℝ) * (bernoulliCubeLaw (Fin n) p hp).real {row | bernoulliUniqueRowWitness L J row} := by
    have hCoeff : (0 : ℝ) ≤ (9 / 10 : ℝ) * ((L.card : ℝ) * p) := by positivity
    calc
      _ ≤ (81 / 100 : ℝ) * ((d : ℝ) * L.card) := by
        nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (Nat.cast_nonneg (α := ℝ) L.card)]
      _ = ((9 / 10 : ℝ) * n) * ((9 / 10 : ℝ) * ((L.card : ℝ) * p)) := by
        rw [hpR]
        field_simp
        ring
      _ ≤ ((I \ J).card : ℝ) * ((9 / 10 : ℝ) * ((L.card : ℝ) * p)) :=
        mul_le_mul_of_nonneg_right hRows hCoeff
      _ ≤ _ := mul_le_mul_of_nonneg_left hProb (Nat.cast_nonneg _)
  rw [sparseBernoulliMatrixLaw_eq hnPos hdn]
  simpa only [mul_assoc] using bernoulli_retained_few_events_probability p hp
    (I \ J) (bernoulliUniqueRowWitness L J) ((d : ℝ) * L.card) hMean

end CircularLaw
