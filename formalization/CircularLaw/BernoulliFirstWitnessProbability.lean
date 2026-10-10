import CircularLaw.BernoulliUniqueWitnessProbability

/-!
# Uniform first-steep witnesses under the actual Bernoulli law

A union over all disjoint coordinate pairs pays the same finite pair
entropy as the slice proof. The clipped adjacent-rank ratio absorbs it.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def BernoulliUniformUniqueWitness {n : ℕ} (d : ℕ) (I : Finset (Fin n)) (s t : ℕ)
    (sample : BernoulliSquareSample n) : Prop :=
  ∀ L R : Finset (Fin n), Disjoint L R → L.card = s → (L ∪ R).card = t →
    (d : ℝ) * s / 2 ≤
      (bernoulliRetainedEventCount (I \ (L ∪ R)) (bernoulliUniqueRowWitness L (L ∪ R)) sample : ℝ)

theorem bernoulli_uniform_unique_witness_failure_counting {n d s t : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (I : Finset (Fin n))
    (hI : (99 / 100 : ℝ) * n ≤ I.card) (hSmall : 16 * d * t ≤ n) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliUniformUniqueWitness d I s t sample} ≤
      (n.choose t : ℝ) * t.choose s * Real.exp (-uniqueWitnessRate * d * s) := by
  let μ := sparseBernoulliMatrixLaw n d
  let E : DisjointSetPair n s t → BernoulliSquareSample n → Prop := fun p sample =>
    (bernoulliRetainedEventCount (I \ (p.val.1 ∪ p.val.2))
      (bernoulliUniqueRowWitness p.val.1 (p.val.1 ∪ p.val.2)) sample : ℝ) < (d : ℝ) * s / 2
  have hEvent : ∀ sample : BernoulliSquareSample n, ¬BernoulliUniformUniqueWitness d I s t sample →
      ∃ p ∈ (Finset.univ : Finset (DisjointSetPair n s t)), E p sample := by
    intro sample hBad
    unfold BernoulliUniformUniqueWitness at hBad
    push_neg at hBad
    obtain ⟨L, R, hDis, hL, hUnion, hCount⟩ := hBad
    exact ⟨⟨(L, R), hDis, hL, hUnion⟩, Finset.mem_univ _, hCount⟩
  apply (measureReal_mono (μ := μ) hEvent (h₂ := by finiteness)).trans
  apply (finite_measure_finset_exists_le μ Finset.univ E).trans
  calc
    _ ≤ ∑ _p : DisjointSetPair n s t, Real.exp (-uniqueWitnessRate * d * s) := by
      apply Finset.sum_le_sum
      intro p _
      have h := bernoulli_eligible_unique_witness_failure hn hd hdn I p.val.1 (p.val.1 ∪ p.val.2)
        Finset.subset_union_left hI (by simpa only [p.property.2.2] using hSmall)
      simpa only [p.property.2.1] using h
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_disjoint_set_pairs,
        Nat.cast_mul]

theorem bernoulli_uniform_unique_witness_failure_entropy {n d s t : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (htPos : 0 < t) (htn : t ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card) (hSmall : 16 * d * t ≤ n) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliUniformUniqueWitness d I s t sample} ≤
      Real.exp (-uniqueWitnessRate * d * s + (t : ℝ) *
        (Real.log (Real.exp 1 * n / t) + Real.log 2)) := by
  apply (bernoulli_uniform_unique_witness_failure_counting hn hd hdn I hI hSmall).trans
  apply (mul_le_mul_of_nonneg_right
    (choose_pair_entropy (by omega : 0 < n) htPos htn (s := s)) (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

theorem bernoulli_lly_first_pair_witness_failure {n d ℓ s t : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hs : 0 < s) (hst : s ≤ t) (htn : t ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (hSmall : 16 * d * t ≤ n) (hRatio : t ≤ ℓ * s)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliUniformUniqueWitness d I s t sample} ≤
      Real.exp (-(uniqueWitnessRate / 2) * d) := by
  have hEntropy := lly_first_pair_entropy_absorbed (by omega : 0 < n) hs hst hRatio hBudget
  apply (bernoulli_uniform_unique_witness_failure_entropy hn hd hdn
    (by omega : 0 < t) htn I hI hSmall).trans
  apply Real.exp_le_exp.mpr
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hDs : (d : ℝ) ≤ (d : ℝ) * s := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsR (Nat.cast_nonneg (α := ℝ) d)
  have hScale := mul_le_mul_of_nonneg_left hDs (le_of_lt uniqueWitnessRate_pos)
  nlinarith

def BernoulliLLYFirstWitness {n : ℕ} (d : ℕ) (I : Finset (Fin n)) (ℓ r k : ℕ)
    (sample : BernoulliSquareSample n) : Prop :=
  ∀ i ∈ Finset.range (r + 1),
    BernoulliUniformUniqueWitness d I (llyFirstRank ℓ k i) (llyFirstRank ℓ k (i + 1)) sample

theorem bernoulli_lly_first_witness_failure_probability {n d ℓ r k : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (hSmall : 16 * d * k ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliLLYFirstWitness d I ℓ r k sample} ≤
      (r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d) := by
  let μ := sparseBernoulliMatrixLaw n d
  apply (measureReal_mono (μ := μ) ?_ (h₂ := by finiteness)).trans
    ((finite_measure_finset_exists_le μ (Finset.range (r + 1))
      (fun i sample => ¬BernoulliUniformUniqueWitness d I (llyFirstRank ℓ k i)
        (llyFirstRank ℓ k (i + 1)) sample)).trans ?_)
  · intro sample hBad
    unfold BernoulliLLYFirstWitness at hBad
    push_neg at hBad
    exact hBad
  · calc
      _ ≤ ∑ _i ∈ Finset.range (r + 1), Real.exp (-(uniqueWitnessRate / 2) * d) := by
        apply Finset.sum_le_sum
        intro i _
        exact bernoulli_lly_first_pair_witness_failure hn hd hdn (lly_first_rank_pos hℓ hk i)
          (lly_first_rank_mono hℓ (by omega : i ≤ i + 1))
          ((lly_first_rank_le ℓ k (i + 1)).trans hkn) I hI
          ((Nat.mul_le_mul_left (16 * d) (lly_first_rank_le ℓ k (i + 1))).trans hSmall)
          (lly_first_rank_ratio hℓ i) hBudget
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem bernoulli_lly_first_witness_failure_polynomial {n d ℓ r k : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (hSmall : 16 * d * k ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (hScales : r + 1 ≤ n) (A : ℝ)
    (hDegree : (2 / uniqueWitnessRate) * (A + 1) * Real.log (n : ℝ) ≤ d) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliLLYFirstWitness d I ℓ r k sample} ≤
      (n : ℝ) ^ (-A) := by
  apply (bernoulli_lly_first_witness_failure_probability hn hd hdn hℓ hk hkn I hI hSmall hBudget).trans
  have hScalesR : ((r + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hScales
  have hExponent : -(uniqueWitnessRate / 2) * (d : ℝ) = -(d : ℝ) / (2 / uniqueWitnessRate) := by
    field_simp
  calc
    _ ≤ (n : ℝ) * Real.exp (-(uniqueWitnessRate / 2) * d) :=
      mul_le_mul_of_nonneg_right hScalesR (Real.exp_pos _).le
    _ = (n : ℝ) * Real.exp (-(d : ℝ) / (2 / uniqueWitnessRate)) := by rw [hExponent]
    _ ≤ _ := dimension_exp_degree_le_rpow (by omega : 0 < n)
      (div_pos (by norm_num) uniqueWitnessRate_pos) hDegree

end CircularLaw
