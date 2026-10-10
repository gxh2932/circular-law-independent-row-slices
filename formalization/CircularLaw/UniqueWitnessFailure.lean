import CircularLaw.UniformWitnessFailure

/-!
# Uniform unique-coordinate witnesses outside the coordinate sets

For each pair the eligible rows are `I \ (L union R)`. Restriction of the
actual matrix law supplies precisely the independent rows being counted.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def UniformUniqueWitness {n d : ℕ} (I : Finset (Fin n)) (s t : ℕ)
    (rows : RowSliceMatrix n d) : Prop :=
  ∀ L R : Finset (Fin n), Disjoint L R → L.card = s → (L ∪ R).card = t →
    (d : ℝ) * s / 2 ≤
      (uniqueWitnessRows L (L ∪ R) (fun i : ↥(I \ (L ∪ R)) => rows i.val)).card

theorem eligible_witness_rows_card {n t : ℕ} (I J : Finset (Fin n))
    (hI : (99 / 100 : ℝ) * n ≤ I.card) (hJ : J.card = t)
    (ht : (t : ℝ) ≤ (9 / 100 : ℝ) * n) :
    (9 / 10 : ℝ) * n ≤ Fintype.card ↥(I \ J) := by
  have hInter := Finset.card_le_card (Finset.inter_subset_right (s₁ := I) (s₂ := J))
  have hCount := Finset.card_sdiff_add_card_inter I J
  have hNat : I.card ≤ (I \ J).card + J.card := by omega
  have hReal : (I.card : ℝ) ≤ (I \ J).card + J.card := by exact_mod_cast hNat
  rw [Fintype.card_coe]
  rw [hJ] at hReal
  linarith

theorem eligible_unique_witness_failure {n d t : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (hdn : d ≤ n) (I L J : Finset (Fin n)) (hLJ : L ⊆ J)
    (hI : (99 / 100 : ℝ) * n ≤ I.card) (hJ : J.card = t)
    (ht : (t : ℝ) ≤ (9 / 100 : ℝ) * n)
    (hLoss : ((d : ℝ) - 1) * ((t : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 10) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ((uniqueWitnessRows L J (fun i : ↥(I \ J) => rows i.val)).card : ℝ) <
        (d : ℝ) * L.card / 2) ≤ Real.exp (-uniqueWitnessRate * d * L.card) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  rw [uniformProbability_pi_restrict (α := fun _ : Fin n => RowSlice n d) (I \ J)
    (fun retained => ((uniqueWitnessRows L J retained).card : ℝ) < (d : ℝ) * L.card / 2)]
  apply unique_witness_rows_failure hn hd hdn L J hLJ
    (eligible_witness_rows_card I J hI hJ ht)
  simpa only [hJ] using hLoss

theorem uniform_unique_witness_failure_counting {n d s t : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (I : Finset (Fin n))
    (hI : (99 / 100 : ℝ) * n ≤ I.card) (ht : (t : ℝ) ≤ (9 / 100 : ℝ) * n)
    (hLoss : ((d : ℝ) - 1) * ((t : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 10) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬UniformUniqueWitness I s t rows) ≤
      (n.choose t : ℝ) * t.choose s * Real.exp (-uniqueWitnessRate * d * s) := by
  let E : DisjointSetPair n s t → RowSliceMatrix n d → Prop := fun p rows =>
    ((uniqueWitnessRows p.val.1 (p.val.1 ∪ p.val.2)
      (fun i : ↥(I \ (p.val.1 ∪ p.val.2)) => rows i.val)).card : ℝ) < (d : ℝ) * s / 2
  have hEvent : ∀ rows : RowSliceMatrix n d, ¬UniformUniqueWitness I s t rows →
      ∃ p ∈ (Finset.univ : Finset (DisjointSetPair n s t)), E p rows := by
    intro rows hBad
    unfold UniformUniqueWitness at hBad
    push_neg at hBad
    obtain ⟨L, R, hDis, hL, hUnion, hCount⟩ := hBad
    exact ⟨⟨(L, R), hDis, hL, hUnion⟩, Finset.mem_univ _, hCount⟩
  apply (uniformProbability_mono hEvent).trans
  apply (uniformProbability_finset_exists_le Finset.univ E).trans
  calc
    _ ≤ ∑ _p : DisjointSetPair n s t, Real.exp (-uniqueWitnessRate * d * s) := by
      apply Finset.sum_le_sum
      intro p _
      have h := eligible_unique_witness_failure hn hd hdn I p.val.1 (p.val.1 ∪ p.val.2)
        Finset.subset_union_left hI p.property.2.2 ht hLoss
      simpa only [p.property.2.1] using h
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_disjoint_set_pairs,
        Nat.cast_mul]

theorem uniform_unique_witness_failure_entropy {n d s t : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (htPos : 0 < t) (htn : t ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (ht : (t : ℝ) ≤ (9 / 100 : ℝ) * n)
    (hLoss : ((d : ℝ) - 1) * ((t : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 10) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬UniformUniqueWitness I s t rows) ≤
      Real.exp (-uniqueWitnessRate * d * s + (t : ℝ) *
        (Real.log (Real.exp 1 * n / t) + Real.log 2)) := by
  apply (uniform_unique_witness_failure_counting hn hd hdn I hI ht hLoss).trans
  apply (mul_le_mul_of_nonneg_right
    (choose_pair_entropy (by omega : 0 < n) htPos htn (s := s)) (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end CircularLaw
