import CircularLaw.UniformEmbeddingRestriction
import CircularLaw.WeightedBernoulliSymmetrization
import CircularLaw.SingletonBlockConcentration

/-!
# Exact sampling of a uniform slice from paired coordinates

An injective sample of two blocks supplies disjoint coordinate pairs.
Selecting one coordinate from each pair by independent fair Boolean
choices gives the actual uniform fixed-degree slice law. The law is
proved by domain permutation and constant-fibre counting.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def pairedChoicePermutation {d : ℕ} (x : Fin d → Bool) : Equiv.Perm (Fin d ⊕ Fin d) where
  toFun
    | Sum.inl j => if x j then Sum.inr j else Sum.inl j
    | Sum.inr j => if x j then Sum.inl j else Sum.inr j
  invFun
    | Sum.inl j => if x j then Sum.inr j else Sum.inl j
    | Sum.inr j => if x j then Sum.inl j else Sum.inr j
  left_inv z := by
    cases z with
    | inl j => cases h : x j <;> simp [h]
    | inr j => cases h : x j <;> simp [h]
  right_inv z := by
    cases z with
    | inl j => cases h : x j <;> simp [h]
    | inr j => cases h : x j <;> simp [h]

def pairedChoiceEmbedding {d : ℕ} (x : Fin d → Bool) : Fin d ↪ Fin d ⊕ Fin d :=
  Function.Embedding.inl.trans (pairedChoicePermutation x).toEmbedding

theorem paired_choice_embedding_apply {d : ℕ} (x : Fin d → Bool) (j : Fin d) :
    pairedChoiceEmbedding x j = if x j then Sum.inr j else Sum.inl j := rfl

def pairedSlice {n d : ℕ} (e : Fin d ⊕ Fin d ↪ Fin n) (x : Fin d → Bool) : RowSlice n d :=
  sliceOfEmbedding ((pairedChoiceEmbedding x).trans e)

theorem uniform_paired_slice_fixed_choices {n d : ℕ} (hSize : 2 * d ≤ n)
    (x : Fin d → Bool) (E : RowSlice n d → Prop) :
    uniformProbability (fun e : Fin d ⊕ Fin d ↪ Fin n => E (pairedSlice e x)) =
      uniformProbability E := by
  have h := uniform_embedding_domain_permutation (pairedChoicePermutation x)
    (fun e : Fin d ⊕ Fin d ↪ Fin n => E (sliceOfEmbedding (Function.Embedding.inl.trans e)))
  exact h.trans (uniform_sum_embedding_slice hSize E)

theorem uniform_paired_slice {n d : ℕ} (hSize : 2 * d ≤ n) (E : RowSlice n d → Prop) :
    uniformProbability (fun p : (Fin d ⊕ Fin d ↪ Fin n) × (Fin d → Bool) =>
      E (pairedSlice p.1 p.2)) = uniformProbability E := by
  rw [uniformProbability_prod_fubini]
  simp only [uniform_paired_slice_fixed_choices hSize, finiteMean_const]

theorem uniform_paired_slice_conditioning {n d : ℕ} (hSize : 2 * d ≤ n)
    (E : RowSlice n d → Prop) :
    uniformProbability E = finiteMean (fun e : Fin d ⊕ Fin d ↪ Fin n =>
      uniformProbability (fun x : Fin d → Bool => E (pairedSlice e x))) := by
  rw [← uniform_paired_slice hSize E]
  rw [← uniformProbability_reindex
    (Equiv.prodComm (Fin d → Bool) (Fin d ⊕ Fin d ↪ Fin n))
    (fun p => E (pairedSlice p.1 p.2)), uniformProbability_prod_fubini]
  rfl

theorem paired_slice_linear_form {n d : ℕ} (e : Fin d ⊕ Fin d ↪ Fin n)
    (x : Fin d → Bool) (y : Fin n → ℂ) :
    rowLinearForm (pairedSlice e x) y =
      (∑ j, y (e (Sum.inl j))) +
        ∑ j, weightedBernoulliValue (y (e (Sum.inr j)) - y (e (Sum.inl j))) (x j) := by
  rw [rowLinearForm_eq_support_sum]
  simp only [pairedSlice, sliceOfEmbedding, Finset.sum_map]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.Embedding.trans_apply]
  rw [paired_choice_embedding_apply]
  cases x j <;> simp [weightedBernoulliValue]

end CircularLaw
