import CircularLaw.Conditioning
import CircularLaw.FiniteConditioning
import Mathlib.Logic.Equiv.Embedding

/-!
# Uniform injective sampling restricted to one of two blocks

The exact fibre of restriction to the first block consists of embeddings
of the second block into the complement of the first block's range.
Every first-block embedding has the same positive fibre cardinality.
Thus restriction preserves the uniform embedding law.
-/

noncomputable section
open Classical

namespace CircularLaw

def sigmaFirstFiberEquiv {α : Type*} {β : α → Type*} (a : α) :
    {p : (Σ a, β a) // p.1 = a} ≃ β a where
  toFun p := p.property ▸ p.val.2
  invFun b := ⟨⟨a, b⟩, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨a', b⟩, h⟩
    change a' = a at h
    subst a'
    rfl
  right_inv _ := rfl

def sumLeftEmbeddingFiberEquiv {α β γ : Type*} (u : α ↪ γ) :
    {e : α ⊕ β ↪ γ // Function.Embedding.inl.trans e = u} ≃
      (β ↪ ↥(Set.range u)ᶜ) :=
  (Equiv.subtypeEquiv (Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted (α := α)
    (β := β) (γ := γ)) (fun _ => Iff.rfl)).trans (sigmaFirstFiberEquiv u)

theorem embedding_range_complement_card {a n : ℕ} (u : Fin a ↪ Fin n) :
    Fintype.card ↥(Set.range u)ᶜ = n - a := by
  have hRange : Fintype.card ↥(Set.range u) = a := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (Equiv.ofInjective u u.injective)).symm
  change Fintype.card {x : Fin n // ¬ x ∈ Set.range u} = n - a
  rw [Fintype.card_subtype_compl]
  simpa only [Fintype.card_fin] using congrArg (fun k => Fintype.card (Fin n) - k) hRange

theorem sum_left_embedding_fiber_card {a b n : ℕ} (u : Fin a ↪ Fin n) :
    Nat.card {e : Fin a ⊕ Fin b ↪ Fin n // Function.Embedding.inl.trans e = u} =
      (n - a).descFactorial b := by
  rw [Nat.card_congr (sumLeftEmbeddingFiberEquiv u), Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, embedding_range_complement_card, Fintype.card_fin]

theorem uniform_sum_embedding_restriction {a b n : ℕ} (hSize : a + b ≤ n)
    (E : (Fin a ↪ Fin n) → Prop) :
    uniformProbability (fun e : Fin a ⊕ Fin b ↪ Fin n =>
      E (Function.Embedding.inl.trans e)) = uniformProbability E :=
  uniformProbability_constant_fibers _ ((n - a).descFactorial b)
    (Nat.descFactorial_pos.mpr (by omega)) sum_left_embedding_fiber_card E

theorem uniform_sum_embedding_slice {d n : ℕ} (hSize : 2 * d ≤ n)
    (E : RowSlice n d → Prop) :
    uniformProbability (fun e : Fin d ⊕ Fin d ↪ Fin n =>
      E (sliceOfEmbedding (Function.Embedding.inl.trans e))) = uniformProbability E := by
  exact (uniform_sum_embedding_restriction (a := d) (b := d) (by omega)
    (fun u => E (sliceOfEmbedding u))).trans (uniform_embedding_support E)

def embeddingDomainPermutationEquiv {α β : Type*} (p : Equiv.Perm α) : (α ↪ β) ≃ (α ↪ β) where
  toFun e := p.toEmbedding.trans e
  invFun e := p.symm.toEmbedding.trans e
  left_inv e := by ext x; simp
  right_inv e := by ext x; simp

theorem uniform_embedding_domain_permutation {α β : Type*} [Fintype α] [Fintype β]
    (p : Equiv.Perm α) (E : (α ↪ β) → Prop) :
    uniformProbability (fun e : α ↪ β => E (p.toEmbedding.trans e)) = uniformProbability E :=
  uniformProbability_reindex (embeddingDomainPermutationEquiv p) E

end CircularLaw
