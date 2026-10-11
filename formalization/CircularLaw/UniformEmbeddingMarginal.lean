import CircularLaw.UniformEmbeddingRestriction
import Mathlib.Logic.Equiv.Set

/-!
# Uniform marginals at arbitrary selected injective coordinates

Restriction along any domain embedding gives the exact uniform law on
the selected injections. The proof completes the selected coordinates by
their complement and uses the literal constant-fibre count.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem embedding_range_complement_card_general {α β : Type*}
    [Fintype α] [Fintype β] (u : α ↪ β) :
    Fintype.card ↥(Set.range u)ᶜ = Fintype.card β - Fintype.card α := by
  rw [Fintype.card_compl_set, Fintype.card_range]

theorem sum_left_embedding_fiber_card_general {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (u : α ↪ γ) :
    Nat.card {e : α ⊕ β ↪ γ // Function.Embedding.inl.trans e = u} =
      (Fintype.card γ - Fintype.card α).descFactorial (Fintype.card β) := by
  rw [Nat.card_congr (sumLeftEmbeddingFiberEquiv u), Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, embedding_range_complement_card_general]

theorem uniform_sum_embedding_restriction_general {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (hSize : Fintype.card α + Fintype.card β ≤ Fintype.card γ)
    (E : (α ↪ γ) → Prop) :
    uniformProbability (fun e : α ⊕ β ↪ γ => E (Function.Embedding.inl.trans e)) =
      uniformProbability E :=
  uniformProbability_constant_fibers _
    ((Fintype.card γ - Fintype.card α).descFactorial (Fintype.card β))
    (Nat.descFactorial_pos.mpr (by omega)) sum_left_embedding_fiber_card_general E

def embeddingDomainCompletionEquiv {α β : Type*} (u : α ↪ β) :
    α ⊕ ↥(Set.range u)ᶜ ≃ β :=
  (Equiv.sumCongr (Equiv.ofInjective u u.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range u))

theorem embedding_domain_completion_inl {α β : Type*} (u : α ↪ β) (a : α) :
    embeddingDomainCompletionEquiv u (Sum.inl a) = u a := rfl

def embeddingDomainTransportEquiv {α β γ : Type*} (p : α ≃ β) : (β ↪ γ) ≃ (α ↪ γ) where
  toFun e := p.toEmbedding.trans e
  invFun e := p.symm.toEmbedding.trans e
  left_inv e := by ext x; simp
  right_inv e := by ext x; simp

theorem uniform_embedding_restriction {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (u : α ↪ β)
    (hSize : Fintype.card β ≤ Fintype.card γ) (E : (α ↪ γ) → Prop) :
    uniformProbability (fun e : β ↪ γ => E (u.trans e)) = uniformProbability E := by
  let p := embeddingDomainCompletionEquiv u
  have hCard : Fintype.card α + Fintype.card ↥(Set.range u)ᶜ = Fintype.card β := by
    simpa only [Fintype.card_sum] using Fintype.card_congr p
  have hLaw := uniform_sum_embedding_restriction_general (hCard ▸ hSize) E
  have hReindex := uniformProbability_reindex (embeddingDomainTransportEquiv p)
    (fun e => E (Function.Embedding.inl.trans e))
  exact hReindex.trans hLaw

theorem finiteMean_embedding_restriction {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (u : α ↪ β)
    (hSize : Fintype.card β ≤ Fintype.card γ) (g : (α ↪ γ) → ℝ) :
    finiteMean (fun e : β ↪ γ => g (u.trans e)) = finiteMean g := by
  calc
    _ = ∑ v, uniformProbability (fun e : β ↪ γ => u.trans e = v) * g v :=
      finiteMean_part_mass (fun e => u.trans e) g
    _ = ∑ v, uniformProbability (fun e : α ↪ γ => e = v) * g v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [uniform_embedding_restriction u hSize (fun e => e = v)]
    _ = _ := (finiteMean_part_mass (fun e : α ↪ γ => e) g).symm

end CircularLaw
