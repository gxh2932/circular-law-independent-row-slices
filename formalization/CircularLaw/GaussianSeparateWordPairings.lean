import CircularLaw.SumBlockBijections
import CircularLaw.PairedSumColorings
import CircularLaw.GaussianTwoWordPairings

/-!
# Separate matchings for arbitrary Gaussian words

Direct and adjoint subtypes of a sum split into their actual word blocks.
Block-preserving matchings are exactly pairs of one-word matchings.
Their vertex-class exponents add, including loops and repeated edges.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem subtype_sum_walk_block {α β : Type*} {p : α ⊕ β → Prop} (a : {a // p a}) :
    sumWalkBlock (Equiv.subtypeSum a) = sumWalkBlock a.val := by
  rcases a with ⟨a | b, h⟩ <;> rfl

theorem subtype_sum_walk_block_symm {α β : Type*} {p : α ⊕ β → Prop}
    (a : {a // p (Sum.inl a)} ⊕ {b // p (Sum.inr b)}) :
    sumWalkBlock (Equiv.subtypeSum.symm a).val = sumWalkBlock a := by
  cases a <;> rfl

def gaussianWordPairingSumTransport {α β : Type*} (b : α → Bool) (c : β → Bool) :
    GaussianWordPairing (Sum.elim b c) ≃
      (GaussianDirectPositions b ⊕ GaussianDirectPositions c ≃
        GaussianAdjointPositions b ⊕ GaussianAdjointPositions c) :=
  Equiv.equivCongr Equiv.subtypeSum Equiv.subtypeSum

theorem gaussian_word_pairing_sum_block_iff {α β : Type*} (b : α → Bool) (c : β → Bool)
    (e : GaussianWordPairing (Sum.elim b c)) :
    (∀ a, sumWalkBlock (e a).val = sumWalkBlock a.val) ↔
      ∀ a, sumWalkBlock (gaussianWordPairingSumTransport b c e a) = sumWalkBlock a := by
  constructor
  · intro h a
    change sumWalkBlock (Equiv.subtypeSum (e (Equiv.subtypeSum.symm a))) = sumWalkBlock a
    rw [subtype_sum_walk_block]
    simpa only [subtype_sum_walk_block_symm] using h (Equiv.subtypeSum.symm a)
  · intro h a
    have h' := h (Equiv.subtypeSum a)
    change sumWalkBlock (Equiv.subtypeSum (e (Equiv.subtypeSum.symm (Equiv.subtypeSum a)))) =
      sumWalkBlock (Equiv.subtypeSum a) at h'
    simpa only [Equiv.symm_apply_apply, subtype_sum_walk_block] using h'

def gaussianSeparateWordPairingsEquiv {α β : Type*} (b : α → Bool) (c : β → Bool) :
    {e : GaussianWordPairing (Sum.elim b c) // ∀ a, sumWalkBlock (e a).val = sumWalkBlock a.val} ≃
      GaussianWordPairing b × GaussianWordPairing c :=
  (Equiv.subtypeEquiv (gaussianWordPairingSumTransport b c)
    (gaussian_word_pairing_sum_block_iff b c)).trans
      (sumBlockBijectionsEquiv _ _ _ _)

def gaussianSeparateWordPairing {α β : Type*} {b : α → Bool} {c : β → Bool}
    (e : GaussianWordPairing b) (f : GaussianWordPairing c) : GaussianWordPairing (Sum.elim b c) :=
  (gaussianWordPairingSumTransport b c).symm (Equiv.sumCongr e f)

theorem gaussian_separate_word_pairings_equiv_symm {α β : Type*}
    (b : α → Bool) (c : β → Bool) (e : GaussianWordPairing b) (f : GaussianWordPairing c) :
    ((gaussianSeparateWordPairingsEquiv b c).symm (e, f)).val = gaussianSeparateWordPairing e f := rfl

theorem gaussian_separate_word_pairing_left {α β : Type*} {b : α → Bool} {c : β → Bool}
    (e : GaussianWordPairing b) (f : GaussianWordPairing c) (a : GaussianDirectPositions b) :
    gaussianSeparateWordPairing e f ⟨Sum.inl a.val, a.property⟩ =
      ⟨Sum.inl (e a).val, (e a).property⟩ := rfl

theorem gaussian_separate_word_pairing_right {α β : Type*} {b : α → Bool} {c : β → Bool}
    (e : GaussianWordPairing b) (f : GaussianWordPairing c) (a : GaussianDirectPositions c) :
    gaussianSeparateWordPairing e f ⟨Sum.inr a.val, a.property⟩ =
      ⟨Sum.inr (f a).val, (f a).property⟩ := rfl

theorem gaussian_separate_word_vertex_exponent {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (b : α → Bool) (c : β → Bool)
    (ρ : Equiv.Perm α) (τ : Equiv.Perm β) (e : GaussianWordPairing b) (f : GaussianWordPairing c) :
    gaussianWordVertexExponent (Sum.elim b c) (Equiv.sumCongr ρ τ) (gaussianSeparateWordPairing e f) =
      gaussianWordVertexExponent b ρ e + gaussianWordVertexExponent c τ f := by
  let d : GaussianDirectPositions (Sum.elim b c) ≃
      GaussianDirectPositions b ⊕ GaussianDirectPositions c := Equiv.subtypeSum
  rw [gaussianWordVertexExponent,
    ← paired_walk_relation_reindex d.symm (Equiv.sumCongr ρ τ)]
  have hp : (fun a : GaussianDirectPositions (Sum.elim b c) => a.val) ∘ d.symm =
      Sum.map (fun a : GaussianDirectPositions b => a.val) (fun a : GaussianDirectPositions c => a.val) := by
    funext a
    cases a <;> rfl
  have hq : (fun a : GaussianDirectPositions (Sum.elim b c) =>
      (gaussianSeparateWordPairing e f a).val) ∘ d.symm =
      Sum.map (fun a : GaussianDirectPositions b => (e a).val)
        (fun a : GaussianDirectPositions c => (f a).val) := by
    funext a
    cases a <;> rfl
  rw [hp, hq, paired_walk_sum_class_count]
  rfl

theorem gaussian_two_word_separate_pairing_sum (n k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    (∑ e : GaussianWordPairing (Sum.elim b c),
      if ∀ a, sumWalkBlock (e a).val = sumWalkBlock a.val then
        (n : ℂ) ^ gaussianWordVertexExponent (Sum.elim b c)
          (Equiv.sumCongr (finRotate (k + 1)) (finRotate (l + 1))) e else 0) =
      (∑ e : GaussianWordPairing b, (n : ℂ) ^ gaussianWordVertexExponent b (finRotate (k + 1)) e) *
        (∑ f : GaussianWordPairing c, (n : ℂ) ^ gaussianWordVertexExponent c (finRotate (l + 1)) f) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun e : GaussianWordPairing (Sum.elim b c) =>
    ∀ a, sumWalkBlock (e a).val = sumWalkBlock a.val) _
      (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
  rw [← (gaussianSeparateWordPairingsEquiv b c).symm.sum_comp, Fintype.sum_prod_type]
  simp only [gaussian_separate_word_pairings_equiv_symm, gaussian_separate_word_vertex_exponent,
    pow_add]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

end CircularLaw
