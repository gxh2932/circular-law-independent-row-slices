import CircularLaw.PermutationCycleColorings
import Mathlib.Logic.Relation

/-!
# Exact counts for finite assignments constrained by a relation

Equality constraints on vertex labels generate an equivalence relation.
Assignments satisfying the constraints are exactly functions on its
quotient, including when constraints repeat or identify a vertex with itself.
This supplies the dimension exponent for nonalternating Gaussian words.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem relation_coloring_eqv_gen {α β : Type*} (r : α → α → Prop)
    (f : α → β) (hf : ∀ a b, r a b → f a = f b) {a b : α}
    (hab : Relation.EqvGen r a b) : f a = f b := by
  induction hab with
  | rel a b h => exact hf a b h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def relationColoringsEquiv {α β : Type*} (r : α → α → Prop) :
    {f : α → β // ∀ a b, r a b → f a = f b} ≃
      (Quotient (Relation.EqvGen.setoid r) → β) where
  toFun f := Quotient.lift f.val (fun _ _ h => relation_coloring_eqv_gen r f.val f.property h)
  invFun g := ⟨fun a => g (Quotient.mk _ a), fun a b h =>
    congrArg g (Quotient.sound (Relation.EqvGen.rel a b h))⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    rfl
  right_inv g := by
    funext q
    induction q using Quotient.inductionOn with
    | h a => rfl

def relationClassCount {α : Type*} [Fintype α] (r : α → α → Prop) : ℕ :=
  Fintype.card (Quotient (Relation.EqvGen.setoid r))

theorem relation_coloring_card {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (r : α → α → Prop) :
    Fintype.card {f : α → β // ∀ a b, r a b → f a = f b} =
      Fintype.card β ^ relationClassCount r := by
  rw [Fintype.card_congr (relationColoringsEquiv (β := β) r), Fintype.card_fun]
  rfl

theorem relation_fin_coloring_card {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) (n : ℕ) :
    Fintype.card {f : α → Fin n // ∀ a b, r a b → f a = f b} =
      n ^ relationClassCount r := by
  have h := relation_coloring_card (β := Fin n) r
  simp only [Fintype.card_subtype] at h ⊢
  simpa only [Fintype.card_fin] using h

end CircularLaw
