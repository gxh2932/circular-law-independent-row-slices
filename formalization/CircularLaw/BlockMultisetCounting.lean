import CircularLaw.CoordinateClassRestriction
import Mathlib.Data.Sym.Card

/-!
# Counting coordinate-multiset classes by rank blocks

Each fixed rank block is encoded by its multiset of permitted values.
Summing the blocks recovers the original coordinate multiset. Stars and
bars gives the exact number of block codes, with empty blocks and empty
alphabets included. The class bound only requires that each vector can
be permuted into the prescribed coordinate envelopes.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem coordinateMultiset_card {α β : Type*} [Fintype α] (y : α → β) :
    (coordinateMultiset y).card = Fintype.card α := by
  simp only [coordinateMultiset, Multiset.card_map, Finset.card_val, Finset.card_univ]

theorem coordinateMultiset_map {α β γ : Type*} [Fintype α]
    (f : β → γ) (y : α → β) :
    (coordinateMultiset y).map f = coordinateMultiset (f ∘ y) := by
  simp only [coordinateMultiset, Multiset.map_map]

theorem coordinateMultiset_sum_singletons {α β : Type*} [Fintype α] (y : α → β) :
    coordinateMultiset y = ∑ a, ({y a} : Multiset β) := by
  rw [← Multiset.sum_map_singleton (coordinateMultiset y)]
  simp only [coordinateMultiset, Multiset.map_map]
  rfl

theorem coordinateMultiset_sum_fibers {α ι β : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (y : α → β) :
    (∑ q, coordinateMultiset (fun a : {a : α // part a = q} => y a.val)) =
      coordinateMultiset y := by
  simp only [coordinateMultiset_sum_singletons]
  simpa only [Fintype.sum_sigma] using
    (Equiv.sigmaFiberEquiv part).sum_comp (fun a => ({y a} : Multiset β))

abbrev BlockMultisetCodes {α ι β : Type*} [Fintype α]
    (part : α → ι) (values : ι → Finset β) :=
  ∀ q, Sym {v : β // v ∈ values q} (assignmentPartSize part q)

def blockMultisetCodeOf {α ι β : Type*} [Fintype α]
    (part : α → ι) (values : ι → Finset β) (y : α → β)
    (hy : ∀ a, y a ∈ values (part a)) : BlockMultisetCodes part values := fun q =>
  ⟨coordinateMultiset (fun a : {a : α // part a = q} =>
    (⟨y a.val, by simpa only [a.property] using hy a.val⟩ : {v : β // v ∈ values q})),
    by rw [coordinateMultiset_card]; exact Nat.card_eq_fintype_card.symm⟩

def recoverBlockMultiset {α ι β : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (values : ι → Finset β) (code : BlockMultisetCodes part values) :
    Multiset β := ∑ q, (code q).val.map Subtype.val

theorem recoverBlockMultiset_codeOf {α ι β : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (values : ι → Finset β) (y : α → β)
    (hy : ∀ a, y a ∈ values (part a)) :
    recoverBlockMultiset part values (blockMultisetCodeOf part values y hy) =
      coordinateMultiset y := by
  unfold recoverBlockMultiset blockMultisetCodeOf
  simp only [coordinateMultiset_map]
  exact coordinateMultiset_sum_fibers part y

theorem blockMultisetCodes_card {α ι β : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (values : ι → Finset β) :
    Nat.card (BlockMultisetCodes part values) =
      ∏ q, ((values q).card + assignmentPartSize part q - 1).choose
        (assignmentPartSize part q) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [Sym.card_sym_eq_choose, Fintype.card_coe]

def blockClassCode {α ι β : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (values : ι → Finset β) (A : Set (α → β))
    (hA : ∀ y ∈ A, ∃ σ : Equiv.Perm α, ∀ a, y (σ a) ∈ values (part a))
    (m : {m : Multiset β // m ∈ coordinateMultisetClasses A}) :
    BlockMultisetCodes part values := by
  let y := Classical.choose m.property
  have hy := Classical.choose_spec m.property
  let σ := Classical.choose (hA y hy.1)
  have hσ := Classical.choose_spec (hA y hy.1)
  exact blockMultisetCodeOf part values (y ∘ σ) hσ

theorem recoverBlockMultiset_classCode {α ι β : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (values : ι → Finset β) (A : Set (α → β))
    (hA : ∀ y ∈ A, ∃ σ : Equiv.Perm α, ∀ a, y (σ a) ∈ values (part a))
    (m : {m : Multiset β // m ∈ coordinateMultisetClasses A}) :
    recoverBlockMultiset part values (blockClassCode part values A hA m) = m.val := by
  unfold blockClassCode
  rw [recoverBlockMultiset_codeOf, coordinateMultiset_perm]
  exact (Classical.choose_spec m.property).2

theorem blockClassCode_injective {α ι β : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (values : ι → Finset β) (A : Set (α → β))
    (hA : ∀ y ∈ A, ∃ σ : Equiv.Perm α, ∀ a, y (σ a) ∈ values (part a)) :
    Function.Injective (blockClassCode part values A hA) := by
  intro m m' h
  apply Subtype.ext
  have hr := congrArg (recoverBlockMultiset part values) h
  simpa only [recoverBlockMultiset_classCode] using hr

theorem coordinateMultisetClasses_finite_of_blocks {α ι β : Type*}
    [Fintype α] [Fintype ι] (part : α → ι) (values : ι → Finset β)
    (A : Set (α → β))
    (hA : ∀ y ∈ A, ∃ σ : Equiv.Perm α, ∀ a, y (σ a) ∈ values (part a)) :
    (coordinateMultisetClasses A).Finite := by
  letI : Finite {m : Multiset β // m ∈ coordinateMultisetClasses A} :=
    Finite.of_injective _ (blockClassCode_injective part values A hA)
  exact Set.toFinite _

theorem coordinateMultisetClasses_card_le_blocks {α ι β : Type*}
    [Fintype α] [Fintype ι] (part : α → ι) (values : ι → Finset β)
    (A : Set (α → β))
    (hA : ∀ y ∈ A, ∃ σ : Equiv.Perm α, ∀ a, y (σ a) ∈ values (part a)) :
    Nat.card {m : Multiset β // m ∈ coordinateMultisetClasses A} ≤
      ∏ q, ((values q).card + assignmentPartSize part q - 1).choose
        (assignmentPartSize part q) :=
  (Nat.card_le_card_of_injective _ (blockClassCode_injective part values A hA)).trans_eq
    (blockMultisetCodes_card part values)

end CircularLaw
