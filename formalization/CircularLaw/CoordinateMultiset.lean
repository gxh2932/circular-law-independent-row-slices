import CircularLaw.PartAssignmentCounting
import Mathlib.Data.Multiset.Fintype

/-!
# The manuscript's coordinate-multiset equivalence classes

Equality of coordinate multisets is equivalent to a coordinate permutation.
Every such class is finite even when the coordinate value type is infinite.
-/

noncomputable section
open Classical

namespace CircularLaw

def coordinateMultiset {α β : Type*} [Fintype α] (y : α → β) : Multiset β :=
  (Finset.univ : Finset α).val.map y

theorem coordinateMultiset_count {α β : Type*} [Fintype α] (y : α → β) (v : β) :
    (coordinateMultiset y).count v = assignmentPartSize y v := by
  rw [coordinateMultiset, Multiset.count_map, assignmentPartSize,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (Finset.univ.filter (fun a => v = y a)).card =
    (Finset.univ.filter (fun a => y a = v)).card
  apply congrArg Finset.card
  exact Finset.filter_congr (fun _ _ => eq_comm)

theorem coordinateMultiset_perm {α β : Type*} [Fintype α]
    (y : α → β) (σ : Equiv.Perm α) : coordinateMultiset (y ∘ σ) = coordinateMultiset y := by
  apply Multiset.ext.mpr
  intro v
  rw [coordinateMultiset_count, coordinateMultiset_count]
  exact Nat.card_congr (σ.subtypeEquiv (p := fun a => (y ∘ σ) a = v)
    (q := fun a => y a = v) (fun _ => Iff.rfl))

theorem coordinateMultiset_eq_iff_perm {α β : Type*} [Fintype α] (y z : α → β) :
    coordinateMultiset z = coordinateMultiset y ↔ ∃ σ : Equiv.Perm α, z = y ∘ σ := by
  constructor
  · intro h
    let e (v : β) : {a : α // y a = v} ≃ {a : α // z a = v} :=
      Fintype.equivOfCardEq (by
        have hCount : (coordinateMultiset z).count v = (coordinateMultiset y).count v :=
          congrArg (fun m : Multiset β => m.count v) h
        rw [coordinateMultiset_count, coordinateMultiset_count] at hCount
        simpa only [assignmentPartSize, Nat.card_eq_fintype_card] using hCount.symm)
    let σ := Equiv.ofFiberEquiv e
    refine ⟨σ.symm, funext (fun a => ?_)⟩
    have hMap := Equiv.ofFiberEquiv_map e (σ.symm a)
    simpa only [σ, Equiv.apply_symm_apply, Function.comp_apply] using hMap
  · rintro ⟨σ, rfl⟩
    exact coordinateMultiset_perm y σ

abbrev CoordinatePermutationClass {α β : Type*} [Fintype α] (y : α → β) :=
  {z : α → β // coordinateMultiset z = coordinateMultiset y}

instance coordinatePermutationClass_finite {α β : Type*} [Fintype α] (y : α → β) :
    Finite (CoordinatePermutationClass y) :=
  Finite.of_surjective (fun σ : Equiv.Perm α =>
    (⟨y ∘ σ, coordinateMultiset_perm y σ⟩ : CoordinatePermutationClass y)) (by
      rintro ⟨z, hz⟩
      obtain ⟨σ, hσ⟩ := (coordinateMultiset_eq_iff_perm y z).mp hz
      subst z
      exact ⟨σ, rfl⟩)

abbrev CoordinateMultisetClassIn {α β : Type*} [Fintype α]
    (A : Set (α → β)) (y : α → β) :=
  {z : α → β // z ∈ A ∧ coordinateMultiset z = coordinateMultiset y}

instance coordinateMultisetClassIn_finite {α β : Type*} [Fintype α]
    (A : Set (α → β)) (y : α → β) : Finite (CoordinateMultisetClassIn A y) :=
  Finite.of_injective (fun z : CoordinateMultisetClassIn A y =>
    (⟨z.val, z.property.2⟩ : CoordinatePermutationClass y))
      (fun _ _ h => Subtype.ext
        (congrArg (fun c : CoordinatePermutationClass y => c.val) h))

theorem coordinateMultisetClassIn_card_le {α β : Type*} [Fintype α]
    (A : Set (α → β)) (y : α → β) :
    Nat.card (CoordinateMultisetClassIn A y) ≤ Nat.card (CoordinatePermutationClass y) :=
  Nat.card_le_card_of_injective (fun z : CoordinateMultisetClassIn A y =>
    (⟨z.val, z.property.2⟩ : CoordinatePermutationClass y))
      (fun _ _ h => Subtype.ext
        (congrArg (fun c : CoordinatePermutationClass y => c.val) h))

end CircularLaw
