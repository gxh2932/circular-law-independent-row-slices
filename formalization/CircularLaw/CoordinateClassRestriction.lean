import CircularLaw.CoordinateMultiset
import Mathlib.Data.Set.Finite.Lattice

/-!
# Restricting the manuscript's coordinate-multiset classes

The nonempty classes of a family are exactly its image under the coordinate
multiset map. Taking a subfamily therefore cannot increase their number.
The cardinality comparison explicitly retains finiteness of the larger
class family, so an infinite family's natural cardinal is never used.
-/

noncomputable section
open Classical

namespace CircularLaw

def coordinateMultisetClasses {α β : Type*} [Fintype α]
    (A : Set (α → β)) : Set (Multiset β) := coordinateMultiset '' A

theorem coordinateMultisetClasses_mono {α β : Type*} [Fintype α]
    {A B : Set (α → β)} (h : A ⊆ B) :
    coordinateMultisetClasses A ⊆ coordinateMultisetClasses B := Set.image_mono h

theorem coordinateMultisetClasses_finite {α β : Type*} [Fintype α]
    {A : Set (α → β)} (h : A.Finite) : (coordinateMultisetClasses A).Finite :=
  h.image coordinateMultiset

theorem finite_of_coordinateMultisetClasses_finite {α β : Type*} [Fintype α]
    {A : Set (α → β)} (hA : (coordinateMultisetClasses A).Finite) : A.Finite := by
  apply Set.Finite.of_finite_fibers coordinateMultiset hA
  rintro m ⟨y, _, rfl⟩
  have hClass : {z : α → β | z ∈ A ∧ coordinateMultiset z = coordinateMultiset y}.Finite :=
    @Set.toFinite (α → β) {z | z ∈ A ∧ coordinateMultiset z = coordinateMultiset y}
      (coordinateMultisetClassIn_finite A y)
  convert hClass using 1

theorem coordinateMultisetClasses_finite_iff {α β : Type*} [Fintype α]
    (A : Set (α → β)) : (coordinateMultisetClasses A).Finite ↔ A.Finite :=
  ⟨finite_of_coordinateMultisetClasses_finite, coordinateMultisetClasses_finite⟩

theorem coordinateMultisetClasses_card_le {α β : Type*} [Fintype α]
    {A B : Set (α → β)} (h : A ⊆ B) (hB : (coordinateMultisetClasses B).Finite) :
    Nat.card {m : Multiset β // m ∈ coordinateMultisetClasses A} ≤
      Nat.card {m : Multiset β // m ∈ coordinateMultisetClasses B} := by
  letI := hB.fintype
  exact Nat.card_le_card_of_injective
    (fun m : {m : Multiset β // m ∈ coordinateMultisetClasses A} =>
      (⟨m.val, coordinateMultisetClasses_mono h m.property⟩ :
        {m : Multiset β // m ∈ coordinateMultisetClasses B}))
    (fun _ _ hEq => Subtype.ext (congrArg
      (fun m : {m : Multiset β // m ∈ coordinateMultisetClasses B} => m.val) hEq))

end CircularLaw
