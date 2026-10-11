import CircularLaw.CoordinateClassRestriction

/-!
# Exact summation over represented coordinate-multiset classes

Every represented class has a reference vector in the family. A fiber
equivalence regroups the original family sum by these actual classes.
In particular, the class cardinalities sum to the family cardinality.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

abbrev CoordinateMultisetClassesOf {α β : Type*} [Fintype α] (A : Set (α → β)) :=
  {m : Multiset β // m ∈ coordinateMultisetClasses A}

def coordinateClassRepresentative {α β : Type*} [Fintype α] (A : Set (α → β))
    (m : CoordinateMultisetClassesOf A) : A :=
  ⟨Classical.choose m.property, (Classical.choose_spec m.property).1⟩

theorem coordinateClassRepresentative_multiset {α β : Type*} [Fintype α] (A : Set (α → β))
    (m : CoordinateMultisetClassesOf A) :
    coordinateMultiset (coordinateClassRepresentative A m).val = m.val :=
  (Classical.choose_spec m.property).2

def coordinateClassIndex {α β : Type*} [Fintype α] (A : Set (α → β)) (y : A) :
    CoordinateMultisetClassesOf A :=
  ⟨coordinateMultiset y.val, ⟨y.val, y.property, rfl⟩⟩

def coordinateClassFiberEquiv {α β : Type*} [Fintype α] (A : Set (α → β))
    (m : CoordinateMultisetClassesOf A) :
    {y : A // coordinateClassIndex A y = m} ≃
      CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val where
  toFun y := ⟨y.val.val, y.val.property, by
    have h := congrArg (fun q : CoordinateMultisetClassesOf A => q.val) y.property
    exact h.trans (coordinateClassRepresentative_multiset A m).symm⟩
  invFun z := ⟨⟨z.val, z.property.1⟩, Subtype.ext
    (z.property.2.trans (coordinateClassRepresentative_multiset A m))⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

def coordinateClassesEquiv {α β : Type*} [Fintype α] (A : Set (α → β)) :
    A ≃ Σ m : CoordinateMultisetClassesOf A,
      CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val :=
  (Equiv.sigmaFiberEquiv (coordinateClassIndex A)).symm.trans
    (Equiv.sigmaCongrRight (coordinateClassFiberEquiv A))

theorem coordinateClassesEquiv_value {α β : Type*} [Fintype α] (A : Set (α → β)) (y : A) :
    (coordinateClassesEquiv A y).2.val = y.val := rfl

theorem coordinate_family_sum_by_classes {α β : Type*} [Fintype α]
    (A : Set (α → β)) [Fintype A] [Fintype (CoordinateMultisetClassesOf A)] (f : (α → β) → ℝ) :
    letI : ∀ m : CoordinateMultisetClassesOf A,
      Fintype (CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val) :=
        fun _ => Fintype.ofFinite _
    (∑ y : A, f y.val) = ∑ m : CoordinateMultisetClassesOf A,
      ∑ z : CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val, f z.val := by
  letI : ∀ m : CoordinateMultisetClassesOf A,
    Fintype (CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val) :=
      fun _ => Fintype.ofFinite _
  have h := (coordinateClassesEquiv A).sum_comp (fun p => f p.2.val)
  simpa only [coordinateClassesEquiv_value, Fintype.sum_sigma] using h

theorem coordinate_class_card_sum {α β : Type*} [Fintype α]
    (A : Set (α → β)) [Fintype A] [Fintype (CoordinateMultisetClassesOf A)] :
    (∑ m : CoordinateMultisetClassesOf A,
      (Nat.card (CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val) : ℝ)) =
        Nat.card A := by
  letI : ∀ m : CoordinateMultisetClassesOf A,
    Fintype (CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val) :=
      fun _ => Fintype.ofFinite _
  have h := coordinate_family_sum_by_classes A (fun _ => (1 : ℝ))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card] using h.symm

theorem coordinate_family_sum_class_constant {α β : Type*} [Fintype α]
    (A : Set (α → β)) [Fintype A] [Fintype (CoordinateMultisetClassesOf A)] (f : (α → β) → ℝ)
    (hConst : ∀ y z : α → β, coordinateMultiset z = coordinateMultiset y → f z = f y) :
    (∑ y : A, f y.val) = ∑ m : CoordinateMultisetClassesOf A,
      (Nat.card (CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val) : ℝ) *
        f (coordinateClassRepresentative A m).val := by
  letI : ∀ m : CoordinateMultisetClassesOf A,
    Fintype (CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val) :=
      fun _ => Fintype.ofFinite _
  rw [coordinate_family_sum_by_classes]
  apply Finset.sum_congr rfl
  intro m _
  calc
    (∑ z : CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val, f z.val) =
        ∑ _z : CoordinateMultisetClassIn A (coordinateClassRepresentative A m).val,
          f (coordinateClassRepresentative A m).val :=
      Finset.sum_congr rfl (fun z _ => hConst _ _ z.property.2)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

end CircularLaw
