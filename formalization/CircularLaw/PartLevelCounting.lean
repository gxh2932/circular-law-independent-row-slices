import CircularLaw.PartAssignmentCounting

/-!
# Counting level choices inside prescribed parts

After an assignment to parts of fixed sizes, each coordinate chooses one
of its part's permitted values. Fiberwise regrouping gives the exact
product of the heights raised to the part sizes.
-/

noncomputable section
open Classical
open scoped BigOperators Nat

namespace CircularLaw

abbrev PartLevelChoices {α ι β : Type*} (values : ι → Finset β) (labels : α → ι) :=
  ∀ a : α, {v : β // v ∈ values (labels a)}

abbrev PartLevelAssignments {α ι β : Type*} [Fintype α]
    (part : α → ι) (values : ι → Finset β) :=
  Σ labels : FixedPartAssignments part, PartLevelChoices values labels.val

theorem fixedAssignment_height_product {α ι : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (labels : FixedPartAssignments part) (height : ι → ℕ) :
    (∏ a, height (labels.val a)) = ∏ q, height q ^ assignmentPartSize part q := by
  rw [← (Equiv.sigmaFiberEquiv labels.val).prod_comp (fun a => height (labels.val a)),
    Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro q _
  have hFiber : Fintype.card {a : α // labels.val a = q} = assignmentPartSize part q := by
    simpa only [Nat.card_eq_fintype_card] using labels.property q
  change (∏ a : {a : α // labels.val a = q}, height (labels.val a.val)) = _
  calc
    _ = ∏ _a : {a : α // labels.val a = q}, height q :=
      Finset.prod_congr rfl (fun a _ => congrArg height a.property)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, hFiber]

theorem partLevelChoices_card {α ι β : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (values : ι → Finset β) (labels : FixedPartAssignments part) :
    Nat.card (PartLevelChoices values labels.val) =
      ∏ q, (values q).card ^ assignmentPartSize part q := by
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [Fintype.card_coe]
  exact fixedAssignment_height_product part labels (fun q => (values q).card)

theorem partLevelAssignments_card {α ι β : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (values : ι → Finset β) :
    Nat.card (PartLevelAssignments part values) =
      Nat.card (FixedPartAssignments part) *
        (∏ q, (values q).card ^ assignmentPartSize part q) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hFiber (labels : FixedPartAssignments part) :
      Fintype.card (PartLevelChoices values labels.val) =
        ∏ q, (values q).card ^ assignmentPartSize part q := by
    simpa only [Nat.card_eq_fintype_card] using partLevelChoices_card part values labels
  simp only [hFiber, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.cast_id]

theorem partLevelAssignments_card_real {α ι β : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (values : ι → Finset β) :
    (Nat.card (PartLevelAssignments part values) : ℝ) =
      (((Fintype.card α)! : ℝ) / (∏ q, ((assignmentPartSize part q)! : ℝ))) *
        (∏ q, ((values q).card : ℝ) ^ assignmentPartSize part q) := by
  rw [partLevelAssignments_card, Nat.cast_mul, fixedPartAssignments_card,
    Nat.cast_prod]
  simp only [Nat.cast_pow]

end CircularLaw
