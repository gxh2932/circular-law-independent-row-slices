import CircularLaw.Conditioning
import Mathlib.Data.Fintype.Perm

/-!
# Exact counting of assignments to parts of fixed sizes

A coordinate permutation produces every assignment with the prescribed
fiber sizes. Its fiber is the product of the permutation groups inside
the parts. Counting these fibers proves the multinomial factor directly.
-/

noncomputable section
open Classical
open scoped BigOperators Nat

namespace CircularLaw

def assignmentPartSize {α ι : Type*} [Fintype α] (part : α → ι) (q : ι) : ℕ :=
  Nat.card {a : α // part a = q}

abbrev FixedPartAssignments {α ι : Type*} [Fintype α] (part : α → ι) :=
  {labels : α → ι // ∀ q, Nat.card {a : α // labels a = q} = assignmentPartSize part q}

def assignmentOfPerm {α ι : Type*} [Fintype α] (part : α → ι) (σ : Equiv.Perm α) :
    FixedPartAssignments part :=
  ⟨part ∘ σ.symm, fun q => Nat.card_congr
    (σ.symm.subtypeEquiv (p := fun a => (part ∘ σ.symm) a = q)
      (q := fun a => part a = q) (fun _ => Iff.rfl))⟩

theorem assignmentOfPerm_eq_iff {α ι : Type*} [Fintype α]
    (part : α → ι) (labels : FixedPartAssignments part) (σ : Equiv.Perm α) :
    assignmentOfPerm part σ = labels ↔ ∀ a, labels.val (σ a) = part a := by
  constructor
  · intro h a
    have hVal := congrFun (congrArg Subtype.val h) (σ a)
    simpa only [assignmentOfPerm, Function.comp_apply, Equiv.symm_apply_apply] using hVal.symm
  · intro h
    apply Subtype.ext
    funext a
    simpa only [assignmentOfPerm, Function.comp_apply, Equiv.apply_symm_apply] using
      (h (σ.symm a)).symm

def partPreservingPermFiberEquiv {α ι : Type*} (part labels : α → ι) :
    {σ : Equiv.Perm α // ∀ a, labels (σ a) = part a} ≃
      (∀ q, {a : α // part a = q} ≃ {a : α // labels a = q}) where
  toFun σ q := σ.val.subtypeEquiv (fun a => by rw [σ.property a])
  invFun e := ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    rfl
  right_inv e := by
    funext q
    apply Equiv.ext
    rintro ⟨a, ha⟩
    apply Subtype.ext
    subst q
    rfl

def fixedAssignmentFiberEquiv {α ι : Type*} [Fintype α]
    (part : α → ι) (labels : FixedPartAssignments part) (q : ι) :
    {a : α // part a = q} ≃ {a : α // labels.val a = q} :=
  Fintype.equivOfCardEq (by simpa only [assignmentPartSize, Nat.card_eq_fintype_card] using
    (labels.property q).symm)

theorem assignmentOfPerm_fiber_card {α ι : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (labels : FixedPartAssignments part) :
    Nat.card {σ : Equiv.Perm α // assignmentOfPerm part σ = labels} =
      ∏ q, (assignmentPartSize part q)! := by
  let e := (Equiv.subtypeEquivRight (fun σ => assignmentOfPerm_eq_iff part labels σ)).trans
    (partPreservingPermFiberEquiv part labels.val)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro q _
  simpa only [assignmentPartSize, Nat.card_eq_fintype_card] using
    Fintype.card_equiv (fixedAssignmentFiberEquiv part labels q)

theorem fixedPartAssignments_card_mul_factorials {α ι : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) :
    Nat.card (FixedPartAssignments part) * (∏ q, (assignmentPartSize part q)!) =
      (Fintype.card α)! := by
  have h := card_event_of_constant_fibers (assignmentOfPerm part)
    (∏ q, (assignmentPartSize part q)!) (assignmentOfPerm_fiber_card part) (fun _ => True)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype_true, Fintype.card_perm,
    mul_comm] using h.symm

theorem fixedPartAssignments_card {α ι : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) :
    (Nat.card (FixedPartAssignments part) : ℝ) =
      ((Fintype.card α)! : ℝ) / (∏ q, ((assignmentPartSize part q)! : ℝ)) := by
  have hPos : (0 : ℝ) < ∏ q, ((assignmentPartSize part q)! : ℝ) :=
    Finset.prod_pos (fun q _ => by exact_mod_cast Nat.factorial_pos (assignmentPartSize part q))
  apply (eq_div_iff hPos.ne').mpr
  exact_mod_cast fixedPartAssignments_card_mul_factorials part

end CircularLaw
