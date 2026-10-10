import CircularLaw.CoordinateMultiset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Counting a family with a small set of exceptional coordinates

A code records the exceptional coordinate set and one value from the
appropriate finite alphabet at each position. Its exact cardinality is
the binomial position count times the two alphabet powers.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

abbrev TwoAlphabetCodes {α β : Type*} [Fintype α] (A B : Finset β) (r : ℕ) :=
  Σ T : {T : Finset α // T.card = r},
    ∀ i : α, {v : β // v ∈ if i ∈ T.val then A else B}

def twoAlphabetDecode {α β : Type*} [Fintype α] {A B : Finset β} {r : ℕ}
    (c : TwoAlphabetCodes (α := α) A B r) : α → β := fun i => (c.2 i).val

theorem twoAlphabetCode_exists {α β : Type*} [Fintype α] (A B : Finset β) (r : ℕ)
    (y : α → β) (h : ∃ T : Finset α, T.card = r ∧
      (∀ i ∈ T, y i ∈ A) ∧ ∀ i ∉ T, y i ∈ B) :
    ∃ c : TwoAlphabetCodes (α := α) A B r, twoAlphabetDecode c = y := by
  obtain ⟨T, hT, hA, hB⟩ := h
  refine ⟨⟨⟨T, hT⟩, fun i => ⟨y i, ?_⟩⟩, rfl⟩
  by_cases hi : i ∈ T
  · simpa only [if_pos hi] using hA i hi
  · simpa only [if_neg hi] using hB i hi

theorem twoAlphabetValues_card {α β : Type*} [Fintype α] (A B : Finset β)
    (T : Finset α) :
    Fintype.card (∀ i : α, {v : β // v ∈ if i ∈ T then A else B}) =
      A.card ^ T.card * B.card ^ (Fintype.card α - T.card) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_coe]
  simp_rw [apply_ite Finset.card]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, Finset.prod_const, Finset.card_sdiff,
    Finset.inter_univ, Finset.card_univ]

theorem twoAlphabetCodes_card {α β : Type*} [Fintype α] (A B : Finset β) (r : ℕ) :
    Nat.card (TwoAlphabetCodes (α := α) A B r) =
      (Fintype.card α).choose r * A.card ^ r * B.card ^ (Fintype.card α - r) := by
  have hValues (T : {T : Finset α // T.card = r}) :
      Fintype.card (∀ i : α, {v : β // v ∈ if i ∈ T.val then A else B}) =
        A.card ^ r * B.card ^ (Fintype.card α - r) := by
    rw [twoAlphabetValues_card, T.property]
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [hValues]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, nsmul_eq_mul]
  norm_cast
  ac_rfl

theorem twoAlphabet_family_count {α β : Type*} [Fintype α] (A B : Finset β) (r : ℕ)
    (F : Set (α → β)) (h : ∀ y ∈ F, ∃ T : Finset α, T.card = r ∧
      (∀ i ∈ T, y i ∈ A) ∧ ∀ i ∉ T, y i ∈ B) :
    F.Finite ∧ Nat.card F ≤
      (Fintype.card α).choose r * A.card ^ r * B.card ^ (Fintype.card α - r) := by
  have hCodes (y : F) := twoAlphabetCode_exists A B r y.val (h y.val y.property)
  let f : F → TwoAlphabetCodes (α := α) A B r := fun y => Classical.choose (hCodes y)
  have hf : Function.Injective f := by
    intro y z hEq
    apply Subtype.ext
    exact (Classical.choose_spec (hCodes y)).symm.trans
      ((congrArg twoAlphabetDecode hEq).trans (Classical.choose_spec (hCodes z)))
  letI : Finite F := Finite.of_injective f hf
  exact ⟨Set.toFinite F, (Nat.card_le_card_of_injective f hf).trans_eq (twoAlphabetCodes_card A B r)⟩

end CircularLaw
