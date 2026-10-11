import CircularLaw.PairedTwoClosedWalks
import Mathlib.Data.Sum.Basic

/-!
# Bijections preserving two possibly different finite blocks

Preservation of the sum tag restricts an actual bijection to one
bijection on each block. The converse is their sum. The source and
target blocks need not be the same types or have a common size.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem sum_block_bijection_symm {α β γ δ : Type*} (e : α ⊕ β ≃ γ ⊕ δ)
    (h : ∀ a, sumWalkBlock (e a) = sumWalkBlock a) (a : γ ⊕ δ) :
    sumWalkBlock (e.symm a) = sumWalkBlock a := by
  simpa only [Equiv.apply_symm_apply] using (h (e.symm a)).symm

def sumBlockLeftMap {α β γ δ : Type*} (e : α ⊕ β ≃ γ ⊕ δ)
    (h : ∀ a, sumWalkBlock (e a) = sumWalkBlock a) (a : α) : γ :=
  (e (Sum.inl a)).getLeft (by
    have ha := h (Sum.inl a)
    cases he : e (Sum.inl a) with
    | inl c => simp
    | inr d => simp only [he, sumWalkBlock, Bool.true_eq_false] at ha)

def sumBlockRightMap {α β γ δ : Type*} (e : α ⊕ β ≃ γ ⊕ δ)
    (h : ∀ a, sumWalkBlock (e a) = sumWalkBlock a) (a : β) : δ :=
  (e (Sum.inr a)).getRight (by
    have ha := h (Sum.inr a)
    cases he : e (Sum.inr a) with
    | inl c => simp only [he, sumWalkBlock, Bool.false_eq_true] at ha
    | inr d => simp)

theorem sum_block_left_map_eq {α β γ δ : Type*} (e : α ⊕ β ≃ γ ⊕ δ)
    (h : ∀ a, sumWalkBlock (e a) = sumWalkBlock a) (a : α) :
    Sum.inl (sumBlockLeftMap e h a) = e (Sum.inl a) := by
  cases he : e (Sum.inl a) with
  | inl c => simp [sumBlockLeftMap, he]
  | inr d => exact False.elim (by simpa only [he, sumWalkBlock, Bool.true_eq_false] using h (Sum.inl a))

theorem sum_block_right_map_eq {α β γ δ : Type*} (e : α ⊕ β ≃ γ ⊕ δ)
    (h : ∀ a, sumWalkBlock (e a) = sumWalkBlock a) (a : β) :
    Sum.inr (sumBlockRightMap e h a) = e (Sum.inr a) := by
  cases he : e (Sum.inr a) with
  | inl c => exact False.elim (by simpa only [he, sumWalkBlock, Bool.false_eq_true] using h (Sum.inr a))
  | inr d => simp [sumBlockRightMap, he]

def sumBlockLeftBijection {α β γ δ : Type*} (e : α ⊕ β ≃ γ ⊕ δ)
    (h : ∀ a, sumWalkBlock (e a) = sumWalkBlock a) : α ≃ γ where
  toFun := sumBlockLeftMap e h
  invFun := sumBlockLeftMap e.symm (sum_block_bijection_symm e h)
  left_inv a := by
    apply Sum.inl_injective
    rw [sum_block_left_map_eq, sum_block_left_map_eq, Equiv.symm_apply_apply]
  right_inv a := by
    apply Sum.inl_injective
    rw [sum_block_left_map_eq, sum_block_left_map_eq, Equiv.apply_symm_apply]

def sumBlockRightBijection {α β γ δ : Type*} (e : α ⊕ β ≃ γ ⊕ δ)
    (h : ∀ a, sumWalkBlock (e a) = sumWalkBlock a) : β ≃ δ where
  toFun := sumBlockRightMap e h
  invFun := sumBlockRightMap e.symm (sum_block_bijection_symm e h)
  left_inv a := by
    apply Sum.inr_injective
    rw [sum_block_right_map_eq, sum_block_right_map_eq, Equiv.symm_apply_apply]
  right_inv a := by
    apply Sum.inr_injective
    rw [sum_block_right_map_eq, sum_block_right_map_eq, Equiv.apply_symm_apply]

def sumBlockBijectionsEquiv (α β γ δ : Type*) :
    {e : α ⊕ β ≃ γ ⊕ δ // ∀ a, sumWalkBlock (e a) = sumWalkBlock a} ≃
      (α ≃ γ) × (β ≃ δ) where
  toFun e := (sumBlockLeftBijection e.val e.property, sumBlockRightBijection e.val e.property)
  invFun e := ⟨Equiv.sumCongr e.1 e.2, by rintro (a | b) <;> rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    cases a with
    | inl a => exact sum_block_left_map_eq e.val e.property a
    | inr b => exact sum_block_right_map_eq e.val e.property b
  right_inv e := by
    apply Prod.ext
    · apply Equiv.ext
      intro a
      rfl
    · apply Equiv.ext
      intro a
      rfl

end CircularLaw
