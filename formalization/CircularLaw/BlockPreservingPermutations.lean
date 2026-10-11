import CircularLaw.PermutationCycleColorings
import Mathlib.Logic.Equiv.Prod

/-!
# Block-preserving permutations and independent block cycles

A permutation preserving the first coordinate is exactly a family of
permutations of the second coordinate. Its invariant colorings separate
over the blocks; counting binary colorings proves additivity of cycle
counts for two blocks, including fixed-point cycles.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def blockPermutation {α β : Type*} (τ : α → Equiv.Perm β) : Equiv.Perm (α × β) where
  toFun a := (a.1, τ a.1 a.2)
  invFun a := (a.1, (τ a.1).symm a.2)
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp

theorem block_permutation_apply {α β : Type*} (τ : α → Equiv.Perm β) (a : α × β) :
    blockPermutation τ a = (a.1, τ a.1 a.2) := rfl

theorem block_preserving_symm {α β : Type*} (σ : Equiv.Perm (α × β))
    (h : ∀ a, (σ a).1 = a.1) (a : α × β) :
    (σ.symm a).1 = a.1 := by
  simpa only [Equiv.apply_symm_apply] using (h (σ.symm a)).symm

def blockPermutationRestriction {α β : Type*} (σ : Equiv.Perm (α × β))
    (h : ∀ a, (σ a).1 = a.1) (b : α) : Equiv.Perm β where
  toFun i := (σ (b, i)).2
  invFun i := (σ.symm (b, i)).2
  left_inv i := by
    have hEq : (b, (σ (b, i)).2) = σ (b, i) := by
      apply Prod.ext
      · exact (h (b, i)).symm
      · rfl
    change (σ.symm (b, (σ (b, i)).2)).2 = i
    rw [hEq, Equiv.symm_apply_apply]
  right_inv i := by
    have hEq : (b, (σ.symm (b, i)).2) = σ.symm (b, i) := by
      apply Prod.ext
      · exact (block_preserving_symm σ h (b, i)).symm
      · rfl
    change (σ (b, (σ.symm (b, i)).2)).2 = i
    rw [hEq, Equiv.apply_symm_apply]

def blockPreservingPermutationsEquiv (α β : Type*) :
    {σ : Equiv.Perm (α × β) // ∀ a, (σ a).1 = a.1} ≃ (α → Equiv.Perm β) where
  toFun σ := blockPermutationRestriction σ.val σ.property
  invFun τ := ⟨blockPermutation τ, fun _ => rfl⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    apply Prod.ext
    · exact (σ.property a).symm
    · rfl
  right_inv τ := by
    funext b
    ext i
    rfl

theorem block_permutation_inv {α β : Type*} (τ : α → Equiv.Perm β) :
    (blockPermutation τ)⁻¹ = blockPermutation (fun b => (τ b)⁻¹) := by
  apply Equiv.ext
  intro a
  change (a.1, (τ a.1).symm a.2) = (a.1, (τ a.1)⁻¹ a.2)
  rfl

theorem block_permutation_mul {α β : Type*} (τ υ : α → Equiv.Perm β) :
    blockPermutation τ * blockPermutation υ = blockPermutation (fun b => τ b * υ b) := by
  apply Equiv.ext
  intro a
  simp only [Equiv.Perm.mul_apply, block_permutation_apply]

def blockInvariantColoringsEquiv {α β γ : Type*} (τ : α → Equiv.Perm β) :
    {f : α × β → γ // ∀ a, f (blockPermutation τ a) = f a} ≃
      (∀ b, {g : β → γ // ∀ i, g (τ b i) = g i}) :=
  (Equiv.subtypeEquiv (Equiv.curry α β γ) (fun f => by
    constructor
    · intro h b i
      exact h (b, i)
    · intro h a
      exact h a.1 a.2)).trans Equiv.subtypePiEquivPi

theorem block_permutation_two_cycle_count {β : Type*} [Fintype β] [DecidableEq β]
    (τ : Bool → Equiv.Perm β) :
    permutationCycleCount (blockPermutation τ) =
      permutationCycleCount (τ true) + permutationCycleCount (τ false) := by
  have hCard := Fintype.card_congr (blockInvariantColoringsEquiv (γ := Fin 2) τ)
  rw [permutation_invariant_fin_coloring_card, Fintype.card_pi] at hCard
  simp only [permutation_invariant_fin_coloring_card, Fintype.prod_bool, ← pow_add] at hCard
  exact (Nat.pow_right_injective (by omega : 1 < 2)) hCard

end CircularLaw
