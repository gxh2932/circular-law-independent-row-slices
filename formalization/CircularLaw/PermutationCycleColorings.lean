import CircularLaw.GaussianPairingCount
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Permutation-invariant assignments are colorings of the cycles

The quotient by the actual same-cycle relation includes fixed-point
cycles. An invariant assignment descends to this quotient, and every
quotient coloring gives an invariant assignment. Hence a permutation
with `c` cycles has exactly `n^c` assignments to `Fin n`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def permutationCycleCount {α : Type*} [Fintype α] (σ : Equiv.Perm α) : ℕ :=
  Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid σ))

theorem permutation_invariant_same_cycle {α β : Type*} (σ : Equiv.Perm α)
    (f : α → β) (hf : ∀ a, f (σ a) = f a) {a b : α} (hab : σ.SameCycle a b) :
    f a = f b := by
  have hInv (x : α) : f (σ⁻¹ x) = f x := by
    simpa using (hf (σ.symm x)).symm
  have hPow (m : ℤ) (x : α) : f ((σ ^ m) x) = f x := by
    induction m using Int.induction_on generalizing x with
    | zero => simp
    | succ m ih => rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hf]
    | pred m ih => rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, hInv]
  obtain ⟨m, rfl⟩ := hab
  exact (hPow m a).symm

def permutationInvariantColoringsEquiv {α β : Type*} (σ : Equiv.Perm α) :
    {f : α → β // ∀ a, f (σ a) = f a} ≃
      (Quotient (Equiv.Perm.SameCycle.setoid σ) → β) where
  toFun f := Quotient.lift f.val (fun _ _ h =>
    permutation_invariant_same_cycle σ f.val f.property h)
  invFun g := ⟨fun a => g (Quotient.mk _ a), fun a => by
    apply congrArg g
    apply Quotient.sound
    exact (Equiv.Perm.SameCycle.symm ⟨1, by simp⟩)⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    rfl
  right_inv g := by
    funext q
    induction q using Quotient.inductionOn with
    | h a => rfl

theorem permutation_invariant_coloring_card {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (σ : Equiv.Perm α) :
    Fintype.card {f : α → β // ∀ a, f (σ a) = f a} =
      Fintype.card β ^ permutationCycleCount σ := by
  rw [Fintype.card_congr (permutationInvariantColoringsEquiv (β := β) σ), Fintype.card_fun]
  rfl

theorem permutation_invariant_fin_coloring_card {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (n : ℕ) :
    Fintype.card {f : α → Fin n // ∀ a, f (σ a) = f a} = n ^ permutationCycleCount σ := by
  have h := permutation_invariant_coloring_card (β := Fin n) σ
  simp only [Fintype.card_subtype] at h ⊢
  simpa only [Fintype.card_fin] using h

end CircularLaw
