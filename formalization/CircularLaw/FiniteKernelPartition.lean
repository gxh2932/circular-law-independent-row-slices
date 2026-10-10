import CircularLaw.FiniteKernelColorings
import Mathlib.Data.Fintype.Sets

/-!
# Partitioning all finite colorings by their exact equality pattern

There are finitely many equivalence relations on a finite position set.
Every coloring belongs to exactly one kernel fiber. Consequently a sum
over all colorings can be grouped by its exact vertex pattern. If the
summand is constant on each kernel fiber, the coefficient is exactly the
falling factorial supplied by `FiniteKernelColorings`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

instance finiteSetoidFintype (α : Type*) [Fintype α] : Fintype (Setoid α) :=
  Fintype.ofInjective (fun s : Setoid α => s.r) (by
    intro s t h
    apply Setoid.ext
    intro a c
    exact Iff.of_eq (congrFun (congrFun h a) c))

def kernelFiberColoringsEquiv {α β : Type*} (s : Setoid α) :
    {f : α → β // Setoid.ker f = s} ≃ {f : α → β // ∀ a c, f a = f c ↔ s a c} :=
  Equiv.subtypeEquivRight (fun f => by
    constructor
    · intro h
      subst s
      exact fun _ _ => Iff.rfl
    · intro h
      apply Setoid.ext
      exact h)

def allKernelColoringsEquiv {α β : Type*} :
    (α → β) ≃ Σ s : Setoid α, {f : α → β // ∀ a c, f a = f c ↔ s a c} :=
  (Equiv.sigmaFiberEquiv (fun f : α → β => Setoid.ker f)).symm.trans
    (Equiv.sigmaCongrRight kernelFiberColoringsEquiv)

theorem all_kernel_colorings_value {α β : Type*} (f : α → β) :
    (allKernelColoringsEquiv f).2.val = f := rfl

theorem sum_fixed_kernel_colorings {α β M : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [AddCommMonoid M] (F : (α → β) → M) :
    (∑ f, F f) = ∑ s : Setoid α,
      ∑ f : {f : α → β // ∀ a c, f a = f c ↔ s a c}, F f.val := by
  calc
    _ = ∑ x : Σ s : Setoid α, {f : α → β // ∀ a c, f a = f c ↔ s a c}, F x.2.val :=
      Fintype.sum_equiv allKernelColoringsEquiv F (fun x => F x.2.val) (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

theorem sum_kernel_constant_colorings {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (F : (α → β) → ℝ) (G : Setoid α → ℝ)
    (hFiber : ∀ s (f : α → β), (∀ a c, f a = f c ↔ s a c) → F f = G s) :
    (∑ f, F f) = ∑ s : Setoid α,
      ((Nat.card β).descFactorial (Nat.card (Quotient s)) : ℝ) * G s := by
  rw [sum_fixed_kernel_colorings]
  apply Finset.sum_congr rfl
  intro s _
  calc
    _ = ∑ _f : {f : α → β // ∀ a c, f a = f c ↔ s a c}, G s :=
      Finset.sum_congr rfl (fun f _ => hFiber s f.val f.property)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card, fixed_kernel_coloring_card]

theorem sum_kernel_constant_fin_colorings {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (F : (α → Fin n) → ℝ) (G : Setoid α → ℝ)
    (hFiber : ∀ s (f : α → Fin n), (∀ a c, f a = f c ↔ s a c) → F f = G s) :
    (∑ f, F f) = ∑ s : Setoid α,
      (n.descFactorial (Nat.card (Quotient s)) : ℝ) * G s := by
  simpa only [Nat.card_fin] using sum_kernel_constant_colorings F G hFiber

end CircularLaw
