import CircularLaw.GaussianEntryProducts
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.BigOperators.Fin

/-!
# Counting Gaussian direct-to-conjugate pairings at every order

A matching permutation transports each conjugate occurrence to a direct
occurrence of the same entry. When fiber counts agree, these matchings
form a torsor for permutations preserving the direct entry labels.
Their number is the product of the fiber factorials. Repeated indices
are counted with their actual multiplicities.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem function_fiber_card_comp_perm {α ι : Type*} [Fintype α]
    (u : α → ι) (e : Equiv.Perm α) (i : ι) :
    Fintype.card {a // (u ∘ e) a = i} = Fintype.card {a // u a = i} := by
  exact Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))

theorem matching_permutation_fiber_card {α ι : Type*} [Fintype α]
    (u v : α → ι) (e : Equiv.Perm α) (he : u ∘ e = v) (i : ι) :
    Fintype.card {a // u a = i} = Fintype.card {a // v a = i} := by
  rw [← he]
  exact (function_fiber_card_comp_perm u e i).symm

theorem function_matching_permutation_card {α ι : Type*} [Fintype α] [Fintype ι]
    (u v : α → ι) :
    Fintype.card {e : Equiv.Perm α // u ∘ e = v} =
      if ∀ i, Fintype.card {a // u a = i} = Fintype.card {a // v a = i}
      then ∏ i, (Fintype.card {a // u a = i}).factorial else 0 := by
  by_cases h : ∀ i, Fintype.card {a // u a = i} = Fintype.card {a // v a = i}
  · rw [if_pos h]
    let fibers (i : ι) : {a // v a = i} ≃ {a // u a = i} :=
      Fintype.equivOfCardEq (h i).symm
    let e : Equiv.Perm α := Equiv.ofFiberEquiv fibers
    have he : u ∘ e = v := funext (Equiv.ofFiberEquiv_map fibers)
    let matchEquiv : {τ : Equiv.Perm α // u ∘ τ = u} ≃
        {σ : Equiv.Perm α // u ∘ σ = v} :=
      Equiv.subtypeEquiv (Equiv.mulRight e) (fun τ => by
        constructor
        · intro hτ
          funext a
          exact (congrFun hτ (e a)).trans (congrFun he a)
        · intro hτ
          funext a
          obtain ⟨b, rfl⟩ := e.surjective a
          exact (congrFun hτ b).trans (congrFun he b).symm)
    rw [← Fintype.card_congr matchEquiv, DomMulAct.stabilizer_card]
  · rw [if_neg h]
    haveI : IsEmpty {e : Equiv.Perm α // u ∘ e = v} := ⟨fun e =>
      h (matching_permutation_fiber_card u v e.val e.property)⟩
    exact Fintype.card_eq_zero

theorem list_ofFn_count_eq_fiber_card {ι : Type*} [DecidableEq ι] {k : ℕ}
    (u : Fin k → ι) (i : ι) :
    (List.ofFn u).count i = Fintype.card {j // u j = i} := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp only [beq_iff_eq]
    exact add_comm _ _

end CircularLaw
