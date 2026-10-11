import CircularLaw.FiniteRelationColorings
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Exact coloring counts for a fixed equality pattern

When a closed-walk vertex pattern specifies exactly which positions
coincide, its colorings are embeddings of its quotient into the ambient
index set. Their count is the falling factorial, rather than a power
that also counts further identifications. For a fixed pattern the
falling factorial divided by the corresponding dimension power tends
to one. These statements retain every equality and inequality of the
pattern and do not assume a moment limit.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def fixedKernelColoringsEquiv {α β : Type*} (s : Setoid α) :
    {f : α → β // ∀ a c, f a = f c ↔ s a c} ≃ (Quotient s ↪ β) where
  toFun f :=
    { toFun := Quotient.lift f.val (fun a c h => (f.property a c).mpr h)
      inj' := by
        intro qa qc h
        induction qa using Quotient.inductionOn with
        | h a =>
          induction qc using Quotient.inductionOn with
          | h c =>
            exact Quotient.sound ((f.property a c).mp h) }
  invFun g :=
    ⟨fun a => g (Quotient.mk s a), fun a c =>
      ⟨fun h => Quotient.exact (g.injective h),
        fun h => congrArg g (Quotient.sound h)⟩⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv g := by
    apply DFunLike.ext
    intro q
    induction q using Quotient.inductionOn with
    | h a => rfl

theorem fixed_kernel_coloring_card {α β : Type*} [Fintype α] [Fintype β]
    (s : Setoid α) :
    Nat.card {f : α → β // ∀ a c, f a = f c ↔ s a c} =
      (Nat.card β).descFactorial (Nat.card (Quotient s)) := by
  rw [Nat.card_congr (fixedKernelColoringsEquiv (β := β) s)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]

theorem fixed_kernel_fin_coloring_card {α : Type*} [Fintype α]
    (s : Setoid α) (n : ℕ) :
    Nat.card {f : α → Fin n // ∀ a c, f a = f c ↔ s a c} =
      n.descFactorial (Nat.card (Quotient s)) := by
  simpa only [Nat.card_fin] using fixed_kernel_coloring_card (β := Fin n) s

theorem fixed_kernel_coloring_range_card {α β : Type*} (s : Setoid α)
    (f : α → β) (hKernel : ∀ a c, f a = f c ↔ s a c) :
    Nat.card (Set.range f) = Nat.card (Quotient s) := by
  have hKer : Setoid.ker f = s := Setoid.ext hKernel
  rw [← hKer]
  exact (Nat.card_congr (Setoid.quotientKerEquivRange f)).symm

theorem fixed_kernel_fin_coloring_card_le_power {α : Type*} [Fintype α]
    (s : Setoid α) (n : ℕ) :
    Nat.card {f : α → Fin n // ∀ a c, f a = f c ↔ s a c} ≤
      n ^ Nat.card (Quotient s) := by
  rw [fixed_kernel_fin_coloring_card]
  exact Nat.descFactorial_le_pow n _

theorem fixed_desc_factorial_ratio_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial r : ℝ) / (n : ℝ) ^ r)
      atTop (𝓝 1) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp (isEquivalent_descFactorial r)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact pow_ne_zero _ (by exact_mod_cast hn.ne')

theorem fixed_kernel_fin_coloring_ratio_tendsto {α : Type*} [Fintype α]
    (s : Setoid α) :
    Tendsto (fun n : ℕ =>
      (Nat.card {f : α → Fin n // ∀ a c, f a = f c ↔ s a c} : ℝ) /
        (n : ℝ) ^ Nat.card (Quotient s)) atTop (𝓝 1) := by
  simp only [fixed_kernel_fin_coloring_card]
  exact fixed_desc_factorial_ratio_tendsto _

end CircularLaw
