import CircularLaw.TalagrandInductionGeometry
import Mathlib.Analysis.MeanInequalities

/-!
# Finite product laws for Talagrand induction

Coordinate weights may be arbitrary nonnegative probabilities. The
product expectation, disintegration into a first coordinate and tail,
and event masses are derived from their literal finite sums.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

variable {α : Type*} [Fintype α] {n : ℕ}

def finiteProductWeight (μ : Fin n → α → ℝ) (x : Fin n → α) : ℝ := ∏ i, μ i (x i)

def finiteProductExpectation (μ : Fin n → α → ℝ) (f : (Fin n → α) → ℝ) : ℝ :=
  ∑ x, finiteProductWeight μ x * f x

def finiteProductEventMass (μ : Fin n → α → ℝ) (A : Set (Fin n → α)) : ℝ :=
  finiteProductExpectation μ (fun x => if x ∈ A then 1 else 0)

omit [Fintype α] in
theorem finiteProductWeight_nonneg {μ : Fin n → α → ℝ} (hμ : ∀ i t, 0 ≤ μ i t)
    (x : Fin n → α) : 0 ≤ finiteProductWeight μ x := Finset.prod_nonneg (fun i _ => hμ i (x i))

theorem finiteProductExpectation_mono {μ : Fin n → α → ℝ} (hμ : ∀ i t, 0 ≤ μ i t)
    {f g : (Fin n → α) → ℝ} (h : ∀ x, f x ≤ g x) :
    finiteProductExpectation μ f ≤ finiteProductExpectation μ g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (finiteProductWeight_nonneg hμ x))

theorem finiteProductExpectation_nonneg {μ : Fin n → α → ℝ} (hμ : ∀ i t, 0 ≤ μ i t)
    {f : (Fin n → α) → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteProductExpectation μ f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (finiteProductWeight_nonneg hμ x) (hf x))

theorem finiteProductExpectation_zero_dim (μ : Fin 0 → α → ℝ) (f : (Fin 0 → α) → ℝ) :
    finiteProductExpectation μ f = f Fin.elim0 := by
  simp only [finiteProductExpectation, finiteProductWeight, Fintype.prod_empty, one_mul, Fintype.sum_unique]
  exact congrArg f (Subsingleton.elim _ _)

omit [Fintype α] in
theorem finiteProductWeight_cons (μ : Fin (n + 1) → α → ℝ) (t : α) (x : Fin n → α) :
    finiteProductWeight μ (Fin.cons t x) = μ 0 t * finiteProductWeight (fun i => μ i.succ) x := by
  simp only [finiteProductWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem finiteProductExpectation_cons (μ : Fin (n + 1) → α → ℝ)
    (f : (Fin (n + 1) → α) → ℝ) :
    finiteProductExpectation μ f =
      ∑ t, μ 0 t * finiteProductExpectation (fun i => μ i.succ) (fun x => f (Fin.cons t x)) := by
  unfold finiteProductExpectation
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).sum_comp, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro x _
  change finiteProductWeight μ (Fin.cons t x) * f (Fin.cons t x) = _
  rw [finiteProductWeight_cons]
  ring

theorem finiteProductExpectation_const {μ : Fin n → α → ℝ} (hNorm : ∀ i, ∑ t, μ i t = 1)
    (c : ℝ) : finiteProductExpectation μ (fun _ => c) = c := by
  induction n with
  | zero => exact finiteProductExpectation_zero_dim _ _
  | succ n ih =>
    rw [finiteProductExpectation_cons]
    simp_rw [ih (fun i => hNorm i.succ)]
    rw [← Finset.sum_mul, hNorm 0, one_mul]

theorem finiteProductEventMass_nonneg {μ : Fin n → α → ℝ} (hμ : ∀ i t, 0 ≤ μ i t)
    (A : Set (Fin n → α)) : 0 ≤ finiteProductEventMass μ A :=
  finiteProductExpectation_nonneg hμ (fun _ => by split_ifs <;> norm_num)

theorem finiteProductEventMass_mono {μ : Fin n → α → ℝ} (hμ : ∀ i t, 0 ≤ μ i t)
    {A B : Set (Fin n → α)} (hAB : A ⊆ B) : finiteProductEventMass μ A ≤ finiteProductEventMass μ B := by
  apply finiteProductExpectation_mono hμ
  intro x
  by_cases hx : x ∈ A
  · simp only [if_pos hx, if_pos (hAB hx), le_refl]
  · simp only [if_neg hx]; split_ifs <;> norm_num

theorem finiteProductEventMass_le_one {μ : Fin n → α → ℝ} (hμ : ∀ i t, 0 ≤ μ i t)
    (hNorm : ∀ i, ∑ t, μ i t = 1) (A : Set (Fin n → α)) : finiteProductEventMass μ A ≤ 1 := by
  rw [← finiteProductExpectation_const hNorm 1]
  apply finiteProductExpectation_mono hμ
  intro x
  split_ifs <;> norm_num

theorem finiteProductEventMass_pos_nonempty {μ : Fin n → α → ℝ} {A : Set (Fin n → α)}
    (hA : 0 < finiteProductEventMass μ A) : A.Nonempty := by
  by_contra hEmpty
  have hNot : ∀ x, x ∉ A := fun x hx => hEmpty ⟨x, hx⟩
  simp only [finiteProductEventMass, finiteProductExpectation, if_neg (hNot _),
    mul_zero, Finset.sum_const_zero] at hA
  exact lt_irrefl 0 hA

theorem finiteProductEventMass_cons (μ : Fin (n + 1) → α → ℝ) (A : Set (Fin (n + 1) → α)) :
    finiteProductEventMass μ A =
      ∑ t, μ 0 t * finiteProductEventMass (fun i => μ i.succ) (talagrandSlice A t) :=
  finiteProductExpectation_cons μ _

theorem finiteProductExpectation_exp_ge_one {μ : Fin n → α → ℝ} (hμ : ∀ i t, 0 ≤ μ i t)
    (hNorm : ∀ i, ∑ t, μ i t = 1) {f : (Fin n → α) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    1 ≤ finiteProductExpectation μ (fun x => Real.exp (f x)) := by
  rw [← finiteProductExpectation_const hNorm 1]
  exact finiteProductExpectation_mono hμ (fun x => Real.one_le_exp (hf x))

theorem finiteProductExpectation_const_mul (μ : Fin n → α → ℝ) (c : ℝ)
    (f : (Fin n → α) → ℝ) :
    finiteProductExpectation μ (fun x => c * f x) = c * finiteProductExpectation μ f := by
  unfold finiteProductExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end CircularLaw
