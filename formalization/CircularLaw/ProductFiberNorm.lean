import CircularLaw.IndependentLogTail

/-!
# Norm estimates on exposed independent-row fibers

The retained row set may depend on the exposed reference. Conditioning on
all row statistics gives the actual product of uniform row fibers. The
unused row fibers integrate out exactly, leaving the norm estimate on the
selected rows.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem product_fiber_subset_norm_small_ball_log {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (β i)]
    (f : ∀ i, α i → β i) (reference : ∀ i, α i) (I : Finset ι)
    (Y : ∀ i, α i → ℂ) {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    (hProb : ∀ i ∈ I, uniformProbability
      (fun a : {a : α i // f i a = f i (reference i)} => ‖Y i a.val‖ < r) ≤ p) :
    uniformProbability (fun x : {x : ∀ i, α i //
      (fun i => f i (x i)) = (fun i => f i (reference i))} =>
      (∑ i : I, ‖Y i.val (x.val i.val)‖ ^ 2) ≤ r ^ 2 * (I.card : ℝ) / 8) ≤
        Real.exp (-witnessLogRate * I.card * Real.log (1 / p)) := by
  classical
  let γ := fun i => {a : α i // f i a = f i (reference i)}
  letI : ∀ i, Nonempty (γ i) := fun i => ⟨⟨reference i, rfl⟩⟩
  rw [uniformProbability_product_fiber_eq f reference (fun x : ∀ i, α i =>
    (∑ i : I, ‖Y i.val (x i.val)‖ ^ 2) ≤ r ^ 2 * (I.card : ℝ) / 8)]
  rw [uniformProbability_pi_restrict I
    (fun x : ∀ i : I, γ i.val =>
      (∑ i : I, ‖Y i.val (x i).val‖ ^ 2) ≤ r ^ 2 * (I.card : ℝ) / 8)]
  simpa only [Fintype.card_coe] using
    independent_norm_small_ball_log (fun i : I => fun a : γ i.val => Y i.val a.val)
      hr hp hpHalf (fun i => hProb i.val i.property)

theorem product_fiber_subset_norm_small_ball_half {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (β i)]
    (f : ∀ i, α i → β i) (reference : ∀ i, α i) (I : Finset ι)
    (Y : ∀ i, α i → ℂ) {r : ℝ} (hr : 0 < r)
    (hProb : ∀ i ∈ I, uniformProbability
      (fun a : {a : α i // f i a = f i (reference i)} => ‖Y i a.val‖ < r) ≤ 1 / 2) :
    uniformProbability (fun x : {x : ∀ i, α i //
      (fun i => f i (x i)) = (fun i => f i (reference i))} =>
      (∑ i : I, ‖Y i.val (x.val i.val)‖ ^ 2) ≤ r ^ 2 * (I.card : ℝ) / 8) ≤
        Real.exp (-witnessHalfRate * I.card) := by
  classical
  let γ := fun i => {a : α i // f i a = f i (reference i)}
  letI : ∀ i, Nonempty (γ i) := fun i => ⟨⟨reference i, rfl⟩⟩
  rw [uniformProbability_product_fiber_eq f reference (fun x : ∀ i, α i =>
    (∑ i : I, ‖Y i.val (x i.val)‖ ^ 2) ≤ r ^ 2 * (I.card : ℝ) / 8)]
  rw [uniformProbability_pi_restrict I
    (fun x : ∀ i : I, γ i.val =>
      (∑ i : I, ‖Y i.val (x i).val‖ ^ 2) ≤ r ^ 2 * (I.card : ℝ) / 8)]
  simpa only [Fintype.card_coe] using
    independent_norm_small_ball_half (fun i : I => fun a : γ i.val => Y i.val a.val)
      hr (fun i => hProb i.val i.property)

end CircularLaw
