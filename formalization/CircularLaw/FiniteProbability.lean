import CircularLaw.RowSlice

/-!
# Finite uniform laws

Counting tuples gives precisely the independent uniform row law. Empty
sample spaces have value zero under the totalized definition; the main
theorem's degree hypotheses eventually exclude that case.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

/-- Probability of an event under the finite uniform law. -/
def uniformProbability {α : Type*} [Fintype α] (event : α → Prop) : ℝ :=
  (Nat.card {x // event x} : ℝ) / Nat.card α

theorem uniformProbability_nonneg {α : Type*} [Fintype α] (event : α → Prop) :
    0 ≤ uniformProbability event := by
  classical
  unfold uniformProbability
  positivity

theorem uniformProbability_le_one {α : Type*} [Fintype α] (event : α → Prop) :
    uniformProbability event ≤ 1 := by
  classical
  simp only [uniformProbability, Nat.card_eq_fintype_card]
  by_cases h : Fintype.card α = 0
  · simp [h]
  · have hpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Nat.pos_of_ne_zero h
    rw [div_le_one hpos]
    exact_mod_cast Fintype.card_subtype_le event

theorem uniformProbability_true {α : Type*} [Fintype α] [Nonempty α] :
    uniformProbability (fun _ : α => True) = 1 := by
  classical
  have hpos : Fintype.card α ≠ 0 := Fintype.card_ne_zero
  simp [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype, hpos]

/-- Independent uniform coordinates: every rectangular event has the product
of its coordinate probabilities. This includes degenerate finite products. -/
theorem uniformProbability_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (event : ∀ i, α i → Prop) :
    uniformProbability (fun x : ∀ i, α i => ∀ i, event i (x i)) =
      ∏ i, uniformProbability (event i) := by
  classical
  have hcard : Nat.card {x : ∀ i, α i // ∀ i, event i (x i)} =
      ∏ i, Nat.card {x : α i // event i x} := by
    rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := event))]
    simp [Nat.card_eq_fintype_card]
  have htotal : Nat.card (∀ i, α i) = ∏ i, Nat.card (α i) := by
    simp [Nat.card_eq_fintype_card]
  simp only [uniformProbability, hcard, htotal, Nat.cast_prod, Finset.prod_div_distrib]

/-- The matrix sample space in the main statement has independent uniform
rows, as required by the manuscript. -/
theorem independent_uniform_rows (n d : ℕ) (event : Fin n → RowSlice n d → Prop) :
    uniformProbability (fun s : RowSliceMatrix n d => ∀ i, event i (s i)) =
      ∏ i, uniformProbability (event i) :=
  uniformProbability_pi event

end CircularLaw
