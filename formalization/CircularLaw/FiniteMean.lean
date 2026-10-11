import CircularLaw.FiniteProbability

/-!
# Expectations on finite uniform spaces

These operations retain the exact finite law used for row coordinates and
with-replacement samples. They are preparation for the max-weight estimate
in Section 3, not an assumption of that estimate.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def finiteMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

theorem finiteMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    finiteMean (fun a => f a + g a) = finiteMean f + finiteMean g := by
  simp [finiteMean, Finset.sum_add_distrib, add_div]

theorem finiteMean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    finiteMean (fun a => f a - g a) = finiteMean f - finiteMean g := by
  simp [finiteMean, Finset.sum_sub_distrib, sub_div]

theorem finiteMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    finiteMean (fun a => c * f a) = c * finiteMean f := by
  simp [finiteMean, ← Finset.mul_sum]
  ring

theorem finiteMean_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    finiteMean (fun a => f a * c) = finiteMean f * c := by
  simp only [mul_comm, finiteMean_const_mul]

theorem finiteMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    finiteMean (fun _ : α => c) = c := by
  have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finiteMean, h]

theorem finiteMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : finiteMean f ≤ finiteMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

theorem finiteMean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ finiteMean f := by
  unfold finiteMean
  apply div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

theorem abs_finiteMean_le {α : Type*} [Fintype α] (f : α → ℝ) :
    |finiteMean f| ≤ finiteMean (fun a => |f a|) := by
  have hcard : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  simp only [finiteMean, abs_div, abs_of_nonneg hcard]
  apply div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)

theorem finiteMean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) :
    finiteMean (fun p : α × β => f p.1 * g p.2) = finiteMean f * finiteMean g := by
  simp only [finiteMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.sum_mul_sum]
  ring

theorem finiteMean_fst {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (f : α → ℝ) : finiteMean (fun p : α × β => f p.1) = finiteMean f := by
  simpa only [mul_one, finiteMean_const] using finiteMean_prod f (fun _ : β => 1)

theorem finiteMean_snd {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (g : β → ℝ) : finiteMean (fun p : α × β => g p.2) = finiteMean g := by
  simpa only [one_mul, finiteMean_const] using finiteMean_prod (fun _ : α => 1) g

/-- Independent finite coordinates factor the expectation of a product. -/
theorem finiteMean_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (f : ∀ i, α i → ℝ) :
    finiteMean (fun a : ∀ i, α i => ∏ i, f i (a i)) = ∏ i, finiteMean (f i) := by
  classical
  simp only [finiteMean, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]
  rw [Fintype.prod_sum]

theorem finiteMean_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : finiteMean (fun a => f (e a)) = finiteMean f := by
  unfold finiteMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem finiteMean_prod_fubini {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) :
    finiteMean f = finiteMean (fun q => finiteMean (fun p => f (p, q))) := by
  simp only [finiteMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

end CircularLaw
