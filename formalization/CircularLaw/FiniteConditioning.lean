import CircularLaw.Conditioning

/-!
# Exact finite conditioning and mixtures

A finite statistic partitions a uniform sample space into uniform fibers.
This file proves the law of total expectation with its genuine fiber masses,
including empty fibers. It also proves the convolution bound used after
fixing row-profile counts.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

theorem uniformProbability_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (E : β → Prop) :
    uniformProbability (fun a => E (e a)) = uniformProbability E := by
  classical
  rw [← finiteMean_indicator, finiteMean_reindex e
    (fun b => if E b then (1 : ℝ) else 0), finiteMean_indicator]

theorem card_mul_finiteMean {α : Type*} [Fintype α] (g : α → ℝ) :
    (Fintype.card α : ℝ) * finiteMean g = ∑ a, g a := by
  unfold finiteMean
  by_cases h : Fintype.card α = 0
  · haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp h
    simp
  · have hreal : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast h
    field_simp

/-- Finite disintegration: empty fibers contribute zero, and nonempty
fibers carry the conditional uniform law. -/
theorem finiteMean_disintegrate {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (g : α → ℝ) :
    finiteMean g = ∑ y, uniformProbability (fun a => f a = y) *
      finiteMean (fun a : {a // f a = y} => g a.val) := by
  classical
  have hs : (∑ a, g a) = ∑ y, ∑ a : {a // f a = y}, g a.val := by
    rw [← (Equiv.sigmaFiberEquiv f).sum_comp g, Fintype.sum_sigma]
    rfl
  unfold finiteMean at ⊢
  rw [hs]
  simp only [uniformProbability, Nat.card_eq_fintype_card]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  have h := card_mul_finiteMean (fun a : {a // f a = y} => g a.val)
  dsimp only [finiteMean] at h
  rw [show (Fintype.card {a // f a = y} : ℝ) / (Fintype.card α : ℝ) *
      ((∑ a : {a // f a = y}, g a.val) / Fintype.card {a // f a = y}) =
        ((Fintype.card {a // f a = y} : ℝ) *
          ((∑ a : {a // f a = y}, g a.val) / Fintype.card {a // f a = y})) /
            Fintype.card α by ring, h]

theorem uniformProbability_disintegrate {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (E : α → Prop) :
    uniformProbability E = ∑ y, uniformProbability (fun a => f a = y) *
      uniformProbability (fun a : {a // f a = y} => E a.val) := by
  classical
  rw [← finiteMean_indicator E, finiteMean_disintegrate f]
  simp only [finiteMean_indicator]

theorem finiteMean_part_mass {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (w : β → ℝ) :
    finiteMean (fun a => w (f a)) = ∑ y, uniformProbability (fun a => f a = y) * w y := by
  classical
  rw [finiteMean_disintegrate f]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : Nonempty {a // f a = y}
  · letI := h
    have hf : (fun a : {a // f a = y} => w (f a.val)) = (fun _ => w y) :=
      funext (fun a => congrArg w a.property)
    rw [hf, finiteMean_const]
  · haveI : IsEmpty {a // f a = y} := not_nonempty_iff.mp h
    simp [uniformProbability]

/-- Fiberwise event bounds average with the distribution of the statistic.
The hypotheses only need to hold on fibers which actually occur. -/
theorem uniformProbability_le_fiberwise {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (E : α → Prop) (w : β → ℝ)
    (hbound : ∀ y, Nonempty {a // f a = y} →
      uniformProbability (fun a : {a // f a = y} => E a.val) ≤ w y) :
    uniformProbability E ≤ finiteMean (fun a => w (f a)) := by
  classical
  rw [uniformProbability_disintegrate f E, finiteMean_part_mass f w]
  apply Finset.sum_le_sum
  intro y _
  by_cases h : Nonempty {a // f a = y}
  · exact mul_le_mul_of_nonneg_left (hbound y h) (uniformProbability_nonneg _)
  · haveI : IsEmpty {a // f a = y} := not_nonempty_iff.mp h
    simp [uniformProbability]

theorem uniformProbability_prod_fubini {α β : Type*} [Fintype α] [Fintype β]
    (E : α × β → Prop) :
    uniformProbability E = finiteMean (fun b => uniformProbability (fun a => E (a, b))) := by
  classical
  rw [← finiteMean_indicator E, finiteMean_prod_fubini]
  simp only [finiteMean_indicator]

/-- A conditional bound which is constant on each fiber can be averaged
without choosing or assuming a separate distribution on the statistic. -/
theorem uniformProbability_le_fiber_reference {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) (E : α → Prop) (S : α → ℝ)
    (hconstant : ∀ a b, f a = f b → S a = S b)
    (hbound : ∀ reference : α,
      uniformProbability (fun a : {a // f a = f reference} => E a.val) ≤ S reference) :
    uniformProbability E ≤ finiteMean S := by
  classical
  rw [uniformProbability_disintegrate f E, finiteMean_disintegrate f S]
  apply Finset.sum_le_sum
  intro y _
  by_cases h : Nonempty {a // f a = y}
  · rcases h with ⟨reference⟩
    letI : Nonempty {a // f a = y} := ⟨reference⟩
    have hs : (fun a : {a // f a = y} => S a.val) = (fun _ => S reference.val) := by
      funext a
      exact hconstant a.val reference.val (a.property.trans reference.property.symm)
    rw [hs, finiteMean_const]
    apply mul_le_mul_of_nonneg_left _ (uniformProbability_nonneg _)
    have h := hbound reference.val
    rwa [reference.property] at h
  · haveI : IsEmpty {a // f a = y} := not_nonempty_iff.mp h
    simp [uniformProbability]

/-- Fixing the independent other summand merely changes the center. -/
theorem uniformProbability_add_small_ball {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (X : α → ℂ) (Y : β → ℂ) {r A : ℝ}
    (hX : ∀ z : ℂ, uniformProbability (fun a => ‖X a - z‖ ≤ r) ≤ A) (z : ℂ) :
    uniformProbability (fun p : α × β => ‖X p.1 + Y p.2 - z‖ ≤ r) ≤ A := by
  rw [uniformProbability_prod_fubini]
  calc
    _ ≤ finiteMean (fun _ : β => A) := by
      apply finiteMean_mono
      intro b
      convert hX (z - Y b) using 1
      congr 1
      funext a
      congr 2
      ring
    _ = A := finiteMean_const A

/-- An independent sum has no greater concentration than any one of its
summands, uniformly in the center. -/
theorem uniformProbability_pi_sum_small_ball {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (Y : ∀ i, β i → ℂ) (q : ι) {r A : ℝ}
    (hq : ∀ z : ℂ, uniformProbability (fun b : β q => ‖Y q b - z‖ ≤ r) ≤ A) (z : ℂ) :
    uniformProbability (fun b : ∀ i, β i => ‖(∑ i, Y i (b i)) - z‖ ≤ r) ≤ A := by
  classical
  let e := Equiv.piSplitAt q β
  have hsum (p : β q × (∀ i : {i : ι // i ≠ q}, β i.val)) :
      (∑ i, Y i (e.symm p i)) = Y q p.1 + ∑ i, Y i.val (p.2 i) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ q]
    have hfirst : e.symm p q = p.1 := by simp [e, Equiv.piSplitAt_symm_apply]
    rw [hfirst]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hi : e.symm p i.val = p.2 i := by
      simp only [e, Equiv.piSplitAt_symm_apply, dif_neg i.property]
    rw [hi]
  rw [← uniformProbability_reindex e.symm
    (fun b : ∀ i, β i => ‖(∑ i, Y i (b i)) - z‖ ≤ r)]
  simp_rw [hsum]
  rw [uniformProbability_prod_fubini]
  calc
    _ ≤ finiteMean (fun _ : ∀ i : {i : ι // i ≠ q}, β i.val => A) := by
      apply finiteMean_mono
      intro b
      convert hq (z - ∑ i, Y i.val (b i)) using 1
      congr 1
      funext a
      congr 2
      ring
    _ = A := finiteMean_const A

end CircularLaw
