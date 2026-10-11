import CircularLaw.FiniteFreshConditionalExpectation
import CircularLaw.BernoulliPrincipalMinorLaw

/-!
# Conditional probabilities for actual disjoint Bernoulli entry blocks

Injective, disjoint coordinate blocks of the ambient Bernoulli cube are
independent. Conditioning on one block therefore averages a function
over the original Bernoulli law of the fresh block, including when its
coefficients or its failure event depend on the exposed entries.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_cube_disjoint_blocks_independent
    {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (p : ℝ≥0) (hp : p ≤ 1) (e : α ↪ ι) (f : β ↪ ι)
    (hDisjoint : ∀ a b, e a ≠ f b) :
    IndepFun (fun x : ι → Bool => fun a => x (e a))
      (fun x : ι → Bool => fun b => x (f b)) (bernoulliCubeLaw ι p hp) := by
  let S := Finset.univ.map e
  let T := Finset.univ.map f
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiT
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hiS
    obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hiT
    exact hDisjoint a b (ha.trans hb.symm)
  have hInd : iIndepFun (fun i : ι => fun x : ι → Bool => x i)
      (bernoulliCubeLaw ι p hp) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hBlocks := hInd.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  let readS : (S → Bool) → α → Bool := fun x a =>
    x ⟨e a, Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  let readT : (T → Bool) → β → Bool := fun x b =>
    x ⟨f b, Finset.mem_map.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩
  exact hBlocks.comp (measurable_of_countable readS) (measurable_of_countable readT)

theorem bernoulli_disjoint_fresh_conditional_expectation
    {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (p : ℝ≥0) (hp : p ≤ 1) (e : α ↪ ι) (f : β ↪ ι)
    (hDisjoint : ∀ a b, e a ≠ f b) (F : (α → Bool) → (β → Bool) → ℝ) :
    (bernoulliCubeLaw ι p hp)[
      (fun x => F (fun a => x (e a)) (fun b => x (f b))) |
        MeasurableSpace.comap (fun x : ι → Bool => fun a => x (e a)) inferInstance] =ᵐ[
          bernoulliCubeLaw ι p hp]
            fun x => ∫ y, F (fun a => x (e a)) y ∂bernoulliCubeLaw β p hp := by
  have h := finite_independent_fresh_conditional_expectation (bernoulliCubeLaw ι p hp)
    (fun x a => x (e a)) (fun x b => x (f b))
    (measurable_of_countable _) (measurable_of_countable _)
    (bernoulli_cube_disjoint_blocks_independent p hp e f hDisjoint) F
  simpa only [bernoulli_cube_law_restrict p hp f] using h

theorem bernoulli_disjoint_fresh_conditional_probability
    {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (p : ℝ≥0) (hp : p ≤ 1) (e : α ↪ ι) (f : β ↪ ι)
    (hDisjoint : ∀ a b, e a ≠ f b) (B : (α → Bool) → (β → Bool) → Prop) :
    (bernoulliCubeLaw ι p hp)[
      ({x | B (fun a => x (e a)) (fun b => x (f b))}).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (fun x : ι → Bool => fun a => x (e a)) inferInstance] =ᵐ[
          bernoulliCubeLaw ι p hp]
            fun x => (bernoulliCubeLaw β p hp).real {y | B (fun a => x (e a)) y} := by
  have h := finite_independent_fresh_conditional_probability (bernoulliCubeLaw ι p hp)
    (fun x a => x (e a)) (fun x b => x (f b))
    (measurable_of_countable _) (measurable_of_countable _)
    (bernoulli_cube_disjoint_blocks_independent p hp e f hDisjoint) B
  simpa only [bernoulli_cube_law_restrict p hp f] using h

theorem bernoulli_disjoint_fresh_conditional_probability_le_on_past
    {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (p : ℝ≥0) (hp : p ≤ 1) (e : α ↪ ι) (f : β ↪ ι)
    (hDisjoint : ∀ a b, e a ≠ f b) (B : (α → Bool) → (β → Bool) → Prop)
    (G : (α → Bool) → Prop) {q : ℝ}
    (hBound : ∀ a, G a → (bernoulliCubeLaw β p hp).real {y | B a y} ≤ q) :
    ∀ᵐ x ∂bernoulliCubeLaw ι p hp, G (fun a => x (e a)) →
      ((bernoulliCubeLaw ι p hp)[
        ({x | B (fun a => x (e a)) (fun b => x (f b))}).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap (fun x : ι → Bool => fun a => x (e a)) inferInstance]) x ≤ q := by
  filter_upwards [bernoulli_disjoint_fresh_conditional_probability p hp e f hDisjoint B]
    with x hx hGood
  exact hx.le.trans (hBound (fun a => x (e a)) hGood)

end CircularLaw
