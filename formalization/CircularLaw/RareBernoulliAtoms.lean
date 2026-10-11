import CircularLaw.BernoulliSliceFibers
import CircularLaw.WeightedBernoulliSmallBall

/-!
# Zero and single-selection masses in an actual Bernoulli cube

The rare-coefficient small-ball bound uses exact product-law atoms.
Their masses retain the number of selected coefficients, rather than
using an anti-concentration bound that deteriorates at small density.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace CircularLaw

def bernoulliSingleSelection {ι : Type*} [Fintype ι] (i : ι) : ι → Bool :=
  fun j => decide (j = i)

def bernoulliSingleSelections (ι : Type*) [Fintype ι] : Finset (ι → Bool) :=
  Finset.univ.image bernoulliSingleSelection

theorem bernoulli_single_selection_injective {ι : Type*} [Fintype ι] :
    Function.Injective (bernoulliSingleSelection : ι → ι → Bool) := by
  intro i j h
  have hi := congrFun h i
  simpa [bernoulliSingleSelection] using hi.symm

theorem bernoulli_cube_singleton_product_real {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (x : ι → Bool) :
    (bernoulliCubeLaw ι p hp).real {x} =
      ∏ i, if x i = true then (p : ℝ) else 1 - (p : ℝ) := by
  rw [measureReal_def, bernoulliCubeLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, bernoulliCoordinateLaw_singleton_real]

theorem bernoulli_cube_zero_atom_real {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliCubeLaw ι p hp).real {fun _ : ι => false} =
      (1 - (p : ℝ)) ^ Fintype.card ι := by
  rw [bernoulli_cube_singleton_product_real]
  simp

theorem bernoulli_cube_single_selection_real {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (i : ι) :
    (bernoulliCubeLaw ι p hp).real {bernoulliSingleSelection i} =
      (p : ℝ) * (1 - (p : ℝ)) ^ (Fintype.card ι - 1) := by
  rw [bernoulli_cube_singleton_product_real,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [bernoulliSingleSelection, decide_eq_true_eq]
  congr 1
  calc
    _ = ∏ _j ∈ Finset.univ.erase i, (1 - (p : ℝ)) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [if_neg (Finset.ne_of_mem_erase hj)]
    _ = _ := by simp

theorem bernoulli_cube_single_selections_real {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliCubeLaw ι p hp).real (bernoulliSingleSelections ι) =
      (Fintype.card ι : ℝ) * p * (1 - (p : ℝ)) ^ (Fintype.card ι - 1) := by
  rw [← sum_measureReal_singleton, bernoulliSingleSelections,
    Finset.sum_image (fun _ _ _ _ h => bernoulli_single_selection_injective h)]
  simp only [bernoulli_cube_single_selection_real, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

theorem weighted_bernoulli_zero_selection {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    (∑ i, weightedBernoulliValue (a i) false) = 0 := by
  simp [weightedBernoulliValue]

theorem weighted_bernoulli_single_selection {ι : Type*} [Fintype ι] (a : ι → ℂ) (i : ι) :
    (∑ j, weightedBernoulliValue (a j) (bernoulliSingleSelection i j)) = a i := by
  have hValue : ∀ j, weightedBernoulliValue (a j) (bernoulliSingleSelection i j) =
      if j = i then a j else 0 := by
    intro j
    by_cases h : j = i <;> simp [weightedBernoulliValue, bernoulliSingleSelection, h]
  simp_rw [hValue]
  simp

theorem bernoulli_zero_selection_probability_lower (p : ℝ≥0) (hp : p ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * p ≤ (1 - (p : ℝ)) ^ m := by
  have h := one_add_mul_le_pow (by
    have hpR : (p : ℝ) ≤ 1 := by exact_mod_cast hp
    linarith : (-2 : ℝ) ≤ -(p : ℝ)) m
  simpa only [mul_neg, add_neg_cancel, sub_eq_add_neg] using h

end CircularLaw
