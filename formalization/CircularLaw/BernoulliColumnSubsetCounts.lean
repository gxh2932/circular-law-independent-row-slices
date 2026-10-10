import CircularLaw.BernoulliSubsetCountLaplace
import CircularLaw.ShiftedGraphBudgets
import CircularLaw.BernoulliSquareMatrixLaw

/-!
# Actual rectangular Bernoulli column counts

The graph column support counts equal the sums of the corresponding
Boolean entries. Their exponential tails follow from the actual product
law on the rectangular entry set.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal Matrix

namespace CircularLaw

def bernoulliRectangularMatrix {ρ ι : Type*} (x : ρ × ι → Bool) : Matrix ρ ι ℂ :=
  fun i j => cond (x (i, j)) 1 0

theorem bernoulli_rectangular_square_eq {n : ℕ} (x : BernoulliSquareSample n) :
    bernoulliRectangularMatrix x = bernoulliSquareMatrix x := rfl

theorem bernoulli_rectangular_entry_norm_le_one {ρ ι : Type*}
    (x : ρ × ι → Bool) (i : ρ) (j : ι) : ‖bernoulliRectangularMatrix x i j‖ ≤ 1 := by
  cases h : x (i, j) <;> simp [bernoulliRectangularMatrix, h]

theorem bernoulli_rectangular_column_support_card {ρ ι : Type*} [Fintype ρ]
    (x : ρ × ι → Bool) (j : ι) :
    ((matrixColumnSupport (bernoulliRectangularMatrix x) j).card : ℝ) =
      ∑ i, (cond (x (i, j)) 1 0 : ℝ) := by
  simp only [matrixColumnSupport, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases h : x (i, j) <;> simp [bernoulliRectangularMatrix, h]

theorem bernoulli_rectangular_row_l1_mass {ρ ι : Type*} [Fintype ι]
    (x : ρ × ι → Bool) (i : ρ) :
    matrixRowL1Mass (bernoulliRectangularMatrix x) i =
      ∑ j, (cond (x (i, j)) 1 0 : ℝ) := by
  apply Finset.sum_congr rfl
  intro j _
  cases h : x (i, j) <;> simp [bernoulliRectangularMatrix, h]

theorem bernoulli_column_subset_count_eq {ρ ι : Type*} [Fintype ρ]
    (T : Finset ι) (x : ρ × ι → Bool) :
    (∑ j ∈ T, ((matrixColumnSupport (bernoulliRectangularMatrix x) j).card : ℝ)) =
      bernoulliSubsetCount (Finset.univ.product T) x := by
  simp_rw [bernoulli_rectangular_column_support_card]
  rw [Finset.sum_comm, bernoulliSubsetCount]
  exact (Finset.sum_product Finset.univ T (fun ij => (cond (x ij) 1 0 : ℝ))).symm

theorem bernoulli_column_subset_count_upper_tail {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (T : Finset ι) {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    (bernoulliCubeLaw (ρ × ι) p hp).real {x |
      u ≤ ∑ j ∈ T, ((matrixColumnSupport (bernoulliRectangularMatrix x) j).card : ℝ)} ≤
      Real.exp ((Fintype.card ρ : ℝ) * T.card * p * (Real.exp t - 1) - t * u) := by
  simp_rw [bernoulli_column_subset_count_eq]
  simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Nat.cast_mul] using
    bernoulli_subset_count_upper_tail p hp ((Finset.univ : Finset ρ).product T) ht u

end CircularLaw
