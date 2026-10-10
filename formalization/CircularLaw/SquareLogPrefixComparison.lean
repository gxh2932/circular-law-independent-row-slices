import CircularLaw.MonotonePrefixMean
import CircularLaw.SquareSingularSecondMoment

/-!
# Full-to-prefix lower comparison for the ordered singular values

This is the deterministic lower inequality in the manuscript's Bernoulli
logarithmic squeeze. The prefix length is an actual positive integer, and
the entries may have either sign. The finite branch requires strictly
positive singular values; singular samples keep their extended values in
the separately defined empirical logarithmic integral.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def squareNegativeLogAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) : ℝ :=
  if hj : j < n then -Real.log (orderedSquareSingularValues A ⟨j, hj⟩) else 0

theorem squareNegativeLogAt_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    squareNegativeLogAt A j.val = -Real.log (orderedSquareSingularValues A j) := by
  simp only [squareNegativeLogAt, dif_pos j.isLt]

theorem squareNegativeLogAt_monotone {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hPos : ∀ j, 0 < orderedSquareSingularValues A j) :
    MonotoneOn (squareNegativeLogAt A) (Set.Iio n) := by
  intro i hi j hj hij
  change i < n at hi
  change j < n at hj
  simp only [squareNegativeLogAt, dif_pos hi, dif_pos hj]
  apply neg_le_neg
  exact Real.log_le_log (hPos ⟨j, hj⟩)
    (orderedSquareSingularValues_antitone A (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij))

theorem squareNegativeLogAt_full_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ j ∈ Finset.range n, squareNegativeLogAt A j) =
      -∑ j, Real.log (orderedSquareSingularValues A j) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [squareNegativeLogAt_apply, Finset.sum_neg_distrib]

def squareNegativeLogMean {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (-∑ j, Real.log (orderedSquareSingularValues A j)) / n

def squareNegativeLogPrefix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (ell : ℕ) : ℝ :=
  (∑ j ∈ Finset.range ell, squareNegativeLogAt A j) / n

theorem square_full_negative_log_ge_prefix {n ell : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hPos : ∀ j, 0 < orderedSquareSingularValues A j)
    (hEll : 0 < ell) (hElln : ell ≤ n) :
    ((n : ℝ) / ell) * squareNegativeLogPrefix A ell ≤ squareNegativeLogMean A := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le hEll hElln).ne'
  have hEllR : (ell : ℝ) ≠ 0 := by exact_mod_cast hEll.ne'
  have hMean := monotone_prefix_mean_le hEll hElln (squareNegativeLogAt A)
    (squareNegativeLogAt_monotone A hPos)
  rw [squareNegativeLogAt_full_sum] at hMean
  have hScale : ((n : ℝ) / ell) * squareNegativeLogPrefix A ell =
      (∑ j ∈ Finset.range ell, squareNegativeLogAt A j) / ell := by
    unfold squareNegativeLogPrefix
    field_simp
  rw [hScale]
  exact hMean

end CircularLaw
