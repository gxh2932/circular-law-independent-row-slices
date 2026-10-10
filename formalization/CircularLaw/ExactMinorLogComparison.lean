import CircularLaw.PrincipalSingularInterlacing
import CircularLaw.RoundedMinorLogReview

/-!
# An integer-compatible principal-minor logarithmic upper comparison

The exact index shift is `r = 2*(n-m)`, and the ambient interval is the
zero-based half-open interval `[r,m)`. Its cardinality is exactly `m-r`.
The remaining `ell-(m-r)` terms are bounded by the last retained minor
term. This proves a corrected finite comparison, with all integer
conditions explicit. It does not assert the manuscript's rounded formula
or the still-unproved probabilistic convergence squeeze.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem prefix_sum_le_shifted_head_and_tail {ell k r : ℕ} (hkle : k ≤ ell)
    (f g : ℕ → ℝ) (t : ℝ) (hHead : ∀ i < k, f i ≤ g (i + r))
    (hTail : ∀ i, k ≤ i → i < ell → f i ≤ t) :
    (∑ i ∈ Finset.range ell, f i) ≤
      (∑ i ∈ Finset.range k, g (i + r)) + (ell - k : ℕ) * t := by
  calc
    _ = (∑ i ∈ Finset.range k, f i) + ∑ i ∈ Finset.Ico k ell, f i :=
      (Finset.sum_range_add_sum_Ico f hkle).symm
    _ ≤ (∑ i ∈ Finset.range k, g (i + r)) + ∑ _i ∈ Finset.Ico k ell, t :=
      add_le_add (Finset.sum_le_sum (fun i hi => hHead i (Finset.mem_range.mp hi)))
        (Finset.sum_le_sum (fun i hi => hTail i (Finset.mem_Ico.mp hi).1
          (Finset.mem_Ico.mp hi).2))
    _ = _ := by simp

theorem square_minor_negative_log_le_shifted {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hmn : m ≤ n)
    (hPos : ∀ j, 0 < orderedSquareSingularValues A j) (i : Fin m) (j : Fin n)
    (hIndex : j.val = i.val + 2 * (n - m)) :
    squareNegativeLogAt (squarePrincipalMinor A hmn) i.val ≤ squareNegativeLogAt A j.val := by
  rw [squareNegativeLogAt_apply, squareNegativeLogAt_apply]
  apply neg_le_neg
  apply Real.log_le_log (hPos j)
  exact ambient_singular_value_le_principal A
    ⟨Fin.castLE hmn, Fin.castLE_injective hmn⟩ i j hIndex

def squareMinorLogUpperExact {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hmn : m ≤ n) (ell : ℕ) : ℝ :=
  ((∑ j ∈ Finset.Ico (2 * (n - m)) m, squareNegativeLogAt A j) +
    (ell - (m - 2 * (n - m)) : ℕ) *
      squareNegativeLogAt (squarePrincipalMinor A hmn) (ell - 1)) / n

theorem square_minor_prefix_le_exact_upper {n m ell : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hmn : m ≤ n)
    (hPos : ∀ j, 0 < orderedSquareSingularValues A j)
    (hMinorPos : ∀ j, j.val < ell →
      0 < orderedSquareSingularValues (squarePrincipalMinor A hmn) j)
    (hDeleted : 2 * (n - m) ≤ m) (hPrefix : m - 2 * (n - m) ≤ ell)
    (hEll : 0 < ell) (hEllm : ell ≤ m) :
    squareMinorNegativeLogPrefix A hmn ell ≤ squareMinorLogUpperExact A hmn ell := by
  let r := 2 * (n - m)
  let k := m - r
  have hHead : ∀ i < k, squareNegativeLogAt (squarePrincipalMinor A hmn) i ≤
      squareNegativeLogAt A (i + r) := by
    intro i hi
    have hiM : i < m := by dsimp [k, r] at hi; omega
    have hiN : i + r < n := by dsimp [k] at hi; dsimp [r]; omega
    exact square_minor_negative_log_le_shifted A hmn hPos ⟨i, hiM⟩ ⟨i + r, hiN⟩ rfl
  have hTail : ∀ i, k ≤ i → i < ell →
      squareNegativeLogAt (squarePrincipalMinor A hmn) i ≤
        squareNegativeLogAt (squarePrincipalMinor A hmn) (ell - 1) := by
    intro i _ hi
    have hiM : i < m := by omega
    have hLastM : ell - 1 < m := by omega
    simp only [squareNegativeLogAt, dif_pos hiM, dif_pos hLastM]
    apply neg_le_neg
    exact Real.log_le_log (hMinorPos ⟨ell - 1, hLastM⟩ (by change ell - 1 < ell; omega))
      (orderedSquareSingularValues_antitone _
        (show (⟨i, hiM⟩ : Fin m) ≤ ⟨ell - 1, hLastM⟩ from by change i ≤ ell - 1; omega))
  have hSum := prefix_sum_le_shifted_head_and_tail (show k ≤ ell from hPrefix)
    (squareNegativeLogAt (squarePrincipalMinor A hmn)) (squareNegativeLogAt A)
    (squareNegativeLogAt (squarePrincipalMinor A hmn) (ell - 1)) hHead hTail
  have hInterval : (∑ i ∈ Finset.range k, squareNegativeLogAt A (i + r)) =
      ∑ j ∈ Finset.Ico r m, squareNegativeLogAt A j := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [k, Nat.add_comm]
  rw [hInterval] at hSum
  exact div_le_div_of_nonneg_right hSum (Nat.cast_nonneg n)

end CircularLaw
