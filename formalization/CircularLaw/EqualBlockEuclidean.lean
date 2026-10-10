import CircularLaw.EqualBlockSelectedNorm
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Euclidean fixed-vector equal-block estimate

These estimates act on literal shifted row sums of `y + c*1`. Their
events retain the witness-row lower bound, and both estimates follow from
the actual uniform row-slice product through its exposed fibers.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def shiftedRowsL2Norm {n d : ℕ} {ι : Type*} [Fintype ι]
    (rows : ι → RowSlice n d) (y : Fin n → ℂ) (c ζ : ℂ) (index : ι → Fin n) : ℝ :=
  ‖(WithLp.toLp 2 (fun i => shiftedRowAction (rows i) y c ζ (index i)) : EuclideanSpace ℂ ι)‖

theorem shiftedRowsL2Norm_sq {n d : ℕ} {ι : Type*} [Fintype ι]
    (rows : ι → RowSlice n d) (y : Fin n → ℂ) (c ζ : ℂ) (index : ι → Fin n) :
    shiftedRowsL2Norm rows y c ζ index ^ 2 =
      ∑ i, ‖shiftedRowAction (rows i) y c ζ (index i)‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq _

theorem shiftedRowsL2Norm_small_sq {n d : ℕ} {ι : Type*} [Fintype ι]
    (rows : ι → RowSlice n d) (y : Fin n → ℂ) (c ζ : ℂ) (index : ι → Fin n)
    {r B : ℝ} (hB : 0 ≤ B)
    (hNorm : shiftedRowsL2Norm rows y c ζ index ≤ r * Real.sqrt (B / 8)) :
    (∑ i, ‖shiftedRowAction (rows i) y c ζ (index i)‖ ^ 2) ≤ r ^ 2 * B / 8 := by
  have hSquare := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  change shiftedRowsL2Norm rows y c ζ index ^ 2 ≤ (r * Real.sqrt (B / 8)) ^ 2 at hSquare
  rw [shiftedRowsL2Norm_sq, mul_pow, Real.sq_sqrt (div_nonneg hB (by norm_num))] at hSquare
  simpa only [mul_div_assoc] using hSquare

theorem equal_blocks_selected_euclidean_half {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hdn : d ≤ n) (L R : κ → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (L q ∪ R q) (L p ∪ R p)))
    (hHalves : ∀ q, Disjoint (L q) (R q)) (hSize : ∀ q, (L q).card = (R q).card)
    (hLeft : ∀ q, (L q).Nonempty) (y : Fin n → ℂ) {r a B : ℝ}
    (hr : 0 < r) (ha : 1 ≤ a) (hB : 0 ≤ B)
    (hSep : ∀ q l, l ∈ L q → ∀ j, j ∈ R q → 2 * r < dist (y l) (y j))
    (c ζ : ℂ) (index : ι → Fin n) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      shiftedRowsL2Norm rows y c ζ index ≤ r * Real.sqrt (B / 8) ∧
        B ≤ (largeWitnessRows (matrixSingletonCounts (fun q => L q ∪ R q) rows) a).card) ≤
      Real.exp (-witnessHalfRate * B) := by
  apply (uniformProbability_mono ?_).trans
    (equal_block_selected_norm_half hdn (fun q => L q ∪ R q) hDis y hr ha
      (fun q z => equal_halves_small_ball (L q) (R q) (hHalves q) (hSize q) (hLeft q) y (hSep q) z)
      c ζ index)
  intro rows hEvent
  exact ⟨shiftedRowsL2Norm_small_sq rows y c ζ index hB hEvent.1, hEvent.2⟩

theorem equal_blocks_selected_euclidean_log {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hdn : d ≤ n) (L R : κ → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (L q ∪ R q) (L p ∪ R p)))
    (hHalves : ∀ q, Disjoint (L q) (R q)) (hSize : ∀ q, (L q).card = (R q).card)
    (hLeft : ∀ q, (L q).Nonempty) (y : Fin n → ℂ) {r a B p : ℝ}
    (hr : 0 < r) (ha : 1 ≤ a) (hB : 0 ≤ B) (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    (hSep : ∀ q l, l ∈ L q → ∀ j, j ∈ R q → 2 * r < dist (y l) (y j))
    (hEsseen : (2 * (24 * Real.exp 1 / Real.pi)) / Real.sqrt a ≤ p)
    (c ζ : ℂ) (index : ι → Fin n) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      shiftedRowsL2Norm rows y c ζ index ≤ r * Real.sqrt (B / 8) ∧
        B ≤ (largeWitnessRows (matrixSingletonCounts (fun q => L q ∪ R q) rows) a).card) ≤
      Real.exp (-witnessLogRate * B * Real.log (1 / p)) := by
  apply (uniformProbability_mono ?_).trans
    (equal_block_selected_norm_log hdn (fun q => L q ∪ R q) hDis y hr ha hp hpHalf
      (fun q z => equal_halves_small_ball (L q) (R q) (hHalves q) (hSize q) (hLeft q) y (hSep q) z)
      hEsseen c ζ index)
  intro rows hEvent
  exact ⟨shiftedRowsL2Norm_small_sq rows y c ζ index hB hEvent.1, hEvent.2⟩

end CircularLaw
