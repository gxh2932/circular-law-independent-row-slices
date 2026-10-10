import CircularLaw.NormHeavyRectangular
import CircularLaw.RowSliceNormEvents

/-!
# The actual row-slice heavy event and its polynomial failure bound

The checked degree/discrepancy event supplies the full rectangular
heavy estimate simultaneously for all real vectors of squared mass
at most one. This uses `N=9*d` and density multiplier `C=1/9`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rowSliceHeavyConstant (beta : ℝ) : ℝ :=
  3 * normHeavySquareConstant (1 / 9) (Real.exp 2) (2 * (beta + 4))

def RowSliceHeavyBound {m n d : ℕ} (beta : ℝ) (rows : Fin m → RowSlice n d) : Prop :=
  ∀ x : Fin m → ℝ, ∀ y : Fin n → ℝ, (∑ i, (x i) ^ 2) ≤ 1 → (∑ j, (y j) ^ 2) ≤ 1 →
    |weightedSliceMatrixSum (heavyMatrixWeights (fun i j => x i * y j)
      (Real.sqrt (9 * (d : ℝ)) / n)) rows| ≤ rowSliceHeavyConstant beta * Real.sqrt d

theorem rowSliceDegreeDiscrepancy_heavy_bound {m n d : ℕ} (hn : 0 < n) (hmn : m ≤ n)
    (hd : 0 < d) {beta : ℝ} (hBeta : 0 ≤ beta) (rows : Fin m → RowSlice n d)
    (hGood : RowSliceDegreeDiscrepancy beta rows) : RowSliceHeavyBound beta rows := by
  intro x y hx hy
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hN : 0 < 9 * (d : ℝ) := by positivity
  have hCap : 1 < Real.exp (2 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hKappa : 0 ≤ 2 * (beta + 4) := by linarith
  have hDensity : ((1 / 9 : ℝ) * (9 * (d : ℝ))) / n = (d : ℝ) / n := by ring
  have hDP : MatrixDiscrepancy (((1 / 9 : ℝ) * (9 * (d : ℝ))) / n)
      (Real.exp 2) (2 * (beta + 4)) (rectangularSliceMatrixReal rows) := by
    rw [hDensity]
    exact hGood.1
  have hHeavy := normHeavy_rectangular_bilinear_bound hn hmn (by norm_num : (0 : ℝ) < 1 / 9)
    hN hCap hKappa (rectangularSliceMatrixReal rows) (rectangularSliceMatrixReal_nonneg rows)
    hGood.2 hDP x y hx hy
  have hRoot : Real.sqrt (9 * (d : ℝ)) = 3 * Real.sqrt d := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
    norm_num
  rw [weightedSliceMatrixSum_eq_real_bilinear]
  calc
    _ ≤ normHeavySquareConstant (1 / 9) (Real.exp 2) (2 * (beta + 4)) * Real.sqrt (9 * (d : ℝ)) := hHeavy
    _ = _ := by rw [hRoot]; unfold rowSliceHeavyConstant; ring

theorem rowSliceHeavyBound_failure_probability {m n d : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {beta : ℝ} (hBeta : 0 ≤ beta) :
    uniformProbability (fun rows : Fin m → RowSlice n d => ¬RowSliceHeavyBound beta rows) ≤
      (n : ℝ) ^ (-beta) + (n : ℝ) * Real.exp (-9 * d) := by
  have hCover : ∀ rows : Fin m → RowSlice n d,
      ¬RowSliceHeavyBound beta rows → ¬RowSliceDegreeDiscrepancy beta rows := by
    intro rows hFail hGood
    exact hFail (rowSliceDegreeDiscrepancy_heavy_bound hn hmn hd hBeta rows hGood)
  exact (uniformProbability_mono hCover).trans
    (rowSliceDegreeDiscrepancy_failure_probability hm hn hmn hd hdn hBeta)

theorem rowSliceHeavyBound_failure_polynomial {m n d : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {A : ℝ} (hA : 0 ≤ A) (hDegree : (A + 2) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) :
    uniformProbability (fun rows : Fin m → RowSlice n d => ¬RowSliceHeavyBound (A + 1) rows) ≤
      (n : ℝ) ^ (-A) := by
  have hnPos : 0 < n := by omega
  have hBeta : 0 ≤ A + 1 := by linarith
  have hCover : ∀ rows : Fin m → RowSlice n d,
      ¬RowSliceHeavyBound (A + 1) rows → ¬RowSliceDegreeDiscrepancy (A + 1) rows := by
    intro rows hFail hGood
    exact hFail (rowSliceDegreeDiscrepancy_heavy_bound hnPos hmn hd hBeta rows hGood)
  exact (uniformProbability_mono hCover).trans
    (rowSliceDegreeDiscrepancy_failure_polynomial hm hn hmn hd hdn hA hDegree)

end CircularLaw
