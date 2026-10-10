import CircularLaw.BernoulliPrefixFreshLaw
import CircularLaw.SourceExposureExpansionSeed
import CircularLaw.NormalizedSourceExposure

/-!
# Conditional normalized insertion failure with an adapted retained rank

The retained rank, deterministic shift vector, and graph conditions may
depend on the currently exposed prefix. The deterministic barrier seed
supplies the actual leading-kernel expansion budget, and independence of
the next row or column turns the checked fixed-matrix estimate into a conditional
probability bound in the current prefix sigma-algebra.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal InnerProductSpace

namespace CircularLaw

structure SourceNormalizedInsertionConditions {N r a m : ℕ}
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (β d ε : ℝ) : Prop where
  nextRank : r < m
  oldProduct : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z) h
  barrier : (N - m) / 8 < m - r
  fraction : ((N - r : ℕ) : ℝ) / N ≤ ε
  columns : MatrixColumnDegreeBudget A 8 N d
  unique : MatrixUniqueExpansionBudget A e β N d (sourceExposureExpansionSeed N m)
    (sourceGraphTerminalScale N d)
  heavy : MatrixHeavyRowBudget A β N d

theorem bernoulli_row_normalized_failure_le_of_exposure_conditions {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ) (h : r ≤ a)
    {β d ε : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbient : m ≤ N) (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hε : ε ≤ Real.exp (-4)) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hInputs : SourceNormalizedInsertionConditions (N := N) A e z h β d ε)
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      degreeNormalizedRowStepFailure d N
        (sourceNormalizedBernoulliLogIncrement 8 β N d (N - r : ℕ))
        (diagonalEmbeddedShift A e z) h (bernoulliCubeVector x + w)} ≤
      normalizedSourceProjectionFailureBound ε d := by
  exact bernoulli_row_degree_normalized_failure_of_source_threshold
    p hp hpPos hHalf A e z h hInputs.nextRank hInputs.oldProduct (by norm_num) hβ hβOne
    hd hDegree hAmbient hAmbientLower hInputs.barrier hInputs.fraction hε hz hzUpper
    hInputs.columns (source_exposure_unique_budget_for_leading_kernel A e z h
      hInputs.oldProduct.ne' hInputs.barrier hInputs.unique) hInputs.heavy w

theorem bernoulli_adjoint_column_normalized_failure_le_of_exposure_conditions
    {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hRow : r ≤ m) (hNextRank : r + 1 ≤ m)
    {β d ε : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbient : m ≤ N) (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hε : ε ≤ Real.exp (-4)) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hInputs : SourceNormalizedInsertionConditions (N := N) A e z h β d ε)
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      degreeNormalizedColumnStepFailure d N
        (sourceNormalizedBernoulliLogIncrement 8 β N d (N - r : ℕ))
        (diagonalEmbeddedShift A e z).conjTranspose hRow hNextRank (bernoulliCubeVector x + w)} ≤
      normalizedSourceProjectionFailureBound ε d := by
  exact bernoulli_adjoint_column_degree_normalized_failure_of_source_threshold
    p hp hpPos hHalf A e z h hRow hNextRank hInputs.oldProduct (by norm_num) hβ hβOne
    hd hDegree hAmbient hAmbientLower hInputs.barrier hInputs.fraction hε hz hzUpper
    hInputs.columns (source_exposure_unique_budget_for_leading_kernel A e z h
      hInputs.oldProduct.ne' hInputs.barrier hInputs.unique) hInputs.heavy w

def sourcePrefixRowInsertionFailure {N a m : ℕ}
    (e : Fin a ↪ Fin m) (z : ℂ) (β d : ℝ)
    (r : (Fin a × Fin m → Bool) → ℕ) (hr : ∀ u, r u ≤ a)
    (w : (Fin a × Fin m → Bool) → EuclideanSpace ℂ (Fin m))
    (u : Fin a × Fin m → Bool) (y : Fin m → Bool) : Prop :=
  degreeNormalizedRowStepFailure d N
    (sourceNormalizedBernoulliLogIncrement 8 β N d (N - r u : ℕ))
    (diagonalEmbeddedShift (bernoulliRectangularMatrix u) e z) (hr u)
    (bernoulliCubeVector y + w u)

theorem bernoulli_prefix_row_conditional_normalized_failure {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (hNext : a + 1 ≤ N)
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (e : Fin a ↪ Fin m) (z : ℂ) {β d ε : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hε : ε ≤ Real.exp (-4)) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (r : (Fin a × Fin m → Bool) → ℕ) (hr : ∀ u, r u ≤ a)
    (w : (Fin a × Fin m → Bool) → EuclideanSpace ℂ (Fin m))
    (G : (Fin a × Fin m → Bool) → Prop)
    (hInputs : ∀ u, G u → SourceNormalizedInsertionConditions (N := N)
      (bernoulliRectangularMatrix u) e z (hr u) β d ε) :
    ∀ᵐ x ∂bernoulliSquareMatrixLaw N p hp,
      G (fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij)) →
        ((bernoulliSquareMatrixLaw N p hp)[
          ({x | sourcePrefixRowInsertionFailure (N := N) e z β d r hr w
            (fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij))
            (fun j => x (bernoulliFreshRowEntryEmbedding hNext hm j))}).indicator
              (fun _ => (1 : ℝ)) |
            MeasurableSpace.comap (fun x : BernoulliSquareSample N =>
              fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij)) inferInstance]) x ≤
          normalizedSourceProjectionFailureBound ε d := by
  apply bernoulli_disjoint_fresh_conditional_probability_le_on_past p hp
    (bernoulliPrefixEntryEmbedding ha hm) (bernoulliFreshRowEntryEmbedding hNext hm)
    (bernoulli_prefix_fresh_row_disjoint ha hm hNext)
    (sourcePrefixRowInsertionFailure (N := N) e z β d r hr w) G
  intro u hGood
  exact bernoulli_row_normalized_failure_le_of_exposure_conditions
    p hp hpPos hHalf (bernoulliRectangularMatrix u) e z (hr u) hβ hβOne hd hDegree
    hm hAmbientLower hε hz hzUpper (hInputs u hGood) (w u)

def sourcePrefixAdjointColumnInsertionFailure {N a m : ℕ}
    (e : Fin a ↪ Fin m) (z : ℂ) (β d : ℝ)
    (r : (Fin m × Fin a → Bool) → ℕ) (hrm : ∀ u, r u ≤ m)
    (w : (Fin m × Fin a → Bool) → EuclideanSpace ℂ (Fin m))
    (u : Fin m × Fin a → Bool) (y : Fin m → Bool) : Prop :=
  if hNextRank : r u + 1 ≤ m then
    degreeNormalizedColumnStepFailure d N
      (sourceNormalizedBernoulliLogIncrement 8 β N d (N - r u : ℕ))
      (diagonalEmbeddedShift (bernoulliRectangularMatrix u).conjTranspose e z).conjTranspose
        (hrm u) hNextRank (bernoulliCubeVector y + w u)
  else False

theorem bernoulli_prefix_adjoint_column_conditional_normalized_failure {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (hNext : a + 1 ≤ N)
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (e : Fin a ↪ Fin m) (z : ℂ) {β d ε : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hε : ε ≤ Real.exp (-4)) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (r : (Fin m × Fin a → Bool) → ℕ) (hr : ∀ u, r u ≤ a) (hrm : ∀ u, r u ≤ m)
    (w : (Fin m × Fin a → Bool) → EuclideanSpace ℂ (Fin m))
    (G : (Fin m × Fin a → Bool) → Prop)
    (hInputs : ∀ u, G u → SourceNormalizedInsertionConditions (N := N)
      (bernoulliRectangularMatrix u).conjTranspose e z (hr u) β d ε) :
    ∀ᵐ x ∂bernoulliSquareMatrixLaw N p hp,
      G (fun ij => x (bernoulliPrefixEntryEmbedding hm ha ij)) →
        ((bernoulliSquareMatrixLaw N p hp)[
          ({x | sourcePrefixAdjointColumnInsertionFailure (N := N) e z β d r hrm w
            (fun ij => x (bernoulliPrefixEntryEmbedding hm ha ij))
            (fun j => x (bernoulliFreshColumnEntryEmbedding hm hNext j))}).indicator
              (fun _ => (1 : ℝ)) |
            MeasurableSpace.comap (fun x : BernoulliSquareSample N =>
              fun ij => x (bernoulliPrefixEntryEmbedding hm ha ij)) inferInstance]) x ≤
          normalizedSourceProjectionFailureBound ε d := by
  apply bernoulli_disjoint_fresh_conditional_probability_le_on_past p hp
    (bernoulliPrefixEntryEmbedding hm ha) (bernoulliFreshColumnEntryEmbedding hm hNext)
    (bernoulli_prefix_fresh_column_disjoint hm ha hNext)
    (sourcePrefixAdjointColumnInsertionFailure (N := N) e z β d r hrm w) G
  intro u hGood
  have hLocal := hInputs u hGood
  have hNextRank : r u + 1 ≤ m := Nat.succ_le_of_lt hLocal.nextRank
  simpa only [sourcePrefixAdjointColumnInsertionFailure, dif_pos hNextRank] using
    bernoulli_adjoint_column_normalized_failure_le_of_exposure_conditions
      p hp hpPos hHalf (bernoulliRectangularMatrix u).conjTranspose e z (hr u) (hrm u)
      hNextRank hβ hβOne hd hDegree hm hAmbientLower hε hz hzUpper hLocal (w u)

end CircularLaw
