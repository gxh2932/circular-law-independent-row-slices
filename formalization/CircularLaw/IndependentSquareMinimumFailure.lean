import CircularLaw.HermitizationPrefixComparison

/-!
# Transport of the actual two smallest-singular-value failure events

The square coupling has the exact manuscript marginals. A union bound
transports their individual failure estimates to the joint event needed
for removal of regularization. The marginal estimates are explicit
premises, not new mathematical axioms or claimed imported proofs.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem independent_square_slice_marginal (n d : ℕ) :
    (independentSquareComparisonLaw n d).map Prod.fst = rowSliceMatrixLaw n d := by
  rw [independentSquareComparisonLaw, Measure.map_fst_prod]
  simp

theorem independent_square_bernoulli_marginal {n d : ℕ} (hdn : d ≤ n) :
    (independentSquareComparisonLaw n d).map Prod.snd = sparseBernoulliMatrixLaw n d := by
  haveI := rowSliceMatrixLaw_probability hdn
  rw [independentSquareComparisonLaw, Measure.map_snd_prod]
  simp

theorem square_singular_minimum_lower_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (τ : ℝ) :
    (∀ j, τ ≤ orderedSquareSingularValues A j) ↔
      τ ≤ orderedSquareSingularValues A ⟨n - 1, by omega⟩ := by
  constructor
  · intro h
    exact h _
  · intro h j
    have hLast : j ≤ (⟨n - 1, by omega⟩ : Fin n) := by
      change j.val ≤ n - 1
      exact Nat.le_pred_of_lt j.isLt
    exact h.trans (orderedSquareSingularValues_antitone A hLast)

theorem independent_square_minimum_failure_probability_le {n d : ℕ} (hdn : d ≤ n)
    (ζ : ℂ) (τ : ℝ) :
    (independentSquareComparisonLaw n d).real (independentSquareMinimumFailure n d ζ τ) ≤
      (rowSliceMatrixLaw n d).real {rows | ¬∀ j, τ ≤ orderedSquareSingularValues (fullShiftedSliceMatrix ζ rows) j} +
      (sparseBernoulliMatrixLaw n d).real
        {x | ¬∀ j, τ ≤ orderedSquareSingularValues (bernoulliSquareMatrix x - ζ • 1) j} := by
  haveI := rowSliceMatrixLaw_probability hdn
  have hSlice := finite_law_event_real measurable_fst (independent_square_slice_marginal n d)
    (fun rows => ¬∀ j, τ ≤ orderedSquareSingularValues (fullShiftedSliceMatrix ζ rows) j)
  have hBernoulli := finite_law_event_real measurable_snd (independent_square_bernoulli_marginal hdn)
    (fun x => ¬∀ j, τ ≤ orderedSquareSingularValues (bernoulliSquareMatrix x - ζ • 1) j)
  have hUnion : independentSquareMinimumFailure n d ζ τ =
      {samples | ¬∀ j, τ ≤ orderedSquareSingularValues (fullShiftedSliceMatrix ζ samples.1) j} ∪
      {samples | ¬∀ j, τ ≤ orderedSquareSingularValues (bernoulliSquareMatrix samples.2 - ζ • 1) j} := by
    ext samples
    simp only [independentSquareMinimumFailure, Set.mem_setOf_eq, Set.mem_union, not_and_or]
  rw [hUnion]
  exact (measureReal_union_le _ _).trans_eq (congrArg₂ (· + ·) hSlice hBernoulli)

theorem independent_square_minimum_failure_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (ζ : ℕ → ℂ) (τ : ℕ → ℝ)
    (hSlice : Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | ¬∀ j, τ n ≤ orderedSquareSingularValues (fullShiftedSliceMatrix (ζ n) rows) j}) atTop (𝓝 0))
    (hBernoulli : Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      {x | ¬∀ j, τ n ≤ orderedSquareSingularValues (bernoulliSquareMatrix x - ζ n • 1) j}) atTop (𝓝 0)) :
    Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareMinimumFailure n (d n) (ζ n) (τ n))) atTop (𝓝 0) := by
  have hUpper := hSlice.add hBernoulli
  simp only [add_zero] at hUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  exact independent_square_minimum_failure_probability_le hd.2 (ζ n) (τ n)

end CircularLaw
