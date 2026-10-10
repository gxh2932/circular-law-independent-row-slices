import CircularLaw.IndependentSquarePrefixLaw
import CircularLaw.SquareSliceSingularValues
import CircularLaw.RectangularSingularInterlacing

/-!
# Row replacement for the actual shifted square matrix prefixes

Selecting rows from each square sample preserves the shift on its
original diagonal column. The product square law has exactly the paired
row law needed by the proved replacement estimate.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

def squareComparisonRowShift {k n : ℕ} (f : Fin k ↪ Fin n) (ζ : ℂ) :
    Fin k → EuclideanSpace ℂ (Fin n) :=
  fun i => EuclideanSpace.single (f i) (-ζ)

theorem squareComparisonRowShift_norm {k n : ℕ} (f : Fin k ↪ Fin n) (ζ : ℂ)
    (i : Fin k) : ‖squareComparisonRowShift f ζ i‖ = ‖ζ‖ := by
  simp [squareComparisonRowShift, EuclideanSpace.norm_single]

theorem squareComparisonRowShift_bound {k n : ℕ} (hk : 0 < k)
    (f : Fin k ↪ Fin n) (ζ : ℂ) : rowShiftNormBound (squareComparisonRowShift f ζ) = ‖ζ‖ := by
  obtain ⟨i, hi⟩ := rowShiftNormBound_attained hk (squareComparisonRowShift f ζ)
  rw [hi, squareComparisonRowShift_norm]

theorem square_prefix_hybrid_full {k n d : ℕ} (f : Fin k ↪ Fin n) (ζ : ℂ)
    (samples : RowSliceMatrix n d × BernoulliSquareSample n) :
    rowHybridMatrix (squareComparisonRowShift f ζ) k (squareComparisonPrefixPairs f samples) =
      matrixRowRestriction (fullShiftedSliceMatrix ζ samples.1) f := by
  rw [rowHybridMatrix_full]
  ext i j
  simp [squareComparisonRowShift, squareComparisonPrefixPairs, rowSliceEuclideanRow,
    matrixRowRestriction, fullShiftedSliceMatrix_apply, EuclideanSpace.single_apply]
  split_ifs <;> simp_all [sub_eq_add_neg]

theorem square_prefix_hybrid_zero {k n d : ℕ} (f : Fin k ↪ Fin n) (ζ : ℂ)
    (samples : RowSliceMatrix n d × BernoulliSquareSample n) :
    rowHybridMatrix (squareComparisonRowShift f ζ) 0 (squareComparisonPrefixPairs f samples) =
      matrixRowRestriction (bernoulliSquareMatrix samples.2 - ζ • 1) f := by
  rw [rowHybridMatrix_zero]
  ext i j
  simp [squareComparisonRowShift, squareComparisonPrefixPairs, bernoulliCubeVector,
    matrixRowRestriction, bernoulliSquareMatrix, Matrix.one_apply, EuclideanSpace.single_apply]
  split_ifs <;> simp_all [sub_eq_add_neg]

theorem independent_square_prefix_expected_comparison {k n d : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) (hk : 1 ≤ k) (hkn : k < n)
    (f : Fin k ↪ Fin n) (ζ : ℂ) {η : ℝ} (hη : 0 < η)
    (hQ : 1 ≤ rowLogComparisonQ n d (n - k)) :
    (1 / (n : ℝ)) *
      (∫ samples, |regularizedRowPotential
        (matrixRowRestriction (fullShiftedSliceMatrix ζ samples.1) f) η -
        regularizedRowPotential
          (matrixRowRestriction (bernoulliSquareMatrix samples.2 - ζ • 1) f) η|
        ∂independentSquareComparisonLaw n d) ≤
      rowReplacementErrorBound n d k η ‖ζ‖ := by
  have hLaw := independent_square_prefix_pairs_law (show 0 < n by omega) hdn f
  have hIntegral := finite_law_integral_comp (measurable_of_countable (squareComparisonPrefixPairs f))
    hLaw (fun rows => |regularizedRowPotential (rowHybridMatrix (squareComparisonRowShift f ζ) k rows) η -
      regularizedRowPotential (rowHybridMatrix (squareComparisonRowShift f ζ) 0 rows) η|)
  simp only [square_prefix_hybrid_full, square_prefix_hybrid_zero] at hIntegral
  rw [hIntegral]
  have hBound := row_replacement_finite_product hd hdn hk hkn hη (squareComparisonRowShift f ζ) hQ
  rwa [squareComparisonRowShift_bound (show 0 < k by omega)] at hBound

theorem independent_square_prefix_probability_comparison {k n d : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) (hk : 1 ≤ k) (hkn : k < n)
    (f : Fin k ↪ Fin n) (ζ : ℂ) {η : ℝ} (hη : 0 < η)
    (hQ : 1 ≤ rowLogComparisonQ n d (n - k)) {ε : ℝ} (hε : 0 < ε) :
    (independentSquareComparisonLaw n d).real
      {samples | ε < |regularizedRowPotential
        (matrixRowRestriction (fullShiftedSliceMatrix ζ samples.1) f) η -
        regularizedRowPotential
          (matrixRowRestriction (bernoulliSquareMatrix samples.2 - ζ • 1) f) η| / n} ≤
      rowReplacementErrorBound n d k η ‖ζ‖ / ε := by
  have hLaw := independent_square_prefix_pairs_law (show 0 < n by omega) hdn f
  have hEvent := finite_law_event_real (measurable_of_countable (squareComparisonPrefixPairs f)) hLaw
    (fun rows => ε < |regularizedRowPotential (rowHybridMatrix (squareComparisonRowShift f ζ) k rows) η -
      regularizedRowPotential (rowHybridMatrix (squareComparisonRowShift f ζ) 0 rows) η| / n)
  simp only [square_prefix_hybrid_full, square_prefix_hybrid_zero] at hEvent
  rw [hEvent]
  have hBound := row_replacement_finite_probability_bound hd hdn hk hkn hη
    (squareComparisonRowShift f ζ) hQ hε
  rwa [squareComparisonRowShift_bound (show 0 < k by omega)] at hBound

end CircularLaw
