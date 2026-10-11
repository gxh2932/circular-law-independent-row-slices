import CircularLaw.RowGramInverse
import CircularLaw.HermitianInverseTrace

/-!
# Negative second moment for the actual retained shifted matrix

The row Gram matrix is the literal product `H H*`. Its ordered nonnegative
eigenvalue square roots define the rectangular matrix's singular values.
The checked inverse trace identities give the negative second-moment
formula and the bound used after row deletion.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace ComplexOrder

namespace CircularLaw

theorem retainedRowGram_eq_matrix_product {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) :
    Matrix.gram ℂ (retainedConjugateRow H ζ rows) =
      retainedShiftedMatrix H ζ rows * (retainedShiftedMatrix H ζ rows).conjTranspose := by
  ext i j
  rw [Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply]
  change (∑ k, star ((retainedShiftedMatrix H ζ rows) j k) *
    star (star ((retainedShiftedMatrix H ζ rows) i k))) =
      ∑ k, (retainedShiftedMatrix H ζ rows) i k * star ((retainedShiftedMatrix H ζ rows) j k)
  simp only [star_star, mul_comm]

def retainedRowSingularValues {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) : Fin (Fintype.card H) → ℝ :=
  fun j => Real.sqrt ((Matrix.isHermitian_gram ℂ (retainedConjugateRow H ζ rows)).eigenvalues₀ j)

theorem retainedRowGram_ordered_eigenvalue_nonneg {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (j : Fin (Fintype.card H)) :
    0 ≤ (Matrix.isHermitian_gram ℂ (retainedConjugateRow H ζ rows)).eigenvalues₀ j := by
  let e : Fin (Fintype.card H) ≃ H := Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := (Matrix.posSemidef_gram ℂ (retainedConjugateRow H ζ rows)).eigenvalues_nonneg (e j)
  change 0 ≤ (Matrix.isHermitian_gram ℂ (retainedConjugateRow H ζ rows)).eigenvalues₀
    (e.symm (e j)) at h
  simpa only [Equiv.symm_apply_apply] using h

theorem retainedRowSingularValues_nonneg {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (j : Fin (Fintype.card H)) :
    0 ≤ retainedRowSingularValues H ζ rows j := Real.sqrt_nonneg _

theorem retainedRowSingularValues_antitone {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) : Antitone (retainedRowSingularValues H ζ rows) := by
  intro i j hij
  exact Real.sqrt_le_sqrt
    ((Matrix.isHermitian_gram ℂ (retainedConjugateRow H ζ rows)).eigenvalues₀_antitone hij)

theorem retainedRowSingularValues_sq {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (j : Fin (Fintype.card H)) :
    retainedRowSingularValues H ζ rows j ^ 2 =
      (Matrix.isHermitian_gram ℂ (retainedConjugateRow H ζ rows)).eigenvalues₀ j :=
  Real.sq_sqrt (retainedRowGram_ordered_eigenvalue_nonneg H ζ rows j)

theorem retainedRowSpan_erase_generators {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : H) :
    Set.range (retainedConjugateRow (H.erase i.val) ζ rows) =
      (retainedConjugateRow H ζ rows) '' (Set.univ \ {i}) := by
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨hji, hjH⟩ := Finset.mem_erase.mp j.property
    refine ⟨⟨j.val, hjH⟩, ?_, rfl⟩
    simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    exact fun h => hji (congrArg Subtype.val h)
  · rintro ⟨j, hj, rfl⟩
    have hji : j ≠ i := by simpa using hj
    exact ⟨⟨j.val, Finset.mem_erase.mpr ⟨fun h => hji (Subtype.ext h), j.property⟩⟩, rfl⟩

theorem leaveOneOutRowDistance_pos_of_linearIndependent {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (hLI : LinearIndependent ℂ (retainedConjugateRow H ζ rows))
    {i : Fin n} (hi : i ∈ H) : 0 < leaveOneOutRowDistance H ζ rows i := by
  have hNot := linearIndependent_iff_notMem_span.mp hLI ⟨i, hi⟩
  rw [← retainedRowSpan_erase_generators H ζ rows ⟨i, hi⟩] at hNot
  have hClosed := (retainedRowSpan (H.erase i) ζ rows).closed_of_finiteDimensional
  exact (hClosed.notMem_iff_infDist_pos
    ⟨0, (retainedRowSpan (H.erase i) ζ rows).zero_mem⟩).mp hNot

theorem retainedRowGram_posDef_of_distances {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d)
    (hDistance : ∀ i ∈ H, 0 < leaveOneOutRowDistance H ζ rows i) :
    (Matrix.gram ℂ (retainedConjugateRow H ζ rows)).PosDef := by
  apply Matrix.posDef_gram_of_linearIndependent
  apply linearIndependent_iff_notMem_span.mpr
  intro i hi
  have hGenerators : (retainedConjugateRow H ζ rows) '' (Set.univ \ {i}) ⊆
      Set.range (retainedConjugateRow (H.erase i.val) ζ rows) := by
    rintro v ⟨j, hj, rfl⟩
    have hji : j ≠ i := by simpa using hj
    exact ⟨⟨j.val, Finset.mem_erase.mpr ⟨fun h => hji (Subtype.ext h), j.property⟩⟩, rfl⟩
  have hZero := Metric.infDist_zero_of_mem ((Submodule.span_mono hGenerators) hi)
  change leaveOneOutRowDistance H ζ rows i.val = 0 at hZero
  exact (hDistance i.val i.property).ne' hZero

theorem retainedRowSingularValues_pos_of_distances {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d)
    (hDistance : ∀ i ∈ H, 0 < leaveOneOutRowDistance H ζ rows i)
    (j : Fin (Fintype.card H)) : 0 < retainedRowSingularValues H ζ rows j := by
  let e : Fin (Fintype.card H) ≃ H := Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := (retainedRowGram_posDef_of_distances H ζ rows hDistance).eigenvalues_pos (e j)
  change 0 < (Matrix.isHermitian_gram ℂ (retainedConjugateRow H ζ rows)).eigenvalues₀
    (e.symm (e j)) at h
  exact Real.sqrt_pos.mpr (by simpa only [Equiv.symm_apply_apply] using h)

theorem retained_row_negative_second_moment {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d)
    (hDistance : ∀ i ∈ H, 0 < leaveOneOutRowDistance H ζ rows i) :
    (∑ j : Fin (Fintype.card H), (retainedRowSingularValues H ζ rows j ^ 2)⁻¹) =
      ∑ i ∈ H, (leaveOneOutRowDistance H ζ rows i ^ 2)⁻¹ := by
  let hGram := Matrix.isHermitian_gram ℂ (retainedConjugateRow H ζ rows)
  let e : Fin (Fintype.card H) ≃ H := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hPos := retainedRowGram_posDef_of_distances H ζ rows hDistance
  have hEigen (i : H) : hGram.eigenvalues i ≠ 0 := (hPos.eigenvalues_pos i).ne'
  calc
    _ = ∑ j : Fin (Fintype.card H), (hGram.eigenvalues₀ j)⁻¹ := by
      simp only [retainedRowSingularValues_sq]
    _ = ∑ i : H, (hGram.eigenvalues i)⁻¹ := by
      exact (e.symm.sum_comp (fun j => (hGram.eigenvalues₀ j)⁻¹)).symm
    _ = ((Matrix.gram ℂ (retainedConjugateRow H ζ rows))⁻¹).trace.re :=
      (hermitian_inverse_trace_real hGram hEigen).symm
    _ = _ := retainedRowGram_inverse_trace H ζ rows hDistance

theorem surviving_rows_negative_second_moment_bound {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {r : ℝ} (hr : 0 < r)
    (hDistance : ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i) :
    (∑ j : Fin (Fintype.card H), (retainedRowSingularValues H ζ rows j ^ 2)⁻¹) ≤ H.card / r ^ 2 := by
  rw [retained_row_negative_second_moment H ζ rows (fun i hi => hr.trans_le (hDistance i hi))]
  exact surviving_rows_distance_energy H ζ rows hr hDistance

theorem retained_row_negative_second_moment_full_rank {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (hLI : LinearIndependent ℂ (retainedConjugateRow H ζ rows)) :
    (∑ j : Fin (Fintype.card H), (retainedRowSingularValues H ζ rows j ^ 2)⁻¹) =
      ∑ i ∈ H, (leaveOneOutRowDistance H ζ rows i ^ 2)⁻¹ :=
  retained_row_negative_second_moment H ζ rows
    (fun _ hi => leaveOneOutRowDistance_pos_of_linearIndependent H ζ rows hLI hi)

def SurvivingNegativeSecondMomentEvent {n d : ℕ} (T : Finset (Fin n)) (ζ : ℂ) (r : ℝ)
    (rows : RowSliceMatrix n d) : Prop :=
  ∃ H : Finset (Fin n), H ⊆ T ∧ H.card = T.card - rowDeletionThreshold n d ∧
    (∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i) ∧
    LinearIndependent ℂ (retainedConjugateRow H ζ rows) ∧
    (∑ j : Fin (Fintype.card H), (retainedRowSingularValues H ζ rows j ^ 2)⁻¹) ≤ H.card / r ^ 2

theorem survivingRowDistanceEvent_implies_negativeSecondMoment {n d : ℕ}
    (T : Finset (Fin n)) (ζ : ℂ) {r : ℝ} (hr : 0 < r) (rows : RowSliceMatrix n d)
    (h : SurvivingRowDistanceEvent T ζ r rows) : SurvivingNegativeSecondMomentEvent T ζ r rows := by
  obtain ⟨H, hHT, hCard, hDist, hLI, _⟩ := h
  exact ⟨H, hHT, hCard, hDist, hLI, surviving_rows_negative_second_moment_bound H ζ rows hr hDist⟩

def SurvivingNegativeSecondMomentTheorem : Prop :=
  ∃ Cstar R : ℝ, 0 < Cstar ∧ 0 < R ∧
    ∀ C : ℝ, Cstar ≤ C → ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
        ∀ T : Finset (Fin n), T.card = n - kernelCodimension n d →
          ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
            1 - 2 * R / d ≤ uniformProbability (SurvivingNegativeSecondMomentEvent (d := d)
              T ζ (Real.exp (-R * Real.rpow (d : ℝ) (1 / 96))))

theorem surviving_row_negative_second_moment_theorem : SurvivingNegativeSecondMomentTheorem := by
  obtain ⟨Cstar, R, hCstar, hR, hSurvive⟩ := surviving_row_distance_theorem
  refine ⟨Cstar, R, hCstar, hR, ?_⟩
  intro C hC σ Z₀ hσ0 hσ1
  obtain ⟨N, hN⟩ := hSurvive C hC σ Z₀ hσ0 hσ1
  refine ⟨N, ?_⟩
  intro n hn d hBand T hT ζ hShift
  apply (hN n hn d hBand T hT ζ hShift).trans
  exact uniformProbability_mono (fun rows h =>
    survivingRowDistanceEvent_implies_negativeSecondMoment T ζ (Real.exp_pos _) rows h)

end CircularLaw
