import CircularLaw.BadRowMarkov
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Selecting surviving rows while preserving their actual distances

Deleting rows shrinks each comparison span. Whenever at most `t` exposed
rows have distance below `r`, an actual subset of exactly `N-t` rows has
every surviving leave-one-out distance at least `r`. A positive radius
also proves that this retained matrix has full row rank.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical Filter
open scoped BigOperators

namespace CircularLaw

theorem retainedConjugateRow_eq_shiftedConjugateRow {n d : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) (i : I) :
    retainedConjugateRow I ζ rows i = shiftedConjugateRow ζ rows i.val := rfl

theorem retainedRowSpan_mono {n d : ℕ} {I J : Finset (Fin n)} (hIJ : I ⊆ J)
    (ζ : ℂ) (rows : RowSliceMatrix n d) : retainedRowSpan I ζ rows ≤ retainedRowSpan J ζ rows := by
  apply Submodule.span_mono
  rintro v ⟨i, rfl⟩
  exact ⟨⟨i.val, hIJ i.property⟩, rfl⟩

theorem retainedShiftedRowDistance_antitone_span {n d : ℕ}
    {I J : Finset (Fin n)} (hIJ : I ⊆ J) (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) :
    retainedShiftedRowDistance J ζ rows i ≤ retainedShiftedRowDistance I ζ rows i := by
  exact Metric.infDist_le_infDist_of_subset (retainedRowSpan_mono hIJ ζ rows)
    ⟨0, (retainedRowSpan I ζ rows).zero_mem⟩

theorem leaveOneOutRowDistance_antitone {n d : ℕ} {H T : Finset (Fin n)} (hHT : H ⊆ T)
    (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) :
    leaveOneOutRowDistance T ζ rows i ≤ leaveOneOutRowDistance H ζ rows i := by
  apply retainedShiftedRowDistance_antitone_span _ ζ rows i
  intro j hj
  obtain ⟨hji, hjH⟩ := Finset.mem_erase.mp hj
  exact Finset.mem_erase.mpr ⟨hji, hHT hjH⟩

theorem exists_surviving_rows {n d t : ℕ} (T : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (r : ℝ) (hBad : (badLeaveOneOutRows T ζ rows r).card ≤ t) :
    ∃ H : Finset (Fin n), H ⊆ T ∧ H.card = T.card - t ∧
      ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i := by
  have hSubset : badLeaveOneOutRows T ζ rows r ⊆ T := Finset.filter_subset _ _
  have hCard : T.card - t ≤ (T \ badLeaveOneOutRows T ζ rows r).card := by
    rw [Finset.card_sdiff_of_subset hSubset]
    omega
  obtain ⟨H, hH, hHCard⟩ := Finset.exists_subset_card_eq hCard
  refine ⟨H, hH.trans Finset.sdiff_subset, hHCard, ?_⟩
  intro i hi
  obtain ⟨hiT, hiGood⟩ := Finset.mem_sdiff.mp (hH hi)
  have hDist : r ≤ leaveOneOutRowDistance T ζ rows i := by
    by_contra h
    exact hiGood (Finset.mem_filter.mpr ⟨hiT, lt_of_not_ge h⟩)
  exact hDist.trans (leaveOneOutRowDistance_antitone (hH.trans Finset.sdiff_subset) ζ rows i)

theorem surviving_rows_linearIndependent {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {r : ℝ} (hr : 0 < r)
    (hDistance : ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i) :
    LinearIndependent ℂ (retainedConjugateRow H ζ rows) := by
  apply linearIndependent_iff_notMem_span.mpr
  intro i hi
  have hGenerators : (retainedConjugateRow H ζ rows) '' (Set.univ \ {i}) ⊆
      Set.range (retainedConjugateRow (H.erase i.val) ζ rows) := by
    rintro v ⟨j, hj, rfl⟩
    have hji : j ≠ i := by simpa using hj
    have hValues : j.val ≠ i.val := fun h => hji (Subtype.ext h)
    exact ⟨⟨j.val, Finset.mem_erase.mpr ⟨hValues, j.property⟩⟩, rfl⟩
  have hMem := (Submodule.span_mono hGenerators) hi
  have hZero := Metric.infDist_zero_of_mem hMem
  change leaveOneOutRowDistance H ζ rows i.val = 0 at hZero
  exact (not_le_of_gt hr) ((hDistance i.val i.property).trans_eq hZero)

theorem surviving_rows_full_rank {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {r : ℝ} (hr : 0 < r)
    (hDistance : ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i) :
    Module.finrank ℂ (retainedRowSpan H ζ rows) = H.card := by
  simpa only [retainedRowSpan, Fintype.card_coe] using
    finrank_span_eq_card (surviving_rows_linearIndependent H ζ rows hr hDistance)

theorem exists_surviving_full_rank_rows {n d t : ℕ} (T : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {r : ℝ} (hr : 0 < r)
    (hBad : (badLeaveOneOutRows T ζ rows r).card ≤ t) :
    ∃ H : Finset (Fin n), H ⊆ T ∧ H.card = T.card - t ∧
      (∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i) ∧
      LinearIndependent ℂ (retainedConjugateRow H ζ rows) ∧
      Module.finrank ℂ (retainedRowSpan H ζ rows) = H.card := by
  obtain ⟨H, hHT, hCard, hDist⟩ := exists_surviving_rows T ζ rows r hBad
  exact ⟨H, hHT, hCard, hDist, surviving_rows_linearIndependent H ζ rows hr hDist,
    surviving_rows_full_rank H ζ rows hr hDist⟩

def SurvivingRowDistanceEvent {n d : ℕ} (T : Finset (Fin n)) (ζ : ℂ) (r : ℝ)
    (rows : RowSliceMatrix n d) : Prop :=
  ∃ H : Finset (Fin n), H ⊆ T ∧ H.card = T.card - rowDeletionThreshold n d ∧
    (∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i) ∧
    LinearIndependent ℂ (retainedConjugateRow H ζ rows) ∧
    Module.finrank ℂ (retainedRowSpan H ζ rows) = H.card

theorem survivingRowDistanceEvent_probability {n d : ℕ} (hdn : d ≤ n)
    (T : Finset (Fin n)) (ζ : ℂ) {r : ℝ} (hr : 0 < r) {B : ℝ}
    (hBad : uniformProbability (fun rows : RowSliceMatrix n d =>
      rowDeletionThreshold n d < (badLeaveOneOutRows T ζ rows r).card) ≤ B) :
    1 - B ≤ uniformProbability (SurvivingRowDistanceEvent (d := d) T ζ r) := by
  haveI := rowSlice_nonempty hdn
  have hGood : uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬ rowDeletionThreshold n d < (badLeaveOneOutRows T ζ rows r).card) ≤
        uniformProbability (SurvivingRowDistanceEvent (d := d) T ζ r) :=
    uniformProbability_mono (fun rows h =>
      exists_surviving_full_rank_rows T ζ rows hr (Nat.le_of_not_gt h))
  rw [uniformProbability_not] at hGood
  linarith

def SurvivingRowDistanceTheorem : Prop :=
  ∃ Cstar R : ℝ, 0 < Cstar ∧ 0 < R ∧
    ∀ C : ℝ, Cstar ≤ C → ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
        ∀ T : Finset (Fin n), T.card = n - kernelCodimension n d →
          ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
            1 - 2 * R / d ≤ uniformProbability
              (SurvivingRowDistanceEvent (d := d) T ζ (Real.exp (-R * Real.rpow (d : ℝ) (1 / 96))))

theorem surviving_row_distance_theorem : SurvivingRowDistanceTheorem := by
  obtain ⟨Cstar, R, hCstar, hR, hBad⟩ := bad_row_markov_theorem
  refine ⟨Cstar, R, hCstar, hR, ?_⟩
  intro C hC σ Z₀ hσ0 hσ1
  obtain ⟨NB, hNB⟩ := hBad C hC σ Z₀ hσ0 hσ1
  obtain ⟨NP, hNP⟩ := eventually_atTop.mp
    (eventually_fresh_row_gaussian_parameters (hCstar.trans_le hC) hσ1.le)
  refine ⟨max NB NP, ?_⟩
  intro n hn d hBand T hT ζ hShift
  have hnB : NB ≤ n := (le_max_left _ _).trans hn
  have hnP : NP ≤ n := (le_max_right _ _).trans hn
  have hHalf := (hNP n hnP d hBand).2.2.1
  exact survivingRowDistanceEvent_probability (by omega : d ≤ n) T ζ (Real.exp_pos _)
    (hNB n hnB d hBand T hT ζ hShift).2

end CircularLaw
