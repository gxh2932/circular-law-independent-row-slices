import CircularLaw.GaussianRowDistance
import CircularLaw.RowLoadProbability
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Bad leave-one-out rows and the source deletion threshold

The expected bad-row count is the sum of its per-index probabilities.
No independence of the distance events is required. Markov at the literal
source threshold `ceil(n/d²)` gives the two-term bound and its uniform
`O(1/d)` consequence in the lower band.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical Filter
open scoped BigOperators

namespace CircularLaw

def leaveOneOutRowDistance {n d : ℕ} (T : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin n) : ℝ :=
  retainedShiftedRowDistance (T.erase i) ζ rows i

def badLeaveOneOutRows {n d : ℕ} (T : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (r : ℝ) : Finset (Fin n) :=
  T.filter (fun i => leaveOneOutRowDistance T ζ rows i < r)

def rowDeletionThreshold (n d : ℕ) : ℕ := Nat.ceil ((n : ℝ) / (d : ℝ) ^ 2)

theorem badLeaveOneOutRows_cast_sum {n d : ℕ} (T : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (r : ℝ) :
    ((badLeaveOneOutRows T ζ rows r).card : ℝ) =
      ∑ i ∈ T, if leaveOneOutRowDistance T ζ rows i < r then (1 : ℝ) else 0 := by
  simp only [badLeaveOneOutRows, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem badLeaveOneOutRows_expectation {n d : ℕ} (T : Finset (Fin n)) (ζ : ℂ) (r : ℝ) :
    finiteMean (fun rows : RowSliceMatrix n d => ((badLeaveOneOutRows T ζ rows r).card : ℝ)) =
      ∑ i ∈ T, uniformProbability (fun rows : RowSliceMatrix n d =>
        leaveOneOutRowDistance T ζ rows i < r) := by
  simp_rw [badLeaveOneOutRows_cast_sum]
  rw [finiteMean_finset_sum]
  simp only [finiteMean_indicator]

theorem badLeaveOneOutRows_expectation_le {n d : ℕ} (T : Finset (Fin n)) (ζ : ℂ) (r B : ℝ)
    (hEach : ∀ i ∈ T, uniformProbability (fun rows : RowSliceMatrix n d =>
      leaveOneOutRowDistance T ζ rows i < r) ≤ B) :
    finiteMean (fun rows : RowSliceMatrix n d => ((badLeaveOneOutRows T ζ rows r).card : ℝ)) ≤
      T.card * B := by
  rw [badLeaveOneOutRows_expectation]
  simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hEach

theorem badLeaveOneOutRows_expectation_source_bound {n d : ℕ} (hn : 0 < n)
    (T : Finset (Fin n)) (ζ : ℂ) (r : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hEach : ∀ i ∈ T, uniformProbability (fun rows : RowSliceMatrix n d =>
      leaveOneOutRowDistance T ζ rows i < r) ≤ R / (d : ℝ) ^ 3 + R / n) :
    finiteMean (fun rows : RowSliceMatrix n d => ((badLeaveOneOutRows T ζ rows r).card : ℝ)) ≤
      R * n / (d : ℝ) ^ 3 + R := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCard : (T.card : ℝ) ≤ n := by
    exact_mod_cast (by simpa using T.card_le_univ : T.card ≤ n)
  calc
    _ ≤ T.card * (R / (d : ℝ) ^ 3 + R / n) :=
      badLeaveOneOutRows_expectation_le T ζ r _ hEach
    _ ≤ n * (R / (d : ℝ) ^ 3 + R / n) :=
      mul_le_mul_of_nonneg_right hCard (by positivity)
    _ = _ := by field_simp

theorem badLeaveOneOutRows_markov_source_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (T : Finset (Fin n)) (ζ : ℂ) (r : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hEach : ∀ i ∈ T, uniformProbability (fun rows : RowSliceMatrix n d =>
      leaveOneOutRowDistance T ζ rows i < r) ≤ R / (d : ℝ) ^ 3 + R / n) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      rowDeletionThreshold n d < (badLeaveOneOutRows T ζ rows r).card) ≤
        R / d + R * (d : ℝ) ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRatio : (0 : ℝ) < (n : ℝ) / (d : ℝ) ^ 2 := by positivity
  have hMarkov := finite_uniform_markov
    (fun rows : RowSliceMatrix n d => rowDeletionThreshold n d < (badLeaveOneOutRows T ζ rows r).card)
    (fun rows => ((badLeaveOneOutRows T ζ rows r).card : ℝ)) hRatio
    (fun rows => Nat.cast_nonneg _) (by
      intro rows h
      have hCast : (rowDeletionThreshold n d : ℝ) ≤ (badLeaveOneOutRows T ζ rows r).card :=
        by exact_mod_cast h.le
      exact (Nat.le_ceil ((n : ℝ) / (d : ℝ) ^ 2)).trans hCast)
  apply hMarkov.trans
  calc
    _ ≤ (R * n / (d : ℝ) ^ 3 + R) / ((n : ℝ) / (d : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right
        (badLeaveOneOutRows_expectation_source_bound hn T ζ r hR hEach) hRatio.le
    _ = _ := by field_simp

theorem badLeaveOneOutRows_markov_degree_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hCube : d ^ 3 ≤ n) (T : Finset (Fin n)) (ζ : ℂ) (r : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hEach : ∀ i ∈ T, uniformProbability (fun rows : RowSliceMatrix n d =>
      leaveOneOutRowDistance T ζ rows i < r) ≤ R / (d : ℝ) ^ 3 + R / n) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      rowDeletionThreshold n d < (badLeaveOneOutRows T ζ rows r).card) ≤ 2 * R / d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hCubeR : (d : ℝ) ^ 3 ≤ n := by exact_mod_cast hCube
  have hScale : (d : ℝ) ^ 2 / n ≤ 1 / d := by
    apply (div_le_div_iff₀ hnR hdR).mpr
    nlinarith
  calc
    _ ≤ R / d + R * (d : ℝ) ^ 2 / n :=
      badLeaveOneOutRows_markov_source_bound hn hd T ζ r hR hEach
    _ ≤ R / d + R * (1 / d) := by
      rw [mul_div_assoc]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hScale hR) _
    _ = _ := by ring

theorem exposedRows_erase_source_card {n d : ℕ} (T : Finset (Fin n))
    (hT : T.card = n - kernelCodimension n d) {i : Fin n} (hi : i ∈ T) :
    (T.erase i).card = n - (kernelCodimension n d + 1) := by
  rw [Finset.card_erase_of_mem hi, hT]
  omega

def BadRowMarkovTheorem : Prop :=
  ∃ Cstar R : ℝ, 0 < Cstar ∧ 0 < R ∧
    ∀ C : ℝ, Cstar ≤ C → ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
        ∀ T : Finset (Fin n), T.card = n - kernelCodimension n d →
          ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
            finiteMean (fun rows : RowSliceMatrix n d =>
              ((badLeaveOneOutRows T ζ rows (Real.exp (-R * Real.rpow (d : ℝ) (1 / 96)))).card : ℝ)) ≤
                R * n / (d : ℝ) ^ 3 + R ∧
            uniformProbability (fun rows : RowSliceMatrix n d =>
              rowDeletionThreshold n d <
                (badLeaveOneOutRows T ζ rows (Real.exp (-R * Real.rpow (d : ℝ) (1 / 96)))).card) ≤
                  2 * R / d

theorem bad_row_markov_theorem : BadRowMarkovTheorem := by
  obtain ⟨Cstar, R, hCstar, hR, hDistance⟩ := leave_one_out_row_distance_theorem
  refine ⟨Cstar, R, hCstar, hR, ?_⟩
  intro C hC σ Z₀ hσ0 hσ1
  obtain ⟨ND, hND⟩ := hDistance C hC σ Z₀ hσ0 hσ1
  obtain ⟨NP, hNP⟩ := eventually_atTop.mp
    (eventually_fresh_row_gaussian_parameters (hCstar.trans_le hC) hσ1.le)
  refine ⟨max ND NP, ?_⟩
  intro n hn d hBand T hT ζ hShift
  have hnD : ND ≤ n := (le_max_left _ _).trans hn
  have hnP : NP ≤ n := (le_max_right _ _).trans hn
  obtain ⟨hn0, hd0, _, hCube, _⟩ := hNP n hnP d hBand
  have hEach (i : Fin n) (hi : i ∈ T) :
      uniformProbability (fun rows : RowSliceMatrix n d =>
        leaveOneOutRowDistance T ζ rows i < Real.exp (-R * Real.rpow (d : ℝ) (1 / 96))) ≤
          R / (d : ℝ) ^ 3 + R / n := by
    apply (uniformProbability_mono (fun rows h => h.le)).trans
    exact hND n hnD d hBand (kernelCodimension n d + 1) (Or.inr rfl)
      (T.erase i) (exposedRows_erase_source_card T hT hi) ζ hShift i (by simp)
  exact ⟨badLeaveOneOutRows_expectation_source_bound hn0 T ζ _ hR.le hEach,
    badLeaveOneOutRows_markov_degree_bound hn0 hd0 (by omega) T ζ _ hR.le hEach⟩

end CircularLaw
