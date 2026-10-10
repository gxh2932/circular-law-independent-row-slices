import CircularLaw.RowRestrictionLogVolume
import CircularLaw.VaryingProbabilityConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Probability comparison after removing prefix regularization

The two exact removal errors sum to 1/n^2. The deviation estimate keeps
the joint smallest-singular-value failure event. Its vanishing probability
and regularized comparison convergence imply the actual volume comparison.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem row_restriction_volume_comparison_le_regularized {m n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (f : Fin m ↪ Fin n) (hn : 0 < n)
    {τ : ℝ} (hτ : 0 < τ)
    (hA : ∀ j, τ ≤ orderedSquareSingularValues A j)
    (hB : ∀ j, τ ≤ orderedSquareSingularValues B j) :
    |matrixRowLogVolume (matrixRowRestriction A f) -
      matrixRowLogVolume (matrixRowRestriction B f)| / n ≤
    |regularizedRowPotential (matrixRowRestriction A f) (τ / n) -
      regularizedRowPotential (matrixRowRestriction B f) (τ / n)| / n + 1 / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRemoveA := row_restriction_regularized_log_removal A f hn hτ (hA _)
  have hRemoveB := row_restriction_regularized_log_removal B f hn hτ (hB _)
  have hAbsA : |matrixRowLogVolume (matrixRowRestriction A f) / n -
      regularizedRowPotential (matrixRowRestriction A f) (τ / n) / n| ≤ 1 / (2 * (n : ℝ) ^ 2) := by
    rw [show matrixRowLogVolume (matrixRowRestriction A f) / n -
      regularizedRowPotential (matrixRowRestriction A f) (τ / n) / n =
      -((regularizedRowPotential (matrixRowRestriction A f) (τ / n) -
        matrixRowLogVolume (matrixRowRestriction A f)) / n) by ring,
      abs_neg, abs_of_nonneg hRemoveA.1]
    exact hRemoveA.2
  have hAbsB : |regularizedRowPotential (matrixRowRestriction B f) (τ / n) / n -
      matrixRowLogVolume (matrixRowRestriction B f) / n| ≤ 1 / (2 * (n : ℝ) ^ 2) := by
    rw [← sub_div, abs_of_nonneg hRemoveB.1]
    exact hRemoveB.2
  have hFirst := abs_sub_le (matrixRowLogVolume (matrixRowRestriction A f) / n)
    (regularizedRowPotential (matrixRowRestriction A f) (τ / n) / n)
    (matrixRowLogVolume (matrixRowRestriction B f) / n)
  have hSecond := abs_sub_le (regularizedRowPotential (matrixRowRestriction A f) (τ / n) / n)
    (regularizedRowPotential (matrixRowRestriction B f) (τ / n) / n)
    (matrixRowLogVolume (matrixRowRestriction B f) / n)
  have hScale : 1 / (2 * (n : ℝ) ^ 2) + 1 / (2 * (n : ℝ) ^ 2) = 1 / (n : ℝ) ^ 2 := by ring
  have hBound : |matrixRowLogVolume (matrixRowRestriction A f) / n -
      matrixRowLogVolume (matrixRowRestriction B f) / n| ≤
      |regularizedRowPotential (matrixRowRestriction A f) (τ / n) / n -
        regularizedRowPotential (matrixRowRestriction B f) (τ / n) / n| + 1 / (n : ℝ) ^ 2 := by
    linarith
  simpa only [← sub_div, abs_div, abs_of_pos hnR] using hBound

theorem row_restriction_volume_deviation_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {m n : ℕ}
    (A B : Ω → Matrix (Fin n) (Fin n) ℂ) (f : Fin m ↪ Fin n) (hn : 0 < n)
    {τ : ℝ} (hτ : 0 < τ) (ε : ℝ) :
    μ.real {ω | ε + 1 / (n : ℝ) ^ 2 <
      |matrixRowLogVolume (matrixRowRestriction (A ω) f) -
        matrixRowLogVolume (matrixRowRestriction (B ω) f)| / n} ≤
    μ.real {ω | ¬((∀ j, τ ≤ orderedSquareSingularValues (A ω) j) ∧
      (∀ j, τ ≤ orderedSquareSingularValues (B ω) j))} +
    μ.real {ω | ε < |regularizedRowPotential (matrixRowRestriction (A ω) f) (τ / n) -
      regularizedRowPotential (matrixRowRestriction (B ω) f) (τ / n)| / n} := by
  have hSubset : {ω | ε + 1 / (n : ℝ) ^ 2 <
      |matrixRowLogVolume (matrixRowRestriction (A ω) f) -
        matrixRowLogVolume (matrixRowRestriction (B ω) f)| / n} ⊆
      {ω | ¬((∀ j, τ ≤ orderedSquareSingularValues (A ω) j) ∧
        (∀ j, τ ≤ orderedSquareSingularValues (B ω) j))} ∪
      {ω | ε < |regularizedRowPotential (matrixRowRestriction (A ω) f) (τ / n) -
        regularizedRowPotential (matrixRowRestriction (B ω) f) (τ / n)| / n} := by
    intro ω hω
    by_cases hGood : (∀ j, τ ≤ orderedSquareSingularValues (A ω) j) ∧
        (∀ j, τ ≤ orderedSquareSingularValues (B ω) j)
    · apply Or.inr
      have hBound := row_restriction_volume_comparison_le_regularized (A ω) (B ω) f hn hτ hGood.1 hGood.2
      change ε + 1 / (n : ℝ) ^ 2 < _ at hω
      change ε < _
      linarith
    · exact Or.inl hGood
  exact (measureReal_mono (μ := μ) hSubset).trans (measureReal_union_le _ _)

theorem row_restriction_volume_comparison_converges {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsFiniteMeasure (μ n)] (m : ℕ → ℕ)
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ) (f : ∀ n, Fin (m n) ↪ Fin n)
    (τ : ℕ → ℝ) (hτ : ∀ᶠ n in atTop, 0 < τ n)
    (hRegularized : VaryingConvergesInProbability μ (fun n ω =>
      (regularizedRowPotential (matrixRowRestriction (A n ω) (f n)) (τ n / n) -
        regularizedRowPotential (matrixRowRestriction (B n ω) (f n)) (τ n / n)) / n) 0)
    (hBad : Tendsto (fun n => (μ n).real {ω |
      ¬((∀ j, τ n ≤ orderedSquareSingularValues (A n ω) j) ∧
        (∀ j, τ n ≤ orderedSquareSingularValues (B n ω) j))}) atTop (𝓝 0)) :
    VaryingConvergesInProbability μ (fun n ω =>
      (matrixRowLogVolume (matrixRowRestriction (A n ω) (f n)) -
        matrixRowLogVolume (matrixRowRestriction (B n ω) (f n))) / n) 0 := by
  intro ε hε
  have hR := hRegularized (ε / 2) (by linarith)
  have hUpper := hBad.add hR
  simp only [add_zero] at hUpper
  have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).inv_tendsto_atTop
  have hError : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow, zero_pow (by decide : 2 ≠ 0)] using hInv.pow 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hτ, eventually_gt_atTop 0,
    hError.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))] with n hτn hn he
  have hBound := row_restriction_volume_deviation_probability_bound (μ n) (A n) (B n)
    (f n) hn hτn (ε / 2)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hSubset : {ω | ε < |(matrixRowLogVolume (matrixRowRestriction (A n ω) (f n)) -
      matrixRowLogVolume (matrixRowRestriction (B n ω) (f n))) / n - 0|} ⊆
      {ω | ε / 2 + 1 / (n : ℝ) ^ 2 <
        |matrixRowLogVolume (matrixRowRestriction (A n ω) (f n)) -
          matrixRowLogVolume (matrixRowRestriction (B n ω) (f n))| / n} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, sub_zero, abs_div, abs_of_pos hnR] at hω ⊢
    linarith
  have h := (measureReal_mono (μ := μ n) hSubset).trans hBound
  simpa only [sub_zero, abs_div, abs_of_pos hnR] using h

end CircularLaw
