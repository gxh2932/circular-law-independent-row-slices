import CircularLaw.RegularizedLogTailBound
import CircularLaw.EmpiricalNegativeLogUI
import CircularLaw.VaryingProbabilityConvergence

/-!
# Probability removal of regularization from a positive ambient array

Each negative-log tail event includes zero entries. A vanishing ridge
scale and the checked finite reference-tail bound therefore give actual
log-volume convergence, with no minimum-value assumption on the reference.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

theorem regularized_row_log_removal_of_reference_tail {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (m : ℕ → ℕ) (A : ∀ n, Ω n → Matrix (Fin (m n)) (Fin n) ℂ)
    (e : ∀ n, Fin (Fintype.card (Fin (m n))) ↪ Fin n) (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (η : ℕ → ℝ) (hη : ∀ᶠ n : ℕ in atTop, 0 < η n) (hηLimit : Tendsto η atTop (𝓝 0))
    (hLower : ∀ᶠ n : ℕ in atTop, ∀ ω, ∀ j, (s n ω (e n j) : ℝ) ≤ orderedMatrixSingularValues (A n ω) j)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 ≤ T ∧
      Tendsto (fun n => (μ n).real {ω | EmpiricalNegativeLogTailEvent (s n ω) T ε}) atTop (𝓝 0)) :
    VaryingConvergesInProbability μ (fun n ω =>
      (regularizedRowPotential (A n ω) (η n) - matrixRowLogVolume (A n ω)) / n) 0 := by
  intro ε hε
  obtain ⟨T, hT, hTailLimit⟩ := hTail (ε / 4) (by linarith only [hε])
  have hScale : ∀ᶠ n : ℕ in atTop, η n ≤ Real.exp (-T) :=
    (hηLimit.eventually (gt_mem_nhds (Real.exp_pos (-T)))).mono (fun _ h => h.le)
  have hBudget : Tendsto (fun n => η n ^ 2 / (2 * Real.exp (-T) ^ 2)) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_div] using (hηLimit.pow 2).div_const (2 * Real.exp (-T) ^ 2)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hTailLimit
  filter_upwards [hη, hLower, hScale, eventually_gt_atTop 0,
    hBudget.eventually (gt_mem_nhds (by linarith only [hε] : (0 : ℝ) < ε / 2))]
      with n hηn hLowern hScaleN hn hSmall
  apply measureReal_mono (μ := μ n)
  intro ω hFail
  by_contra hGood
  have hPositive (j : Fin n) : 0 < s n ω j :=
    lt_of_le_of_ne (zero_le _) (fun h => hGood (Or.inl ⟨j, h.symm⟩))
  have hTailValue : empiricalNegativeLogTail (s n ω) T ≤ ε / 4 :=
    le_of_not_gt (fun h => hGood (Or.inr h))
  have hBounds := regularized_row_log_removal_reference_tail (A n ω) (e n) hn
    (s n ω) hPositive (hLowern ω) hηn hT hScaleN
  simp only [Set.mem_setOf_eq, sub_zero, abs_of_nonneg hBounds.1] at hFail
  linarith only [hFail, hBounds.2, hTailValue, hSmall]

end CircularLaw
