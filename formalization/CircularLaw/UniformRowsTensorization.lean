import CircularLaw.AveragedRow

/-!
# Tensorization under the exact uniform row-sampling law

Finite uniform sampling is identified with its independent product law.
Pointwise row bounds therefore imply the checked squared Euclidean-norm
estimate with the source tensorization constant.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CircularLaw

theorem uniform_rows_tensorization {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {K : ℕ}
    (f : Fin K → α → ℂ) {t A τ : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A) (hτ : 1 ≤ τ)
    (hsmall : ∀ i σ, 1 ≤ σ → ∀ z : ℂ,
      uniformProbability (fun a : α => ‖f i a - z‖ ≤ σ * t) ≤ A * σ ^ 2)
    (z : Fin K → ℂ) :
    uniformProbability (fun rows : Fin K → α =>
      (∑ i, ‖f i (rows i) - z i‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * K) ≤
        (4 * Real.exp 1 * A * τ ^ 2) ^ K := by
  classical
  let μ := finiteUniformMeasure (Fin K → α)
  let X := fun i (rows : Fin K → α) => f i (rows i)
  have hInd : iIndepFun X μ := by
    dsimp only [X, μ]
    rw [finiteUniformMeasure_pi]
    exact iIndepFun_pi (fun i => (measurable_of_finite (f i)).aemeasurable)
  have hConcentration : ∀ i σ, 1 ≤ σ → levyConcentration μ (X i) (σ * t) ≤
      ENNReal.ofReal (A * σ ^ 2) := by
    intro i σ hσ
    apply iSup_le
    intro w
    have hEval : μ.map (fun rows : Fin K → α => rows i) = finiteUniformMeasure α := by
      dsimp only [μ]
      rw [finiteUniformMeasure_pi]
      exact (measurePreserving_eval (fun _ : Fin K => finiteUniformMeasure α) i).map_eq
    have hEvent := congrArg (fun ν : Measure α => ν {a | ‖f i a - w‖ ≤ σ * t}) hEval
    dsimp only at hEvent
    rw [Measure.map_apply (measurable_pi_apply i) ((Set.toFinite _).measurableSet)] at hEvent
    change μ {rows | ‖f i (rows i) - w‖ ≤ σ * t} = _ at hEvent
    rw [hEvent, finiteUniformMeasure_apply]
    exact ENNReal.ofReal_le_ofReal (hsmall i σ hσ w)
  rw [← finiteUniformMeasure_real]
  exact tensorization μ X (fun _ => measurable_of_finite _) hInd ht hA hτ hConcentration z

end CircularLaw
