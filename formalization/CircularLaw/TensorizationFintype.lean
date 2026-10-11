import CircularLaw.RareSmallBallTensorization

/-!
# Tensorization indexed by any finite type

Reindexing the already checked independent-variable bounds by an equivalence
with `Fin` preserves both the actual event and the full product exponent.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CircularLaw

theorem finite_rare_small_ball_tensorization_fintype {Ω ρ : Type*}
    [Fintype Ω] [Fintype ρ] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ρ → Ω → ℂ) (hInd : iIndepFun X μ) {t q : ℝ} (ht : 0 < t)
    (z : ρ → ℂ)
    (hSmall : ∀ i, μ.real {ω | ‖X i ω - z i‖ ≤ t / 3} ≤ 1 - q / 2) :
    μ.real {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ t ^ 2 * q * Fintype.card ρ / 72} ≤
      Real.exp (-q * (Fintype.card ρ : ℝ) / 8) := by
  let e := (Fintype.equivFin ρ).symm
  have h := finite_rare_small_ball_tensorization μ (fun i => X (e i))
    (hInd.precomp e.injective) ht (fun i => z (e i)) (fun i => hSmall (e i))
  have hSum (ω : Ω) : (∑ i, ‖X (e i) ω - z (e i)‖ ^ 2) =
      ∑ i, ‖X i ω - z i‖ ^ 2 := e.sum_comp (fun i => ‖X i ω - z i‖ ^ 2)
  simp_rw [hSum] at h
  exact h

theorem tensorization_fintype {Ω ρ : Type*} [MeasurableSpace Ω] [Fintype ρ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ρ → Ω → ℂ)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    {t A τ : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A) (hτ : 1 ≤ τ)
    (hSmall : ∀ i (σ : ℝ), 1 ≤ σ → levyConcentration μ (X i) (σ * t) ≤
      ENNReal.ofReal (A * σ ^ 2)) (z : ρ → ℂ) :
    μ.real {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * Fintype.card ρ} ≤
      (4 * Real.exp 1 * A * τ ^ 2) ^ Fintype.card ρ := by
  let e := (Fintype.equivFin ρ).symm
  have h := tensorization μ (fun i => X (e i)) (fun i => hX (e i))
    (hInd.precomp e.injective) ht hA hτ (fun i => hSmall (e i)) (fun i => z (e i))
  have hSum (ω : Ω) : (∑ i, ‖X (e i) ω - z (e i)‖ ^ 2) =
      ∑ i, ‖X i ω - z i‖ ^ 2 := e.sum_comp (fun i => ‖X i ω - z i‖ ^ 2)
  simp_rw [hSum] at h
  exact h

end CircularLaw
