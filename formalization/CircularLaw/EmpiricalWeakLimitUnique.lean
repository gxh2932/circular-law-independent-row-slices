import CircularLaw.EmpiricalWeakConvergence
import CircularLaw.VaryingProbabilityUnique
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Uniqueness of the actual limiting empirical law

Deterministic limits of each bounded continuous test are unique in
probability. Finite Borel measures are determined by these test integrals,
so two actual weak limits are the same measure.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal

namespace CircularLaw

theorem empirical_weak_limit_unique {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν₁ ν₂ : Measure ℝ≥0) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : EmpiricalWeakConvergenceInProbability μ s ν₁)
    (h₂ : EmpiricalWeakConvergenceInProbability μ s ν₂) : ν₁ = ν₂ := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hBound : ∃ C : ℝ, ∀ t, |f t| ≤ C :=
    ⟨‖f‖, fun t => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm t⟩
  exact varying_probability_limit_unique μ (h₁ f f.continuous hBound) (h₂ f f.continuous hBound)

end CircularLaw
