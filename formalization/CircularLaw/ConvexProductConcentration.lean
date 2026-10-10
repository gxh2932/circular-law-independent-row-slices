import CircularLaw.TalagrandFiniteConcentration
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The full manuscript target for convex product concentration

This target retains
arbitrary probability spaces, bounded independent complex coordinates,
and both median- and mean-centered conclusions. Its complete proof is
in `ConvexProductConcentrationProof.lean`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace CircularLaw

def complexCoordinateVector {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℂ)
    (ω : Ω) : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun i => X i ω)

def IsRealLawMedian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (m : ℝ) : Prop :=
  1 / 2 ≤ μ.real {ω | f ω ≤ m} ∧ 1 / 2 ≤ μ.real {ω | m ≤ f ω}

/-- Full source statement, with no concentration input added as a hypothesis. -/
def ConvexProductConcentrationLemma : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (n : ℕ) (X : Fin n → Ω → ℂ), (∀ i, Measurable (X i)) → iIndepFun X μ →
    ∀ (K : ℝ), 0 < K → (∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ K) →
    ∀ (F : EuclideanSpace ℂ (Fin n) → ℝ), ConvexOn ℝ Set.univ F → LipschitzWith 1 F →
    ∀ (m : ℝ), IsRealLawMedian μ (fun ω => F (complexCoordinateVector X ω)) m →
    ∀ (t : ℝ), 0 < t →
      μ.real {ω | t * K ≤ |F (complexCoordinateVector X ω) - m|} ≤ C * Real.exp (-c * t ^ 2) ∧
      μ.real {ω | t * K ≤ |F (complexCoordinateVector X ω) -
        (∫ v, F (complexCoordinateVector X v) ∂μ)|} ≤ C * Real.exp (-c * t ^ 2)

end CircularLaw
