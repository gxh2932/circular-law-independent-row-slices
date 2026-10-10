import CircularLaw.ConvolutionConcentration

/-!
# Small balls for a separated atomic law

When a law is concentrated on separated points, a sufficiently small
closed disk contains at most one of those points. Its probability is
therefore bounded by the maximum atom. The support need not be finite.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace CircularLaw

def SeparatedPlanarLaw (μ : Measure ℂ) (δ u : ℝ) : Prop :=
  ∃ S : Set ℂ, (∀ᵐ x ∂μ, x ∈ S) ∧
    S.Pairwise (fun x y => δ ≤ dist x y) ∧
    ∀ x, μ {x} ≤ ENNReal.ofReal u

theorem separated_planar_law_small_ball {μ : Measure ℂ} {δ u r : ℝ}
    (hLaw : SeparatedPlanarLaw μ δ u) (hr : 2 * r < δ) (z : ℂ) :
    μ (Metric.closedBall z r) ≤ ENNReal.ofReal u := by
  obtain ⟨S, hS, hSep, hAtom⟩ := hLaw
  by_cases hExists : ∃ a ∈ S, a ∈ Metric.closedBall z r
  · obtain ⟨a, haS, haBall⟩ := hExists
    have hSub : (Metric.closedBall z r : Set ℂ) ≤ᵐ[μ] ({a} : Set ℂ) := by
      filter_upwards [hS] with x hxS
      intro hxBall
      have hxa : x = a := by
        by_contra hne
        have hLow := hSep hxS haS hne
        have hHigh : dist x a ≤ 2 * r := by
          have hx : dist x z ≤ r := hxBall
          have ha : dist z a ≤ r := by rw [dist_comm]; exact haBall
          linarith [dist_triangle x z a]
        linarith
      exact Set.mem_singleton_iff.mpr hxa
    exact (measure_mono_ae hSub).trans (hAtom a)
  · have hSub : (Metric.closedBall z r : Set ℂ) ≤ᵐ[μ] (∅ : Set ℂ) := by
      filter_upwards [hS] with x hxS
      intro hxBall
      exact (hExists ⟨x, hxS, hxBall⟩).elim
    exact (measure_mono_ae hSub).trans (by simp only [measure_empty]; exact bot_le)

end CircularLaw
