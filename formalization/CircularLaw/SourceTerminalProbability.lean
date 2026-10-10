import CircularLaw.ProfileExceptionUnion
import CircularLaw.SourceFamilyProbability

/-!
# Source family probabilities at every actual terminal scale

The scale range and profile-exception cost are discharged. The
remaining explicit term in each branch is its checked class energy.
The radius constant is fixed before the uniform dimension threshold.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_source_K1_terminal_probability_uniform {a₃ C σ : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1)
    (R : ℝ) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ,
      u ≤ structuralTerminalExponent n d L →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (∀ x ∈ X, (n : ℝ) - (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))) →
      ∃ hA : (canonicalApproxFamily (d ^ u) X).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L → ∀ V : (Fin n → ℂ) → I → ℂ,
      canonicalFamilyProbabilitySum (canonicalApproxFamily (d ^ u) X) I (d ^ u) d R V ≤
        fixedNetSplitCost n d (n - L) R *
          ((4 : ℝ) ^ (n - L) * (Real.exp n * sourceK1ClassEnergyUpper n d L a₃)) +
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_source_K1_family_probability_uniform ha hSmall hC σ,
    eventually_structural_discretization_range_uniform hCPos hσ,
    eventually_structural_profileException_uniform hC σ R] with n hSum hRange hException
  intro d hBand L hL u hu X hX hK1
  obtain ⟨hA, hBound⟩ := hSum d hBand L hL u (hRange d hBand L hL u hu) X hX hK1
  refine ⟨hA, ?_⟩
  letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
  intro I hI V
  have h := hBound I hI R hR V
  have hError := hException d hBand L hL a₃ u hu X
    (hX.trans (sourceSpreadFamily_subset a₃ (1 / 4608)))
  rw [mul_add] at h
  exact h.trans (add_le_add le_rfl hError)

theorem eventually_source_K2_terminal_probability_uniform {a₃ C σ : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1)
    (R : ℝ) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ,
      u ≤ structuralTerminalExponent n d L →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (∀ x ∈ X, (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))ᶜ) →
      ∃ hA : (canonicalApproxFamily (d ^ u) X).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L → ∀ V : (Fin n → ℂ) → I → ℂ,
      canonicalFamilyProbabilitySum (canonicalApproxFamily (d ^ u) X) I (d ^ u) d R V ≤
        fixedNetSplitCost n d (n - L) R *
          ((4 : ℝ) ^ (n - L) * (Real.exp n * sourceK2ClassEnergyUpper n d L a₃)) +
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_source_K2_family_probability_uniform ha hSmall hC σ,
    eventually_structural_discretization_range_uniform hCPos hσ,
    eventually_structural_profileException_uniform hC σ R] with n hSum hRange hException
  intro d hBand L hL u hu X hX hK2
  obtain ⟨hA, hBound⟩ := hSum d hBand L hL u (hRange d hBand L hL u hu) X hX hK2
  refine ⟨hA, ?_⟩
  letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
  intro I hI V
  have h := hBound I hI R hR V
  have hError := hException d hBand L hL a₃ u hu X
    (hX.trans (sourceSpreadFamily_subset a₃ (1 / 4608)))
  rw [mul_add] at h
  exact h.trans (add_le_add le_rfl hError)

end CircularLaw
