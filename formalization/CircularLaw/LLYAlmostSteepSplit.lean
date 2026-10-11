import CircularLaw.LLYThirdSteepNormalization
import CircularLaw.LLYFirstSteepAdjoint
import CircularLaw.LLYAlmostAdjointReduction

/-!
# Retaining almost-constancy in the steep adjoint reduction

The third-class estimate is needed only for almost-constant unit vectors.
This split keeps that condition, so the actual finite-net probability
bound applies without assuming a bound on the larger unrestricted class.
-/

noncomputable section
open Classical

namespace CircularLaw

def llySecondAlmostUnitAdjointFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (ℓ r k₁ k₂ : ℕ) (α ρ s : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∧ ¬sourceNonAlmostConstant α ρ x ∧
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ≤ s

theorem source_almost_adjoint_failure_lly_split_preserving_almost {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (ℓ r k₁ k₂ k₃ : ℕ) (α ρ s : ℝ)
    (hFail : sourceAlmostConstantAdjointFailure (fullShiftedSliceMatrix ζ rows) α ρ s) :
    ((llyFirstSteepAdjointFailure ζ rows ℓ r k₁ s ∨
      llySecondAlmostUnitAdjointFailure ζ rows ℓ r k₁ k₂ α ρ s) ∨
      llyThirdAlmostUnitAdjointFailure ζ rows ℓ r k₁ k₂ k₃ α ρ s) ∨
      llyGradualAlmostAdjointFailure ζ rows ℓ r k₁ k₂ k₃ α ρ s := by
  obtain ⟨x, hUnit, hAlmost, hSmall⟩ := hFail
  by_cases hFirst : (fun j => x j) ∈ llyFirstSteep d ℓ r k₁
  · exact Or.inl (Or.inl (Or.inl ⟨x, hUnit, hFirst, hSmall⟩))
  by_cases hSecond : (fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂
  · exact Or.inl (Or.inl (Or.inr ⟨x, hUnit, hSecond, hAlmost, hSmall⟩))
  by_cases hThird : (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃
  · exact Or.inl (Or.inr ⟨x, hUnit, hThird, hAlmost, hSmall⟩)
  · exact Or.inr ⟨x, hUnit, hAlmost, by
      rintro ((h | h) | h)
      · exact hFirst h
      · exact hSecond h
      · exact hThird h, hSmall⟩

theorem source_almost_adjoint_probability_lly_split_preserving_almost {n d : ℕ}
    (ζ : ℂ) (ℓ r k₁ k₂ k₃ : ℕ) (α ρ s : ℝ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceAlmostConstantAdjointFailure (fullShiftedSliceMatrix ζ rows) α ρ s) ≤
      ((uniformProbability (fun rows : RowSliceMatrix n d => llyFirstSteepAdjointFailure ζ rows ℓ r k₁ s) +
        uniformProbability (fun rows : RowSliceMatrix n d => llySecondAlmostUnitAdjointFailure ζ rows ℓ r k₁ k₂ α ρ s)) +
        uniformProbability (fun rows : RowSliceMatrix n d => llyThirdAlmostUnitAdjointFailure ζ rows ℓ r k₁ k₂ k₃ α ρ s)) +
        uniformProbability (fun rows : RowSliceMatrix n d => llyGradualAlmostAdjointFailure ζ rows ℓ r k₁ k₂ k₃ α ρ s) := by
  apply (uniformProbability_mono (fun rows hFail =>
    source_almost_adjoint_failure_lly_split_preserving_almost ζ rows ℓ r k₁ k₂ k₃ α ρ s hFail)).trans
  apply (uniformProbability_or_le _ _).trans
  apply add_le_add _ le_rfl
  apply (uniformProbability_or_le _ _).trans
  apply add_le_add _ le_rfl
  exact uniformProbability_or_le _ _

end CircularLaw
