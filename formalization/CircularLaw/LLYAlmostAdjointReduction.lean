import CircularLaw.LLYGradualAdjoint

/-!
# The full almost-constant adjoint event reduced to the steep event

The gradual probability is proved outright. The remaining steep event
contains actual unit vectors for the actual shifted row-slice adjoint.
-/

noncomputable section
open Classical

namespace CircularLaw

def llySteepAdjointFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (ℓ r k₁ k₂ k₃ : ℕ) (τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
    ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ≤ τ

theorem source_almost_adjoint_failure_lly_split {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ)
    (hFail : sourceAlmostConstantAdjointFailure (fullShiftedSliceMatrix ζ rows) δ ρ τ) :
    llySteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ τ ∨
      llyGradualAlmostAdjointFailure ζ rows ℓ r k₁ k₂ k₃ δ ρ τ := by
  obtain ⟨x, hUnit, hAlmost, hSmall⟩ := hFail
  by_cases hSteep : (fun j => x j) ∈ llySteepUnion d ℓ r k₁ k₂ k₃
  · exact Or.inl ⟨x, hUnit, hSteep, hSmall⟩
  · exact Or.inr ⟨x, hUnit, hAlmost, hSteep, hSmall⟩

theorem source_almost_adjoint_failure_probability_le_lly_steep {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hTop : (d : ℝ) * k₁ ≤ (n : ℝ) / 9)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ τ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (hThreshold : τ < 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁))
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceAlmostConstantAdjointFailure (fullShiftedSliceMatrix ζ rows) δ ρ τ) ≤
      uniformProbability (fun rows : RowSliceMatrix n d => llySteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ τ) +
        (n : ℝ) * Real.exp (-(d : ℝ) / 72) := by
  apply (uniformProbability_mono (fun rows hFail =>
    source_almost_adjoint_failure_lly_split ζ rows ℓ r k₁ k₂ k₃ δ ρ τ hFail)).trans
    ((uniformProbability_or_le _ _).trans ?_)
  apply add_le_add (le_refl _)
  exact lly_gradual_almost_adjoint_failure_probability hn hd hdn hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃
    hFit hHalf hTop hScale₂ hScale₃ hDensity hRadius hThreshold ζ hShift

end CircularLaw
