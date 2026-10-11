import CircularLaw.RestrictedNormUniform
import CircularLaw.CanonicalKernelProbabilityReduction
import CircularLaw.StructuralNetUnion
import CircularLaw.UniformGradualClassCount

/-!
# All parts of the named row-slice net-reduction lemma

The deterministic approximants are the literal canonical image. Every
subfamily of the normalized gradual class, hence both manuscript family
types, has checked finiteness, class count and class cardinality. The
actual continuous-kernel probability has the displayed shift-supremum
sum and `n^-100` error. The union over `4<=u<=v_L` has the source crude
count. One dimension threshold covers every source degree and codimension.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology Nat

namespace CircularLaw

structure SourceNetReductionConclusions (n d L : ℕ) (a₃ R Z₀ : ℝ) : Prop where
  family_finite : ∀ u : ℕ, u ≤ structuralTerminalExponent n d L →
    ∀ X : Set (Fin n → ℂ), X ⊆ sourceGradual n d L a₃ → (canonicalApproxFamily (d ^ u) X).Finite
  family_k_vectors : ∀ u : ℕ, ∀ X : Set (Fin n → ℂ), ∀ y ∈ canonicalApproxFamily (d ^ u) X,
    IsKVector (d ^ u) y
  class_count : ∀ u : ℕ, u ≤ structuralTerminalExponent n d L →
    ∀ X : Set (Fin n → ℂ), X ⊆ sourceGradual n d L a₃ →
      (Nat.card {m : Multiset ℂ // m ∈ coordinateMultisetClasses (canonicalApproxFamily (d ^ u) X)} : ℝ) ≤
        Real.exp n
  class_cardinality : ∀ (u : ℕ) (X : Set (Fin n → ℂ)) (y : Fin n → ℂ),
    let P := orderedCanonicalRowProfile y ((d : ℝ) / (d ^ u : ℕ))
    (Nat.card (CoordinateMultisetClassIn (canonicalApproxFamily (d ^ u) X) y) : ℝ) ≤
      ((n)! : ℝ) / (∏ q, ((profilePartSize P q)! : ℝ)) *
        (∏ q, (P.height q : ℝ) ^ profilePartSize P q)
  kernel_probability : ∀ u : ℕ, u ≤ structuralTerminalExponent n d L →
    ∀ X : Set (Fin n → ℂ), X ⊆ sourceGradual n d L a₃ →
    ∀ hA : (canonicalApproxFamily (d ^ u) X).Finite,
    letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
    ∀ I : Finset (Fin n), ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
      uniformProbability (fun rows : RowSliceMatrix n d =>
        ∃ x ∈ X, (retainedShiftedMatrix I ζ rows).mulVec x = 0) ≤
        2 * (d : ℝ) ^ 2 * canonicalFamilySupProbabilitySum (canonicalApproxFamily (d ^ u) X)
          I (d ^ u) d R + 1 / (n : ℝ) ^ 100
  crude_union_count : ∀ X : ℕ → Set (Fin n → ℂ), (∀ u, X u ⊆ sourceGradual n d L a₃) →
    (structuralNetUnion d (structuralTerminalExponent n d L) X).Finite ∧
      (Nat.card (structuralNetUnion d (structuralTerminalExponent n d L) X) : ℝ) ≤
        (structuralTerminalExponent n d L : ℝ) *
          Real.exp (128 * (n : ℝ) * Real.rpow (d : ℝ) (1 / 3))

theorem eventually_source_net_reduction_conclusions_uniform {a₃ C σ : ℝ}
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1) (Z₀ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → SourceNetReductionConclusions n d L a₃ 1 Z₀ := by
  have hCPos : 0 < C := by linarith only [hC]
  filter_upwards [eventually_structuralGradualNet_count_uniform hC σ,
    eventually_restrictedGradualApproxClasses_exp_n_uniform ha₃ ha₃Small hCPos σ,
    eventually_structural_discretization_range_uniform hCPos hσ,
    eventually_structuralNetUnion_count_uniform hC σ,
    eventually_canonical_kernel_probability_reduction_uniform hCPos σ
      (rowSliceComplexNormConstant 100) (max 0 Z₀) 1
      (rowSliceComplexNormConstant_nonneg (by norm_num)) (le_max_left _ _) le_rfl,
    eventually_retainedCenteredNormBound_hundred_uniform hC σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)]
      with n hFinite hClasses hRange hUnion hReduction hNorm hConditions
  intro d hBand L hL
  have hCon := source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu X hX
    exact (hFinite d hBand L hL a₃ u hu X hX).1
  · intro u X y hy
    exact canonicalApproxFamily_isKVector (d ^ u) X hy
  · intro u hu X hX
    exact (hClasses d hBand L hL (d ^ u) (pow_pos hCon.2.1 u)
      (hRange d hBand L hL u hu) X hX).2
  · intro u X y
    exact canonicalApprox_class_cardinality (d ^ u) X y ((d : ℝ) / (d ^ u : ℕ))
  · intro u _ X _ hA
    letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
    intro I ζ hShift
    have h := hReduction d hBand (d ^ u) (pow_pos hCon.2.1 u) X hA I ζ
      (hShift.trans (mul_le_mul_of_nonneg_right (le_max_right 0 Z₀) (Real.sqrt_nonneg _)))
    exact h.trans (add_le_add (le_refl _) (hNorm d hBand I))
  · intro X hX
    exact hUnion d hBand L hL a₃ X hX

def RowSliceNetReductionLemma : Prop :=
  ∀ a₃ : ℝ, 0 < a₃ → a₃ ≤ 1 / 65536 → ∀ C : ℝ, 96 ≤ C →
    ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
        ∀ L : ℕ, IsKernelCodimension n d L → SourceNetReductionConclusions n d L a₃ 1 Z₀

theorem row_slice_net_reduction_lemma : RowSliceNetReductionLemma := by
  intro a₃ ha₃ ha₃Small C hC σ Z₀ _ hσ
  exact eventually_atTop.mp
    (eventually_source_net_reduction_conclusions_uniform ha₃ ha₃Small hC hσ.le Z₀)

end CircularLaw
