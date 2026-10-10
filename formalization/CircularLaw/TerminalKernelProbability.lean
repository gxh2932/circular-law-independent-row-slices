import CircularLaw.CanonicalKernelProbabilityReduction
import CircularLaw.SourceSpreadScaleSum
import CircularLaw.TerminalPvPrefactor

/-!
# Continuous terminal-family kernel probabilities

Every spread scale uses the same centered norm event, whose failure is
charged once. The actual clustered terminal family uses its checked
two-term probability sum. Only the restricted norm failure probability
is left as an explicit probabilistic input.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def sourceSpreadKernelEvent {n d : ℕ} (L : ℕ) (a₃ : ℝ) (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) : Prop :=
  ∃ u ∈ Finset.Icc 4 (structuralTerminalExponent n d L),
    ∃ x ∈ sourceSpreadFamily n d L a₃ (1 / 4608) u,
      (retainedShiftedMatrix I ζ rows).mulVec x = 0

def sourceTerminalClusteredKernelEvent {n d : ℕ} (L : ℕ) (a₃ : ℝ)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) : Prop :=
  ∃ x ∈ sourceTerminalClusteredFamily n d L a₃,
    (retainedShiftedMatrix I ζ rows).mulVec x = 0

theorem sourceSpreadProbabilitySum_nonneg {n d L : ℕ} (a₃ R : ℝ)
    (hFinite : ∀ u ∈ Finset.Icc 4 (structuralTerminalExponent n d L),
      (canonicalApproxFamily (d ^ u) (sourceSpreadFamily n d L a₃ (1 / 4608) u)).Finite)
    (I : Finset (Fin n)) : 0 ≤ sourceSpreadProbabilitySum n d L a₃ R hFinite I := by
  unfold sourceSpreadProbabilitySum
  apply Finset.sum_nonneg
  intro u _
  exact @canonicalFamilySupProbabilitySum_nonneg n
    (canonicalApproxFamily (d ^ u.val) (sourceSpreadFamily n d L a₃ (1 / 4608) u.val))
    (hFinite u.val u.property).fintype I (d ^ u.val) d R

theorem sourceSpread_kernel_on_norm_event_probability {n d L : ℕ} (hn : 0 < n) (hd : 0 < d)
    (a₃ R : ℝ) {B Z₀ : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z₀)
    (hDegree : canonicalNetCoverCoefficient B Z₀ ≤ R * Real.log d)
    (hFinite : ∀ u ∈ Finset.Icc 4 (structuralTerminalExponent n d L),
      (canonicalApproxFamily (d ^ u) (sourceSpreadFamily n d L a₃ (1 / 4608) u)).Finite)
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceSpreadKernelEvent L a₃ I ζ rows ∧ RetainedCenteredNormBound I rows B) ≤
      (d : ℝ) ^ 2 * sourceSpreadProbabilitySum n d L a₃ R hFinite I := by
  let U := {u : ℕ // u ∈ Finset.Icc 4 (structuralTerminalExponent n d L)}
  letI : Fintype U := by dsimp only [U]; infer_instance
  let E := fun (u : U) (rows : RowSliceMatrix n d) =>
    (∃ x ∈ sourceSpreadFamily n d L a₃ (1 / 4608) u.val,
      (retainedShiftedMatrix I ζ rows).mulVec x = 0) ∧ RetainedCenteredNormBound I rows B
  have hCover : ∀ rows : RowSliceMatrix n d,
      sourceSpreadKernelEvent L a₃ I ζ rows ∧ RetainedCenteredNormBound I rows B →
        ∃ u ∈ (Finset.univ : Finset U), E u rows := by
    intro rows hEvent
    obtain ⟨u, hu, x, hx, hKernel⟩ := hEvent.1
    exact ⟨⟨u, hu⟩, Finset.mem_univ _, ⟨x, hx, hKernel⟩, hEvent.2⟩
  apply (uniformProbability_mono hCover).trans
  apply (uniformProbability_finset_exists_le (Finset.univ : Finset U) E).trans
  have hPoint (u : U) :=
    @canonical_kernel_on_norm_event_probability_reduction n d (d ^ u.val) hn hd (pow_pos hd u.val)
      B Z₀ R hB hZ hDegree I ζ hShift (sourceSpreadFamily n d L a₃ (1 / 4608) u.val)
      (hFinite u.val u.property).fintype
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun (u : U) _ => hPoint u)
  apply hSum.trans
  unfold sourceSpreadProbabilitySum
  rw [← Finset.mul_sum]

theorem eventually_terminal_kernel_probability_uniform {a₃ C σ : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1)
    (B Z₀ R : ℝ) (hB : 0 ≤ B) (hZ : 0 ≤ Z₀) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
      uniformProbability (sourceSpreadKernelEvent (d := d) L a₃ I ζ) ≤
        Real.exp (-(sourceK1DecayExponent a₃ / 4) * n * Real.log d) +
        uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B) ∧
      uniformProbability (sourceTerminalClusteredKernelEvent (d := d) L a₃ I ζ) ≤
        Real.exp (-(sourcePvDecayRate a₃ / 4) * n * structuralClusterFraction n L *
          structuralTerminalExponent n d L) +
        Real.exp (-(averagedProfileRate / 8) * n * Real.rpow (d : ℝ) (2 / 3)) +
        uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_sourceSpread_scale_probability_uniform ha hSmall hC hσ R hR,
    eventually_sourceTerminalClustered_prefactor_probability_uniform ha hSmall hC hσ R hR,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_canonical_net_degree_budget_uniform hCPos B Z₀ R hB hZ hR]
    with n hSpread hClustered hConditions hBudget
  intro d hBand L hL I hI ζ hShift
  have hCon := source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)
  have hDegree := hBudget d hBand.1
  obtain ⟨hFinite, hSpreadSum⟩ := hSpread d hBand L hL
  refine ⟨?_, ?_⟩
  · have hCover : ∀ rows : RowSliceMatrix n d, sourceSpreadKernelEvent L a₃ I ζ rows →
        ¬RetainedCenteredNormBound I rows B ∨
          (sourceSpreadKernelEvent L a₃ I ζ rows ∧ RetainedCenteredNormBound I rows B) := by
      intro rows hEvent
      by_cases hNorm : RetainedCenteredNormBound I rows B
      · exact Or.inr ⟨hEvent, hNorm⟩
      · exact Or.inl hNorm
    have hOnEvent := sourceSpread_kernel_on_norm_event_probability hCon.1 hCon.2.1
      a₃ R hB hZ hDegree hFinite I ζ hShift
    have hMass := mul_nonneg (sq_nonneg (d : ℝ)) (sourceSpreadProbabilitySum_nonneg a₃ R hFinite I)
    have hMain : (d : ℝ) ^ 2 * sourceSpreadProbabilitySum n d L a₃ R hFinite I ≤
        Real.exp (-(sourceK1DecayExponent a₃ / 4) * n * Real.log d) := by
      nlinarith only [hMass, (hSpreadSum I hI).2]
    apply (uniformProbability_mono hCover).trans
    apply (uniformProbability_or_le _ _).trans
    have h := add_le_add (le_refl (uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬RetainedCenteredNormBound I rows B))) (hOnEvent.trans hMain)
    convert h using 1
    ring
  · obtain ⟨hA, hClusteredSum⟩ := hClustered d hBand L hL
    letI : Fintype (canonicalApproxFamily (d ^ structuralTerminalExponent n d L)
      (sourceTerminalClusteredFamily n d L a₃)) := hA.fintype
    have hReduction := canonical_kernel_probability_displayed_reduction hCon.1 hCon.2.1
      (pow_pos hCon.2.1 (structuralTerminalExponent n d L)) hB hZ hDegree I ζ hShift
      (sourceTerminalClusteredFamily n d L a₃)
    exact hReduction.trans (add_le_add (hClusteredSum I hI) le_rfl)

end CircularLaw
