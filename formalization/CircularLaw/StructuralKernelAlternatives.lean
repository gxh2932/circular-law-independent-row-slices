import CircularLaw.StructuralNormalRadius
import CircularLaw.TerminalKernelProbability
import CircularLaw.KernelCompatibility

/-!
# The literal structural alternatives from terminal kernel exclusions

The actual kernel compatibility, gradual decomposition, radius comparison
and terminal spread/cluster exclusions imply the two source alternatives.
The centre is arbitrary and the forbidden cluster count is strictly
greater than the manuscript threshold. The probability assembly below
keeps the actual restricted-norm failure as an explicit remaining term.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def SourceStructuralKernel {n d : ℕ} (L : ℕ) (a : ℝ) (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) : Prop :=
  ∀ v : Fin n → ℂ, v ≠ 0 → (retainedShiftedMatrix I ζ rows).mulVec v = 0 →
    (∃ i : ℕ, 0 < i ∧ i ≤ sourceNormalRank a L ∧
      (9 / 10 : ℝ) * ((n : ℝ) / i) ^ 3 * orderedNormAt v (sourceNormalRank a L) <
        orderedNormAt v i) ∨
    (∀ i : ℕ, 0 < i → i ≤ sourceNormalRank a L →
      orderedNormAt v i ≤
        (9 / 10 : ℝ) * ((n : ℝ) / i) ^ 3 * orderedNormAt v (sourceNormalRank a L)) ∧
    ∀ center : ℂ,
      ((Finset.univ.filter (fun j => ‖v j - center‖ ≤
        Real.exp (-2 * structuralGrowth n L) * orderedNormAt v (sourceNormalRank a L))).card : ℝ) ≤
          structuralClusterFraction n L * n

theorem retained_kernel_of_nonzero_smul {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ)
    (hKernel : (retainedShiftedMatrix I ζ rows).mulVec (z • x) = 0) :
    (retainedShiftedMatrix I ζ rows).mulVec x = 0 := by
  rw [Matrix.mulVec_smul] at hKernel
  have hBack := congrArg (fun w => z⁻¹ • w) hKernel
  simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul, smul_zero] using hBack

theorem source_structural_kernel_of_terminal_exclusions {n d L : ℕ} {a a₃ : ℝ}
    (hDecomposition : sourceGradual n d L a₃ =
      (⋃ u ∈ Set.Icc 4 (structuralTerminalExponent n d L),
        sourceSpreadFamily n d L a₃ (1 / 4608) u) ∪
          sourceHighHeightFamily n d L a₃ (1 / 65536) (structuralTerminalExponent n d L))
    (hRadius : ∀ x ∈ sourceGradual n d L a₃,
      Real.exp (-2 * structuralGrowth n L) * orderedNormAt x (sourceNormalRank a L) ≤
        structuralRadius n L)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hCompatible : SourceKernelCompatible L a a₃ I ζ rows)
    (hNoSpread : ¬sourceSpreadKernelEvent L a₃ I ζ rows)
    (hNoCluster : ¬sourceTerminalClusteredKernelEvent L a₃ I ζ rows) :
    SourceStructuralKernel L a I ζ rows := by
  intro v hv hKernel
  by_cases hVL : v ∈ sourceVL n L a
  · exact Or.inl hVL.2
  refine Or.inr ⟨?_, ?_⟩
  · intro i hi hiq
    apply le_of_not_gt
    intro hBad
    exact hVL ⟨hv, i, hi, hiq, hBad⟩
  · intro center
    apply le_of_not_gt
    intro hBad
    have hCone : v ∈ nonzeroScalarCone (sourceGradual n d L a₃) :=
      (hCompatible ⟨hv, hKernel⟩).resolve_left hVL
    obtain ⟨z, hz, x, hx, hScaled⟩ := hCone
    have hKernelX := retained_kernel_of_nonzero_smul I ζ rows z hz x (by
      rw [← hScaled]
      exact hKernel)
    have hRadiusX := hRadius x hx
    rw [hDecomposition] at hx
    rcases hx with hSpread | hHigh
    · obtain ⟨u, hu, hxSpread⟩ := Set.mem_iUnion₂.mp hSpread
      exact hNoSpread ⟨u, Finset.mem_Icc.mpr hu, x, hxSpread, hKernelX⟩
    · apply hNoCluster
      refine ⟨x, sourceTerminalClusteredFamily_of_relative_cluster x hHigh hRadiusX z hz ?_, hKernelX⟩
      refine ⟨center, ?_⟩
      simpa only [← hScaled] using hBad

theorem source_structural_failure_union_bound {n d L : ℕ} {a a₃ : ℝ}
    (I : Finset (Fin n)) (ζ : ℂ)
    (hAlternatives : ∀ rows : RowSliceMatrix n d,
      SourceKernelCompatible L a a₃ I ζ rows →
        ¬sourceSpreadKernelEvent L a₃ I ζ rows →
          ¬sourceTerminalClusteredKernelEvent L a₃ I ζ rows →
            SourceStructuralKernel L a I ζ rows) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceStructuralKernel L a I ζ rows) ≤
      uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceKernelCompatible L a a₃ I ζ rows) +
        uniformProbability (sourceSpreadKernelEvent (d := d) L a₃ I ζ) +
          uniformProbability (sourceTerminalClusteredKernelEvent (d := d) L a₃ I ζ) := by
  have hCover : ∀ rows : RowSliceMatrix n d, ¬SourceStructuralKernel L a I ζ rows →
      ¬SourceKernelCompatible L a a₃ I ζ rows ∨
        sourceSpreadKernelEvent L a₃ I ζ rows ∨ sourceTerminalClusteredKernelEvent L a₃ I ζ rows := by
    intro rows hBad
    by_cases hCompat : SourceKernelCompatible L a a₃ I ζ rows
    · by_cases hSpread : sourceSpreadKernelEvent L a₃ I ζ rows
      · exact Or.inr (Or.inl hSpread)
      · by_cases hCluster : sourceTerminalClusteredKernelEvent L a₃ I ζ rows
        · exact Or.inr (Or.inr hCluster)
        · exact False.elim (hBad (hAlternatives rows hCompat hSpread hCluster))
    · exact Or.inl hCompat
  apply (uniformProbability_mono hCover).trans
  apply (uniformProbability_or_le _ _).trans
  have h := add_le_add (le_refl (uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬SourceKernelCompatible L a a₃ I ζ rows)))
    (uniformProbability_or_le (sourceSpreadKernelEvent (d := d) L a₃ I ζ)
      (sourceTerminalClusteredKernelEvent (d := d) L a₃ I ζ))
  convert h using 1
  ring

theorem eventually_source_structural_kernel_probability_uniform {a a₃ C σ : ℝ}
    (hC : sourceKernelLowerConstant ≤ C) (hC96 : 96 ≤ C)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 65536)
    (hEntropy : smallSetEntropy a₃ ≤ rowLoadRate / 4)
    (ha₃Net : 7 * a₃ ≤ equalBlockRateConstant (1 / 4) / 4800)
    (ha : 0 < a) (haOne : a ≤ 1) (hσ : σ ≤ 1)
    (B Z₀ R : ℝ) (hB : 0 ≤ B) (hZ : 0 ≤ Z₀) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
          uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceStructuralKernel L a I ζ rows) ≤
            4 / (n : ℝ) + Real.exp (-(sourceK1DecayExponent a₃ / 4) * n * Real.log d) +
            Real.exp (-(sourcePvDecayRate a₃ / 4) * n * structuralClusterFraction n L *
              structuralTerminalExponent n d L) +
            Real.exp (-(averagedProfileRate / 8) * n * Real.rpow (d : ℝ) (2 / 3)) +
            2 * uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B) := by
  have hCPos : 0 < C := by linarith
  have ha₃Thousand : a₃ ≤ 1 / 1000 := by linarith
  have ha₃Half : a₃ ≤ 1 / 2 := by linarith
  filter_upwards [eventually_rectangular_kernel_compatibility_uniform hC ha₃ ha₃Thousand
      hEntropy ha₃Net ha haOne σ Z₀,
    eventually_terminal_kernel_probability_uniform ha₃ ha₃Small hC96 hσ B Z₀ R hB hZ hR,
    eventually_source_gradual_decomposition_absolute ha₃ ha₃Half hCPos,
    eventually_structural_normal_rank_radius_uniform hCPos ha haOne σ,
    eventually_terminalPv_hypotheses_uniform ha₃ hCPos σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)]
    with n hCompatible hTerminal hDecomposition hRadius hTerminalHypotheses hConditions
  intro d hBand L hL I hI ζ hShift
  have hCon := hConditions d hBand.1 hBand.2
  have hdn : d ≤ n := by have h := (source_kernel_dimension_twice_degree hCon).2.2; omega
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  have hCompatFailure : uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬SourceKernelCompatible L a a₃ I ζ rows) ≤ 4 / (n : ℝ) := by
    rw [uniformProbability_not]
    linarith only [hCompatible d hBand L hL I hI ζ hShift]
  have hV := (hTerminalHypotheses d hBand L hL).1
  have hDecomp := hDecomposition d hBand.1 L (structuralTerminalExponent n d L) (by omega)
  have hRadiusHere := (hRadius d hBand L hL).2.2 a₃
  have hUnion := source_structural_failure_union_bound I ζ
    (fun rows => source_structural_kernel_of_terminal_exclusions hDecomp hRadiusHere I ζ rows)
  have hTerminalHere := hTerminal d hBand L hL I hI ζ hShift
  apply hUnion.trans
  have h := add_le_add (add_le_add hCompatFailure hTerminalHere.1) hTerminalHere.2
  convert h using 1
  ring

end CircularLaw
