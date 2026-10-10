import CircularLaw.TerminalPvEnergy
import CircularLaw.FiniteProbabilitySupremum

/-!
# Probability sums for the actual clustered terminal family

The terminal parameters discharge every source separation and net-range
hypothesis. The cluster centre may depend on the vector. The actual
source family uses the strict cluster inequality in the manuscript.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def sourceTerminalClusteredFamily (n d L : ℕ) (a₃ : ℝ) : Set (Fin n → ℂ) :=
  {x | x ∈ sourceHighHeightFamily n d L a₃ (1 / 65536) (structuralTerminalExponent n d L) ∧
    ∃ c₀ : ℂ, structuralClusterFraction n L * n <
      ((Finset.univ.filter (fun i => ‖x i - c₀‖ ≤ structuralRadius n L)).card : ℝ)}

theorem sourceTerminalClusteredFamily_subset (n d L : ℕ) (a₃ : ℝ) :
    sourceTerminalClusteredFamily n d L a₃ ⊆
      sourceHighHeightFamily n d L a₃ (1 / 65536) (structuralTerminalExponent n d L) :=
  fun _ hx => hx.1

theorem sourceTerminalClusteredFamily_cluster {n d L : ℕ} {a₃ : ℝ} {x : Fin n → ℂ}
    (hx : x ∈ sourceTerminalClusteredFamily n d L a₃) :
    ∃ c₀ : ℂ, structuralClusterFraction n L * n ≤
      ((Finset.univ.filter (fun i => ‖x i - c₀‖ ≤ structuralRadius n L)).card : ℝ) := by
  obtain ⟨c₀, hc₀⟩ := hx.2
  exact ⟨c₀, hc₀.le⟩

theorem eventually_sourcePv_probability_decay_uniform {a₃ C σ : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1)
    (R : ℝ) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
      ∀ X : Set (Fin n → ℂ),
      X ⊆ sourceHighHeightFamily n d L a₃ (1 / 65536) (structuralTerminalExponent n d L) →
      (∀ x ∈ X, ∃ c₀ : ℂ, structuralClusterFraction n L * n ≤
        ((Finset.univ.filter (fun i => ‖x i - c₀‖ ≤ structuralRadius n L)).card : ℝ)) →
      ∃ hA : (canonicalApproxFamily (d ^ structuralTerminalExponent n d L) X).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ structuralTerminalExponent n d L) X) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L →
      canonicalFamilySupProbabilitySum (canonicalApproxFamily (d ^ structuralTerminalExponent n d L) X)
          I (d ^ structuralTerminalExponent n d L) d R ≤
        Real.exp (-(sourcePvDecayRate a₃ / 2) * n * structuralClusterFraction n L *
          structuralTerminalExponent n d L) +
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_source_Pv_family_probability_uniform ha hSmall hC σ,
    eventually_terminalPv_hypotheses_uniform ha hCPos σ,
    eventually_structural_discretization_range_uniform hCPos hσ,
    eventually_structural_profileException_uniform hC σ R,
    eventually_sourcePv_mainTerm_absorbed_uniform ha (by linarith : 1 ≤ C) σ R]
    with n hSum hHypotheses hRange hException hMain
  intro d hBand L hL X hX hCluster
  have hHyp := hHypotheses d hBand L hL
  obtain ⟨hA, hBound⟩ := hSum d hBand L hL (structuralTerminalExponent n d L)
    (by omega : 5 ≤ structuralTerminalExponent n d L)
    (hRange d hBand L hL _ le_rfl) (structuralRadius n L) (structuralClusterFraction n L)
    hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1 hHyp.2.2.2.2 X hX hCluster
  refine ⟨hA, ?_⟩
  letI : Fintype (canonicalApproxFamily (d ^ structuralTerminalExponent n d L) X) := hA.fintype
  intro I hI
  apply canonicalFamilySupProbabilitySum_le _ I (d ^ structuralTerminalExponent n d L) d R _
  intro V
  have h := hBound I hI R hR V
  rw [mul_add] at h
  apply h.trans
  exact add_le_add (hMain d hBand L hL)
    (hException d hBand L hL a₃ _ le_rfl X
      (hX.trans (sourceHighHeightFamily_subset a₃ (1 / 65536))))

theorem eventually_sourceTerminalClustered_probability_uniform {a₃ C σ : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1)
    (R : ℝ) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
      ∃ hA : (canonicalApproxFamily (d ^ structuralTerminalExponent n d L)
        (sourceTerminalClusteredFamily n d L a₃)).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ structuralTerminalExponent n d L)
        (sourceTerminalClusteredFamily n d L a₃)) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L →
      canonicalFamilySupProbabilitySum (canonicalApproxFamily (d ^ structuralTerminalExponent n d L)
        (sourceTerminalClusteredFamily n d L a₃)) I (d ^ structuralTerminalExponent n d L) d R ≤
        Real.exp (-(sourcePvDecayRate a₃ / 2) * n * structuralClusterFraction n L *
          structuralTerminalExponent n d L) +
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) := by
  filter_upwards [eventually_sourcePv_probability_decay_uniform ha hSmall hC hσ R hR]
    with n hBound
  intro d hBand L hL
  exact hBound d hBand L hL (sourceTerminalClusteredFamily n d L a₃)
    (sourceTerminalClusteredFamily_subset n d L a₃)
    (fun _ hx => sourceTerminalClusteredFamily_cluster hx)

end CircularLaw
