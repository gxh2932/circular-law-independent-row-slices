import CircularLaw.SourceNormalCoordinates
import CircularLaw.TerminalPvProbability

/-!
# The normal-rank radius comparison and cluster normalization

The polynomial normal-rank envelope is absorbed by the literal structural
growth, uniformly for both codimensions. A cluster in a nonzero scalar
multiple at the manuscript's relative radius becomes a cluster at the
checked terminal radius after dividing its centre by the same scalar.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem structural_normal_rank_radius_bound {n d L q : ℕ}
    (hd : 0 < d) (x : Fin n → ℂ)
    (hModulus : orderedNormAt x q ≤ (d : ℝ) ^ 16)
    (hGrowth : 16 * Real.log d ≤ structuralGrowth n L) :
    Real.exp (-2 * structuralGrowth n L) * orderedNormAt x q ≤
      structuralRadius n L := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hExp : Real.exp (16 * Real.log d) = (d : ℝ) ^ 16 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hdR] using Real.exp_nat_mul (Real.log d) 16
  calc
    _ ≤ Real.exp (-2 * structuralGrowth n L) * (d : ℝ) ^ 16 :=
      mul_le_mul_of_nonneg_left hModulus (Real.exp_nonneg _)
    _ = Real.exp (-2 * structuralGrowth n L + 16 * Real.log d) := by
      rw [Real.exp_add, hExp]
    _ ≤ structuralRadius n L := Real.exp_le_exp.mpr (by linarith)

theorem eventually_structural_normal_rank_radius_uniform {C a : ℝ}
    (hC : 0 < C) (ha : 0 < a) (haOne : a ≤ 1) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
        0 < sourceNormalRank a L ∧ sourceNormalRank a L ≤ n ∧
          ∀ a₃ : ℝ, ∀ x ∈ sourceGradual n d L a₃,
            Real.exp (-2 * structuralGrowth n L) * orderedNormAt x (sourceNormalRank a L) ≤
              structuralRadius n L := by
  have hBudget : ∀ᶠ d : ℕ in atTop,
      16 * Real.log d ≤ Real.rpow (d : ℝ) (1 / 96) := by
    filter_upwards [eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1 / 96)
      (by norm_num : (0 : ℝ) < 1) 0 16 (by norm_num)] with d hd
    simpa only [zero_add, one_mul] using hd
  filter_upwards [eventually_source_normal_rank_modulus_uniform hC ha haOne σ,
    eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC hBudget] with n hModulus hConditions hBudget
  intro d hBand L hL
  have hRanks := hModulus d hBand L hL
  have hCon := hConditions d hBand.1 hBand.2
  have hd : 0 < d := by have h := hCon.degree_large; omega
  have hCubicDimension : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  refine ⟨hRanks.1, hRanks.2.1, ?_⟩
  intro a₃ x hx
  exact structural_normal_rank_radius_bound hd x (hRanks.2.2 a₃ x hx)
    ((hBudget d hBand.1).trans (structuralGrowth_degree_bounds hd hCubicDimension hL).1)

theorem structural_relative_cluster_coordinate {n L q : ℕ} (x : Fin n → ℂ)
    (hRadius : Real.exp (-2 * structuralGrowth n L) * orderedNormAt x q ≤ structuralRadius n L)
    (z : ℂ) (hz : z ≠ 0) (center : ℂ) (j : Fin n)
    (hj : ‖(z • x) j - center‖ ≤
      Real.exp (-2 * structuralGrowth n L) * orderedNormAt (z • x) q) :
    ‖x j - center / z‖ ≤ structuralRadius n L := by
  have hNorm : ‖z‖ * ‖x j - center / z‖ = ‖(z • x) j - center‖ := by
    rw [← norm_mul]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [orderedNormAt_smul] at hj
  apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hz)).mp
  rw [hNorm]
  calc
    _ ≤ Real.exp (-2 * structuralGrowth n L) * (‖z‖ * orderedNormAt x q) := hj
    _ ≤ ‖z‖ * structuralRadius n L := by
      convert mul_le_mul_of_nonneg_left hRadius (norm_nonneg z) using 1
      ring

theorem structural_relative_cluster_card_le {n L q : ℕ} (x : Fin n → ℂ)
    (hRadius : Real.exp (-2 * structuralGrowth n L) * orderedNormAt x q ≤ structuralRadius n L)
    (z : ℂ) (hz : z ≠ 0) (center : ℂ) :
    (Finset.univ.filter (fun j => ‖(z • x) j - center‖ ≤
      Real.exp (-2 * structuralGrowth n L) * orderedNormAt (z • x) q)).card ≤
      (Finset.univ.filter (fun j => ‖x j - center / z‖ ≤ structuralRadius n L)).card := by
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
    structural_relative_cluster_coordinate x hRadius z hz center j (Finset.mem_filter.mp hj).2⟩

theorem sourceTerminalClusteredFamily_of_relative_cluster {n d L q : ℕ} {a₃ : ℝ}
    (x : Fin n → ℂ)
    (hx : x ∈ sourceHighHeightFamily n d L a₃ (1 / 65536) (structuralTerminalExponent n d L))
    (hRadius : Real.exp (-2 * structuralGrowth n L) * orderedNormAt x q ≤ structuralRadius n L)
    (z : ℂ) (hz : z ≠ 0)
    (hCluster : ∃ center : ℂ, structuralClusterFraction n L * n <
      ((Finset.univ.filter (fun j => ‖(z • x) j - center‖ ≤
        Real.exp (-2 * structuralGrowth n L) * orderedNormAt (z • x) q)).card : ℝ)) :
    x ∈ sourceTerminalClusteredFamily n d L a₃ := by
  obtain ⟨center, hCount⟩ := hCluster
  refine ⟨hx, center / z, hCount.trans_le ?_⟩
  exact_mod_cast structural_relative_cluster_card_le x hRadius z hz center

end CircularLaw
