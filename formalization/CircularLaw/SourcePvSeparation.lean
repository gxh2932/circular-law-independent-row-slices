import CircularLaw.SourcePvHighTail

/-!
# Clustered Pv separation with the manuscript hypothesis

The literal high-height family and a coordinate cluster give two integer
weight cutoffs. The low tail has mass `delta/36`, the high tail has mass
`cP*a3/4`, and their gap is at least `cP*a3*(v-4)/2`. One dimension
threshold works for all degrees above `C*log(n)`, scales and codimensions.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def SourceClusterSeparationConclusions {n : ℕ} (d v : ℕ) (x : Fin n → ℂ)
    (a₃ cP δ c₀ : ℝ) : Prop :=
  ∃ b₁ b₂ : ℤ, b₁ ≤ b₂ ∧
    δ / 36 ≤ uniformProbability (fun i =>
      dyadicProfilePartOrder (sourceScaleProfile d v x) d ((sourceScaleProfile d v x).part i) ≤ b₁) ∧
    c₀ ≤ uniformProbability (fun i =>
      b₂ ≤ dyadicProfilePartOrder (sourceScaleProfile d v x) d ((sourceScaleProfile d v x).part i)) ∧
    (cP * a₃ / 2) * ((v : ℝ) - 4) ≤ (b₂ : ℝ) - b₁

theorem source_Pv_cluster_separation {n d L v : ℕ} {a₃ cP δ ρ : ℝ}
    (hn : 0 < n) (hd : 0 < d) (ha : 0 < a₃) (hc : 0 < cP)
    (hOne : cP * a₃ ≤ 1) (hSize : 2 ≤ a₃ * (n : ℝ))
    (hDegree : 1 ≤ Real.sqrt (cP * a₃) * (d : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ))
    (hBudget : 512 * (2 - Real.logb 2 (cP * a₃) / 2) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ cP * a₃ / 4)
    (hv : 5 ≤ v) (hδ : 0 < δ) (hρ : ρ ≤ Real.rpow (d : ℝ) (-(v : ℝ)))
    (x : Fin n → ℂ) (hx : x ∈ sourceHighHeightFamily n d L a₃ cP v)
    (c : ℂ) (hCluster : δ * n ≤ ((Finset.univ.filter (fun i => ‖x i - c‖ ≤ ρ)).card : ℝ))
    (hSep : cP * a₃ * ((v : ℝ) - 4) ≥ 2 * Real.logb 2 d +
      2 * Real.logb 2 (72 * Real.sqrt d / δ) + 2 - Real.logb 2 (cP * a₃)) :
    SourceClusterSeparationConclusions d v x a₃ cP δ (cP * a₃ / 4) := by
  obtain ⟨hOrder, hGap⟩ := source_Pv_weight_cutoff_gap ha hc hd hv hSep
  exact ⟨_, _, hOrder, source_cluster_low_weight_tail hn hd x c hδ hρ hCluster,
    source_Pv_high_weight_tail hn hd ha hc hOne hSize hDegree hBudget x hx, hGap⟩

theorem source_cluster_separation_constant_mono {n d v : ℕ} {x : Fin n → ℂ}
    {a₃ cP δ c₀ c₀' : ℝ} (hConst : c₀' ≤ c₀)
    (h : SourceClusterSeparationConclusions d v x a₃ cP δ c₀) :
    SourceClusterSeparationConclusions d v x a₃ cP δ c₀' := by
  obtain ⟨b₁, b₂, hOrder, hLow, hHigh, hGap⟩ := h
  exact ⟨b₁, b₂, hOrder, hLow, hConst.trans hHigh, hGap⟩

theorem eventually_source_Pv_cluster_separation_uniform {a₃ cP C : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hc : 0 < cP)
    (hcUpper : cP ≤ 1 / 65536) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → ∀ L v : ℕ, 5 ≤ v →
      ∀ x : Fin n → ℂ, x ∈ sourceHighHeightFamily n d L a₃ cP v →
      ∀ (c : ℂ) (δ ρ : ℝ), 0 < δ → ρ ≤ Real.rpow (d : ℝ) (-(v : ℝ)) →
      δ * n ≤ ((Finset.univ.filter (fun i => ‖x i - c‖ ≤ ρ)).card : ℝ) →
      cP * a₃ * ((v : ℝ) - 4) ≥ 2 * Real.logb 2 d +
        2 * Real.logb 2 (72 * Real.sqrt d / δ) + 2 - Real.logb 2 (cP * a₃) →
      SourceClusterSeparationConclusions d v x a₃ cP δ (cP * a₃ / 4) := by
  have hs : 0 < cP * a₃ := mul_pos hc ha
  have hOne : cP * a₃ ≤ 1 := by
    have h := mul_le_mul hcUpper haHalf ha.le (by norm_num : (0 : ℝ) ≤ 1 / 65536)
    linarith
  have hDegree := eventually_degree_property_uniform hC
    ((eventually_ge_atTop 1).and ((eventually_sqrt_height_cutoff_degree hs).and
      (eventually_sqrt_height_cutoff_budget hs)))
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈2 / a₃⌉₊, hDegree]
    with n hn hSize hUniform
  intro d hLower L v hv x hx c δ ρ hδ hρ hCluster hSep
  obtain ⟨hd, hCutoff, hBudget⟩ := hUniform d hLower
  have hSizeR : 2 ≤ a₃ * (n : ℝ) := by
    have hN : (⌈2 / a₃⌉₊ : ℝ) ≤ n := by exact_mod_cast hSize
    have h := (div_le_iff₀ ha).mp ((Nat.le_ceil (2 / a₃)).trans hN)
    nlinarith
  exact source_Pv_cluster_separation hn hd ha hc hOne hSizeR hCutoff hBudget
    hv hδ hρ x hx c hCluster hSep

theorem eventually_source_Pv_cluster_separation_absolute {a₃ C : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → ∀ L v : ℕ, 5 ≤ v →
      ∀ x : Fin n → ℂ, x ∈ sourceHighHeightFamily n d L a₃ (1 / 65536) v →
      ∀ (c : ℂ) (δ ρ : ℝ), 0 < δ → ρ ≤ Real.rpow (d : ℝ) (-(v : ℝ)) →
      δ * n ≤ ((Finset.univ.filter (fun i => ‖x i - c‖ ≤ ρ)).card : ℝ) →
      (1 / 65536) * a₃ * ((v : ℝ) - 4) ≥ 2 * Real.logb 2 d +
        2 * Real.logb 2 (72 * Real.sqrt d / δ) + 2 - Real.logb 2 ((1 / 65536) * a₃) →
      SourceClusterSeparationConclusions d v x a₃ (1 / 65536) δ ((1 / 65536) * a₃ / 4) :=
  eventually_source_Pv_cluster_separation_uniform ha haHalf (by norm_num) (by norm_num) hC

end CircularLaw
