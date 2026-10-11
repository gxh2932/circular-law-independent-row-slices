import CircularLaw.TailDispersion
import CircularLaw.SourceLLTTYPackage

/-!
# Actual profile dispersion in the K2 and clustered Pv branches

Both lower bounds use the coordinate distribution of the constructed
dyadic weight order. The uniform conclusions apply the proved LLTTY
package; the separated tails are conclusions, not extra assumptions.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def profileCoordinateDispersion {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (d : ℕ) : ℝ :=
  pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))

theorem profileCoordinateDispersion_eq_integer {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (d : ℕ) :
    profileCoordinateDispersion P d =
      pairDispersion (fun a => (dyadicProfilePartOrder P d (P.part a) : ℝ)) := rfl

theorem source_K2_profile_dispersion {n d u : ℕ} {a₃ cK c₀ c₁ C : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (x : Fin n → ℂ)
    (hBranch : SourceSpreadPackageConclusions d u x a₃ cK c₀ c₁ C)
    (hK2 : cK * (thirdSteepScale n a₃ : ℝ) / 4 ≤
      profileSelectedMass (sourceScaleProfile d u x)
        (profileCutoffParts (sourceScaleProfile d u x) d (cK * a₃ / 16))ᶜ) :
    (2 * c₀ ^ 2 * c₁) * Real.rpow (d : ℝ) (cK * a₃ / 16) ≤
      profileCoordinateDispersion (sourceScaleProfile d u x) d := by
  obtain ⟨b₁, b₂, _, hLow, hHigh, hGap⟩ := hBranch.2.2.2 hK2
  have h := pairDispersion_integer_two_tail_bound
    (g := c₁ * Real.rpow (d : ℝ) (cK * a₃ / 16))
    (fun a => dyadicProfilePartOrder (sourceScaleProfile d u x) d ((sourceScaleProfile d u x).part a))
    hc₀ hc₀ (mul_nonneg hc₁ (Real.rpow_nonneg (Nat.cast_nonneg d) _)) hLow hHigh hGap
  change _ ≤ profileCoordinateDispersion (sourceScaleProfile d u x) d at h
  convert h using 1
  ring

theorem source_Pv_profile_dispersion {n d v : ℕ} {a₃ cP δ c₀ : ℝ}
    (hδ : 0 ≤ δ) (hc₀ : 0 ≤ c₀) (hs : 0 ≤ cP * a₃) (hv : 5 ≤ v)
    (x : Fin n → ℂ) (hSeparation : SourceClusterSeparationConclusions d v x a₃ cP δ c₀) :
    (δ * c₀ * (cP * a₃) / 36) * ((v : ℝ) - 4) ≤
      profileCoordinateDispersion (sourceScaleProfile d v x) d := by
  obtain ⟨b₁, b₂, _, hLow, hHigh, hGap⟩ := hSeparation
  have hvR : (5 : ℝ) ≤ v := by exact_mod_cast hv
  have hGapNonneg : 0 ≤ (cP * a₃ / 2) * ((v : ℝ) - 4) :=
    mul_nonneg (div_nonneg hs (by norm_num)) (by linarith)
  have h := pairDispersion_integer_two_tail_bound
    (fun a => dyadicProfilePartOrder (sourceScaleProfile d v x) d ((sourceScaleProfile d v x).part a))
    (div_nonneg hδ (by norm_num)) hc₀ hGapNonneg hLow hHigh hGap
  change _ ≤ profileCoordinateDispersion (sourceScaleProfile d v x) d at h
  convert h using 1
  ring

theorem eventually_source_K2_profile_dispersion_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hClower : 0 < Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ, ∀ x : Fin n → ℂ,
      x ∈ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))ᶜ →
      (2 * ((1 / 65536) * a₃ / 4) ^ 2 * ((1 / 4608) * a₃ / 16384)) *
        Real.rpow (d : ℝ) ((1 / 4608) * a₃ / 16) ≤
          profileCoordinateDispersion (sourceScaleProfile d u x) d := by
  filter_upwards [eventually_source_LLTTY_package_uniform ha hSmall hClower σ] with n hn
  intro d hBand L hL u x hx hK2
  exact source_K2_profile_dispersion (by positivity) (by positivity) x
    ((hn d hBand L hL).spread_branches u x hx) hK2

theorem eventually_source_Pv_profile_dispersion_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hClower : 0 < Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ v : ℕ, 5 ≤ v →
      ∀ (ρ δ : ℝ), ρ ≤ Real.rpow (d : ℝ) (-(v : ℝ)) → 0 < δ →
      δ ≤ 36 * (1 / 65536) * a₃ →
      (1 / 65536) * a₃ * ((v : ℝ) - 4) ≥ 2 * Real.logb 2 d +
        2 * Real.logb 2 (72 * Real.sqrt d / δ) + 2 - Real.logb 2 ((1 / 65536) * a₃) →
      ∀ x : Fin n → ℂ, x ∈ sourceHighHeightFamily n d L a₃ (1 / 65536) v →
      ∀ c : ℂ, δ * n ≤ ((Finset.univ.filter (fun i => ‖x i - c‖ ≤ ρ)).card : ℝ) →
      (δ * (((1 / 65536) * a₃ / 4)) * ((1 / 65536) * a₃) / 36) * ((v : ℝ) - 4) ≤
        profileCoordinateDispersion (sourceScaleProfile d v x) d := by
  filter_upwards [eventually_source_LLTTY_package_uniform ha hSmall hClower σ] with n hn
  intro d hBand L hL v hv ρ δ hρ hδ hδUpper hSep x hx c hCluster
  exact source_Pv_profile_dispersion hδ.le (by positivity) (by positivity) hv x
    ((hn d hBand L hL).clustered_height v hv ρ hρ δ hδ hδUpper hSep x hx c hCluster)

end CircularLaw
