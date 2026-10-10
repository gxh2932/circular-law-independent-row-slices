import CircularLaw.ClassRowEnergy
import CircularLaw.SteepNetCardinalityFinite

/-!
# The source class energies in all structural branches

The retained row count is exactly `n-L`, for either admissible
codimension. The K1 product decay, K2 degree-power dispersion and
clustered-Pv dispersion are inserted into the actual canonical class
energy. All finite row-count conditions are discharged uniformly in
the standing degree band.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem source_kernel_retained_rows_count {n d L : ℕ} (h : SourceKernelConditions n d)
    (hL : IsKernelCodimension n d L) :
    0 < n - L ∧ n - L ≤ n ∧ (n - L) + L = n ∧ (n : ℝ) / 2 ≤ (n - L : ℕ) := by
  have hFinite := source_kernel_dimension_twice_degree h
  have hCubic : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hFinite.2.1 (by decide : 3 ≤ 4))).trans
      h.dimension_fourth
  have hBounds := kernelCodimension_quotient_bounds hFinite.2.1 hCubic hL
  have hLn : L ≤ n := hBounds.2.1.trans (Nat.div_le_self n (d ^ 3))
  have hPower : 2 ≤ d ^ 3 := by
    have hd : 2 ≤ d := by have hLarge := h.degree_large; omega
    have h := Nat.pow_le_pow_left hd 3
    norm_num at h
    omega
  have hScaled : L * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_right (d ^ 3) hBounds.2.1).trans (Nat.div_mul_le_self n (d ^ 3))
  have hTwice : 2 * L ≤ n := by nlinarith [Nat.mul_le_mul_left L hPower]
  refine ⟨by omega, Nat.sub_le _ _, Nat.sub_add_cancel hLn, ?_⟩
  rw [Nat.cast_sub hLn]
  have hReal : (2 : ℝ) * L ≤ n := by exact_mod_cast hTwice
  linarith

theorem source_K2_class_row_energy {n d K L u : ℕ} {a₃ cK c₀ c₁ C : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hRows : K + L = n) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (A : Set (Fin n → ℂ)) (x : Fin n → ℂ)
    (hBranch : SourceSpreadPackageConclusions d u x a₃ cK c₀ c₁ C)
    (hK2 : cK * (thirdSteepScale n a₃ : ℝ) / 4 ≤
      profileSelectedMass (sourceScaleProfile d u x)
        (profileCutoffParts (sourceScaleProfile d u x) d (cK * a₃ / 16))ᶜ)
    {c : ℝ} (hc : 0 < c) (hK : (n : ℝ) / 2 ≤ K) :
    canonicalClassRowEnergy A (fun i => canonicalApprox (d ^ u) (x i))
      ((d : ℝ) / (d ^ u : ℕ)) d K c ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 4)) * n) * (d : ℝ) ^ n *
        ((n : ℝ) * Real.sqrt d) ^ L *
          Real.exp (-(c / 2) * (K : ℝ) *
            ((2 * c₀ ^ 2 * c₁) * Real.rpow (d : ℝ) (cK * a₃ / 16))) :=
  canonicalClassRowEnergy_dispersion_lower_bound hn hd hRows A
    (fun i => canonicalApprox (d ^ u) (x i)) ((d : ℝ) / (d ^ u : ℕ)) hc hK
    (source_K2_profile_dispersion hc₀ hc₁ x hBranch hK2)

theorem source_Pv_class_row_energy {n d K L v : ℕ} {a₃ cP δ c₀ : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hRows : K + L = n)
    (hδ : 0 ≤ δ) (hc₀ : 0 ≤ c₀) (hs : 0 ≤ cP * a₃) (hv : 5 ≤ v)
    (A : Set (Fin n → ℂ)) (x : Fin n → ℂ)
    (hSeparation : SourceClusterSeparationConclusions d v x a₃ cP δ c₀)
    {c : ℝ} (hc : 0 < c) (hK : (n : ℝ) / 2 ≤ K) :
    canonicalClassRowEnergy A (fun i => canonicalApprox (d ^ v) (x i))
      ((d : ℝ) / (d ^ v : ℕ)) d K c ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 4)) * n) * (d : ℝ) ^ n *
        ((n : ℝ) * Real.sqrt d) ^ L *
          Real.exp (-(c / 2) * (K : ℝ) * ((δ * c₀ * (cP * a₃) / 36) * ((v : ℝ) - 4))) :=
  canonicalClassRowEnergy_dispersion_lower_bound hn hd hRows A
    (fun i => canonicalApprox (d ^ v) (x i)) ((d : ℝ) / (d ^ v : ℕ)) hc hK
    (source_Pv_profile_dispersion hδ hc₀ hs hv x hSeparation)

theorem eventually_source_K1_class_row_energy_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hClower : 0 < Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ, ∀ A : Set (Fin n → ℂ),
      ∀ x : Fin n → ℂ, x ∈ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (n : ℝ) - (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16)) →
      ∀ c : ℝ, 0 < c →
      canonicalClassRowEnergy A (fun i => canonicalApprox (d ^ u) (x i))
        ((d : ℝ) / (d ^ u : ℕ)) d (n - L) c ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) *
        Real.rpow (d : ℝ) (-((1 / 4608) * a₃ / 32) * n) * ((n : ℝ) * Real.sqrt d) ^ L := by
  filter_upwards [eventually_source_K1_product_uniform (cK := 1 / 4608)
    ha haHalf (by norm_num) (by norm_num) hClower,
    eventually_source_kernel_conditions_uniform hClower (1 + σ)] with n hProduct hConditions
  intro d hBand L hL u A x hx hK1 c hc
  have h := hConditions d hBand.1 hBand.2
  have hFinite := source_kernel_dimension_twice_degree h
  have hRows := source_kernel_retained_rows_count h hL
  apply (canonicalClassRowEnergy_product_bound hFinite.1 hFinite.2.1 hRows.2.2.1 A
    (fun i => canonicalApprox (d ^ u) (x i)) ((d : ℝ) / (d ^ u : ℕ)) hc hRows.2.2.2).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hProduct d hBand.1 L u x hx hK1) (Real.exp_nonneg _))
    (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)) L)

theorem eventually_source_K2_class_row_energy_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hClower : 0 < Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ, ∀ A : Set (Fin n → ℂ),
      ∀ x : Fin n → ℂ, x ∈ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))ᶜ →
      ∀ c : ℝ, 0 < c →
      canonicalClassRowEnergy A (fun i => canonicalApprox (d ^ u) (x i))
        ((d : ℝ) / (d ^ u : ℕ)) d (n - L) c ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 4)) * n) * (d : ℝ) ^ n *
        ((n : ℝ) * Real.sqrt d) ^ L *
          Real.exp (-(c / 2) * ((n - L : ℕ) : ℝ) *
            ((2 * ((1 / 65536) * a₃ / 4) ^ 2 * ((1 / 4608) * a₃ / 16384)) *
              Real.rpow (d : ℝ) ((1 / 4608) * a₃ / 16))) := by
  filter_upwards [eventually_source_LLTTY_package_uniform ha hSmall hClower σ,
    eventually_source_kernel_conditions_uniform hClower (1 + σ)] with n hPackage hConditions
  intro d hBand L hL u A x hx hK2 c hc
  have h := hConditions d hBand.1 hBand.2
  have hFinite := source_kernel_dimension_twice_degree h
  have hRows := source_kernel_retained_rows_count h hL
  exact source_K2_class_row_energy hFinite.1 hFinite.2.1 hRows.2.2.1 (by positivity) (by positivity)
    A x ((hPackage d hBand L hL).spread_branches u x hx) hK2 hc hRows.2.2.2

theorem eventually_source_Pv_class_row_energy_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hClower : 0 < Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ v : ℕ, 5 ≤ v →
      ∀ (ρ δ : ℝ), ρ ≤ Real.rpow (d : ℝ) (-(v : ℝ)) → 0 < δ →
      δ ≤ 36 * (1 / 65536) * a₃ →
      (1 / 65536) * a₃ * ((v : ℝ) - 4) ≥ 2 * Real.logb 2 d +
        2 * Real.logb 2 (72 * Real.sqrt d / δ) + 2 - Real.logb 2 ((1 / 65536) * a₃) →
      ∀ A : Set (Fin n → ℂ), ∀ x : Fin n → ℂ,
      x ∈ sourceHighHeightFamily n d L a₃ (1 / 65536) v →
      ∀ c₀ : ℂ, δ * n ≤ ((Finset.univ.filter (fun i => ‖x i - c₀‖ ≤ ρ)).card : ℝ) →
      ∀ c : ℝ, 0 < c →
      canonicalClassRowEnergy A (fun i => canonicalApprox (d ^ v) (x i))
        ((d : ℝ) / (d ^ v : ℕ)) d (n - L) c ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 4)) * n) * (d : ℝ) ^ n *
        ((n : ℝ) * Real.sqrt d) ^ L * Real.exp (-(c / 2) * ((n - L : ℕ) : ℝ) *
          ((δ * ((1 / 65536) * a₃ / 4) * ((1 / 65536) * a₃) / 36) * ((v : ℝ) - 4))) := by
  filter_upwards [eventually_source_LLTTY_package_uniform ha hSmall hClower σ,
    eventually_source_kernel_conditions_uniform hClower (1 + σ)] with n hPackage hConditions
  intro d hBand L hL v hv ρ δ hρ hδ hδUpper hSep A x hx c₀ hCluster c hc
  have h := hConditions d hBand.1 hBand.2
  have hFinite := source_kernel_dimension_twice_degree h
  have hRows := source_kernel_retained_rows_count h hL
  exact source_Pv_class_row_energy hFinite.1 hFinite.2.1 hRows.2.2.1 hδ.le (by positivity)
    (by positivity) hv A x
    ((hPackage d hBand L hL).clustered_height v hv ρ hρ δ hδ hδUpper hSep x hx c₀ hCluster)
    hc hRows.2.2.2

end CircularLaw
