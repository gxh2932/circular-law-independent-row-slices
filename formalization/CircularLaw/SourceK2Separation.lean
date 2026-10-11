import CircularLaw.SourceK1Product
import CircularLaw.ProfileK2Separation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The source K2 separated-order conclusion

Actual small-part coordinate mass gives two probability tails of mass
at least `cK*a3/32` and a gap at least `(cK*a3/16384)*d^kappa`.
The dimension and degree thresholds are uniform over every scale and
codimension. Together with K1 this proves part (iv) of the deterministic
LLTTY package in the standing manuscript setting.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

theorem source_K2_separation {n d u : ℕ} {a₃ cK : ℝ}
    (hn : 4 ≤ n) (hd : 0 < d) (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2)
    (hcK : 0 < cK) (hcKUpper : cK ≤ 1 / 4608) (hSize : 2 ≤ a₃ * (n : ℝ))
    (hPower : 1 ≤ (cK * a₃ / 16384) * Real.rpow (d : ℝ) (cK * a₃ / 16))
    (x : Fin n → ℂ)
    (hK2 : cK * (thirdSteepScale n a₃ : ℝ) / 4 ≤
      profileSelectedMass (sourceScaleProfile d u x)
        (profileCutoffParts (sourceScaleProfile d u x) d (cK * a₃ / 16))ᶜ) :
    ∃ b₁ b₂ : ℤ, b₁ ≤ b₂ ∧
      cK * a₃ / 32 ≤ uniformProbability (fun i =>
        dyadicProfilePartOrder (sourceScaleProfile d u x) d ((sourceScaleProfile d u x).part i) ≤ b₁) ∧
      cK * a₃ / 32 ≤ uniformProbability (fun i =>
        b₂ ≤ dyadicProfilePartOrder (sourceScaleProfile d u x) d ((sourceScaleProfile d u x).part i)) ∧
      (cK * a₃ / 16384) * Real.rpow (d : ℝ) (cK * a₃ / 16) ≤ (b₂ : ℝ) - b₁ := by
  let P := sourceScaleProfile d u x
  let κ := cK * a₃ / 16
  let R := cK * (thirdSteepScale n a₃ : ℝ)
  let D := Real.rpow (d : ℝ) κ
  let γ := cK * a₃ / 16384
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : 0 < D := Real.rpow_pos_of_pos hdR _
  have hThird := thirdSteepScale_bounds ha hSize
  have hR : 0 < R := mul_pos hcK (by exact_mod_cast hThird.1)
  have hThirdN : thirdSteepScale n a₃ ≤ n := by
    have h := thirdSteepScale_half (n := n) ha.le haHalf
    omega
  have hRn : R ≤ n := by
    have hcOne : cK ≤ 1 := by linarith
    have hMul := mul_le_mul_of_nonneg_right hcOne
      (Nat.cast_nonneg (thirdSteepScale n a₃) : (0 : ℝ) ≤ _)
    have hN : (thirdSteepScale n a₃ : ℝ) ≤ n := by exact_mod_cast hThirdN
    dsimp only [R]
    linarith
  have hGeometry := orderedCanonical_profile_order_geometry
    (fun i => canonicalApprox (d ^ u) (x i)) ((d : ℝ) / (d ^ u : ℕ))
  obtain ⟨b₁, b₂, hOrder, hLow, hHigh, hGap⟩ := profile_K2_quantile_separation hn P
    (orderedCanonicalCreationOrder _ _) hGeometry hd κ hR hRn hK2
  have hRLower := mul_le_mul_of_nonneg_left hThird.2.1 hcK.le
  have hTail : cK * a₃ / 32 ≤ (R / 16) / n := by
    apply (le_div_iff₀ hnR).mpr
    dsimp only [R]
    nlinarith
  have hCancel : Real.rpow (d : ℝ) (-κ) * D = 1 := by
    calc
      _ = Real.rpow (d : ℝ) (-κ + κ) := (Real.rpow_add hdR _ _).symm
      _ = 1 := by
        rw [neg_add_cancel]
        exact Real.rpow_zero _
  have hScaled : (R / 8) * D ≤ ((b₂ : ℝ) - b₁ + 1) * 512 * n := by
    calc
      _ ≤ (((b₂ : ℝ) - b₁ + 1) * (512 * Real.rpow (d : ℝ) (-κ) * n)) * D :=
        mul_le_mul_of_nonneg_right hGap hD.le
      _ = (((b₂ : ℝ) - b₁ + 1) * 512 * n) * (Real.rpow (d : ℝ) (-κ) * D) := by ring
      _ = _ := by rw [hCancel, mul_one]
  have hLowerScaled := mul_le_mul_of_nonneg_right hRLower hD.le
  have hGapN : (2 * γ * D) * n ≤ ((b₂ : ℝ) - b₁ + 1) * n := by
    dsimp only [γ, R] at *
    nlinarith only [hScaled, hLowerScaled]
  have hGapTwo := (mul_le_mul_iff_left₀ hnR).mp hGapN
  have hGapFinal : γ * D ≤ (b₂ : ℝ) - b₁ := by
    change 1 ≤ γ * D at hPower
    linarith
  exact ⟨b₁, b₂, hOrder, hTail.trans hLow, hTail.trans hHigh, hGapFinal⟩

theorem eventually_source_K2_separation_uniform {a₃ cK C : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hcK : 0 < cK)
    (hcKUpper : cK ≤ 1 / 4608) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → ∀ u : ℕ,
      ∀ x : Fin n → ℂ,
      cK * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d (cK * a₃ / 16))ᶜ →
      ∃ b₁ b₂ : ℤ, b₁ ≤ b₂ ∧
        cK * a₃ / 32 ≤ uniformProbability (fun i =>
          dyadicProfilePartOrder (sourceScaleProfile d u x) d ((sourceScaleProfile d u x).part i) ≤ b₁) ∧
        cK * a₃ / 32 ≤ uniformProbability (fun i =>
          b₂ ≤ dyadicProfilePartOrder (sourceScaleProfile d u x) d ((sourceScaleProfile d u x).part i)) ∧
        (cK * a₃ / 16384) * Real.rpow (d : ℝ) (cK * a₃ / 16) ≤ (b₂ : ℝ) - b₁ := by
  have hκ : 0 < cK * a₃ / 16 := by positivity
  have hγ : 0 < cK * a₃ / 16384 := by positivity
  have hLimit := (tendsto_rpow_atTop hκ).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  have hPower : ∀ᶠ d : ℕ in atTop,
      1 ≤ (cK * a₃ / 16384) * Real.rpow (d : ℝ) (cK * a₃ / 16) := by
    filter_upwards [hLimit.eventually_ge_atTop (1 / (cK * a₃ / 16384))] with d hd
    have h := (div_le_iff₀ hγ).mp hd
    simpa only [mul_comm] using h
  filter_upwards [eventually_ge_atTop 4, eventually_ge_atTop ⌈2 / a₃⌉₊,
    eventually_degree_property_uniform hC ((eventually_ge_atTop 1).and hPower)] with n hn hSize hDegree
  intro d hLower u x hK2
  have hSizeR : 2 ≤ a₃ * (n : ℝ) := by
    have hN : (⌈2 / a₃⌉₊ : ℝ) ≤ n := by exact_mod_cast hSize
    have h := (div_le_iff₀ ha).mp ((Nat.le_ceil (2 / a₃)).trans hN)
    nlinarith
  exact source_K2_separation hn (hDegree d hLower).1 ha haHalf hcK hcKUpper hSizeR
    (hDegree d hLower).2 x hK2

theorem source_Ku_branch_constants {a₃ cK : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hcK : 0 < cK) (hcKUpper : cK ≤ 1 / 4608) :
    0 < cK * a₃ / 16 ∧ cK * a₃ / 16 < 1 / 3 ∧
      0 < cK * a₃ / 32 ∧ 0 < cK * a₃ / 16384 := by
  have hProduct := mul_le_mul hcKUpper haHalf ha.le (by norm_num : (0 : ℝ) ≤ 1 / 4608)
  exact ⟨by positivity, by nlinarith, by positivity, by positivity⟩

/-- Literal spread mass, the two source mass alternatives, and both
conditional consequences, with a common positive decay/gap constant. -/
def SourceSpreadBranchConclusions {n : ℕ} (d u : ℕ) (x : Fin n → ℂ) (a₃ cK : ℝ) : Prop :=
  let P := sourceScaleProfile d u x
  let κ := cK * a₃ / 16
  let R := cK * (thirdSteepScale n a₃ : ℝ)
  R ≤ profileSelectedMass P (profileSpreadParts P) ∧
    ((n : ℝ) - R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ) ∨
      R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ)ᶜ) ∧
    (((n : ℝ) - R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ)) →
      (∏ q, (P.height q : ℝ) ^ profilePartSize P q) *
        (∏ q, (truncatedProfileWeight P d q ^ profilePartSize P q)⁻¹) ≤
          Real.rpow (d : ℝ) (-(cK * a₃ / 16384) * n)) ∧
    ((R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ)ᶜ) →
      ∃ b₁ b₂ : ℤ, b₁ ≤ b₂ ∧
        cK * a₃ / 32 ≤ uniformProbability (fun i => dyadicProfilePartOrder P d (P.part i) ≤ b₁) ∧
        cK * a₃ / 32 ≤ uniformProbability (fun i => b₂ ≤ dyadicProfilePartOrder P d (P.part i)) ∧
        (cK * a₃ / 16384) * Real.rpow (d : ℝ) κ ≤ (b₂ : ℝ) - b₁)

theorem eventually_source_Ku_branches_uniform {a₃ cK C : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hcK : 0 < cK)
    (hcKUpper : cK ≤ 1 / 4608) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → ∀ L u : ℕ,
      ∀ x : Fin n → ℂ, x ∈ sourceSpreadFamily n d L a₃ cK u →
        SourceSpreadBranchConclusions d u x a₃ cK := by
  filter_upwards [eventually_source_K1_product_uniform ha haHalf hcK.le hcKUpper hC,
    eventually_source_K2_separation_uniform ha haHalf hcK hcKUpper hC,
    eventually_degree_property_uniform hC (eventually_ge_atTop 1)] with n hK1 hK2 hDegree
  intro d hLower L u x hx
  dsimp only [SourceSpreadBranchConclusions]
  refine ⟨sourceSpreadFamily_profile_mass x hx, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using profileCutoff_mass_dichotomy
      (sourceScaleProfile d u x) d (cK * a₃ / 16) (cK * (thirdSteepScale n a₃ : ℝ))
  · intro hMass
    rw [profile_height_weight_product_factorization]
    have hProduct := hK1 d hLower L u x hx hMass
    have hCoefficient : -(cK * a₃ / 32) ≤ -(cK * a₃ / 16384) := by
      have h : 0 ≤ cK * a₃ := mul_nonneg hcK.le ha.le
      linarith
    exact hProduct.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hDegree d hLower)
      (mul_le_mul_of_nonneg_right hCoefficient (Nat.cast_nonneg n)))
  · exact hK2 d hLower u x

theorem eventually_source_Ku_branches_absolute {a₃ C : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → ∀ L u : ℕ,
      ∀ x : Fin n → ℂ, x ∈ sourceSpreadFamily n d L a₃ (1 / 4608) u →
        SourceSpreadBranchConclusions d u x a₃ (1 / 4608) :=
  eventually_source_Ku_branches_uniform ha haHalf (by norm_num) (by norm_num) hC

end CircularLaw
