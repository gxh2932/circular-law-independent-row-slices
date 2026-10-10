import CircularLaw.ProfileCutoffProduct
import CircularLaw.CanonicalClassEntropy
import CircularLaw.SourceRefinementFamilies

/-!
# The K1 estimate for the literal gradual spread family

The coordinate spread condition is transported to the actual ordered
canonical profile. The large-part alternative then gives exponential
degree decay of the source height/weight product. The floor in `n3`
is controlled by a finite dimension threshold, uniform in every scale
and codimension. The actual class entropy consequence is included.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def sourceScaleProfile {n : ℕ} (d u : ℕ) (x : Fin n → ℂ) :
    RowProfile (Fin n) (Fin (Fintype.card
      (CanonicalLabel (fun i => canonicalApprox (d ^ u) (x i)) ((d : ℝ) / (d ^ u : ℕ))))) :=
  orderedCanonicalRowProfile (fun i => canonicalApprox (d ^ u) (x i)) ((d : ℝ) / (d ^ u : ℕ))

theorem canonicalCoordinateLabel_spread_iff {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (i : Fin n) :
    (canonicalCoordinateLabel y δ i).val.1 = true ↔ i ∈ spreadCoordinates y δ := by
  constructor
  · intro hSpread
    have hi := canonicalCoordinateLabel_mem y δ i
    have hPart : i ∈ spreadPart y (canonicalCoordinateLabel y δ i).val.2.val δ := by
      simpa only [taggedPart, taggedValues, spreadPart, hSpread, ↓reduceIte] using hi
    exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_range.mpr
      (canonicalCoordinateLabel y δ i).val.2.isLt, hPart⟩
  · intro hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    let q : CanonicalLabel y δ := ⟨(true, ⟨j, Finset.mem_range.mp hj⟩), ⟨i, hij⟩⟩
    have hLabel : canonicalCoordinateLabel y δ i = q :=
      (canonicalCoordinateLabel_eq_iff y δ i q).mpr hij
    rw [hLabel]

theorem orderedCanonical_spread_mass {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    profileSelectedMass (orderedCanonicalRowProfile y δ)
      (profileSpreadParts (orderedCanonicalRowProfile y δ)) = (spreadCoordinates y δ).card := by
  rw [profileSelectedMass_eq_coordinate_card]
  apply congrArg (fun S : Finset (Fin n) => (S.card : ℝ))
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, profileSpreadParts,
    orderedCanonicalRowProfile, Equiv.apply_symm_apply]
  exact canonicalCoordinateLabel_spread_iff y δ i

theorem thirdSteepScale_three_quarters {n : ℕ} {a₃ : ℝ}
    (hSize : 4 ≤ a₃ * (n : ℝ)) :
    3 * a₃ * (n : ℝ) / 4 ≤ (thirdSteepScale n a₃ : ℝ) := by
  have hFloor := Nat.lt_floor_add_one (a₃ * (n : ℝ))
  change _ ≤ (⌊a₃ * (n : ℝ)⌋₊ : ℝ)
  linarith

theorem sourceSpreadFamily_profile_mass {n d L u : ℕ} {a₃ cK : ℝ}
    (x : Fin n → ℂ) (hx : x ∈ sourceSpreadFamily n d L a₃ cK u) :
    cK * (thirdSteepScale n a₃ : ℝ) ≤
      profileSelectedMass (sourceScaleProfile d u x) (profileSpreadParts (sourceScaleProfile d u x)) := by
  dsimp only [sourceScaleProfile]
  rw [orderedCanonical_spread_mass]
  exact hx.2

theorem source_K1_product_bound {n d L u : ℕ} {a₃ cK : ℝ}
    (hn : 0 < n) (hd : 0 < d) (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2)
    (hcK : 0 ≤ cK) (hcKUpper : cK ≤ 1 / 4608) (hSize : 4 ≤ a₃ * (n : ℝ))
    (x : Fin n → ℂ) (hx : x ∈ sourceSpreadFamily n d L a₃ cK u)
    (hK1 : (n : ℝ) - cK * (thirdSteepScale n a₃ : ℝ) / 4 ≤
      profileSelectedMass (sourceScaleProfile d u x)
        (profileCutoffParts (sourceScaleProfile d u x) d (cK * a₃ / 16))) :
    (∏ q, (((sourceScaleProfile d u x).height q : ℝ) /
      truncatedProfileWeight (sourceScaleProfile d u x) d q) ^
        profilePartSize (sourceScaleProfile d u x) q) ≤
      Real.rpow (d : ℝ) (-(cK * a₃ / 32) * n) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let P := sourceScaleProfile d u x
  let κ := cK * a₃ / 16
  let R := cK * (thirdSteepScale n a₃ : ℝ)
  have hκ : 0 ≤ κ := div_nonneg (mul_nonneg hcK ha.le) (by norm_num)
  have hκUpper : κ ≤ 1 / 3 := by
    have hProduct := mul_le_mul hcKUpper haHalf ha.le (by norm_num : (0 : ℝ) ≤ 1 / 4608)
    dsimp only [κ]
    nlinarith
  have hTotal := profileSelectedMass_add_compl P (profileCutoffParts P d κ)
  rw [Fintype.card_fin] at hTotal
  have hSmall : profileSelectedMass P (profileCutoffParts P d κ)ᶜ ≤ R / 4 := by
    change (n : ℝ) - R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ) at hK1
    linarith
  have hProduct := profile_K1_product_bound P hd hκ hκUpper
    (sourceSpreadFamily_profile_mass x hx) hSmall
  rw [Fintype.card_fin] at hProduct
  have hThird := mul_le_mul_of_nonneg_left (thirdSteepScale_three_quarters hSize) hcK
  have hExponent : κ * (n : ℝ) - R / 8 ≤ -(cK * a₃ / 32) * n := by
    dsimp only [κ, R]
    nlinarith
  exact hProduct.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd) hExponent)

theorem source_K1_class_weighted_dispersion {n d L u : ℕ} {a₃ cK : ℝ}
    (hn : 0 < n) (hd : 0 < d) (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2)
    (hcK : 0 ≤ cK) (hcKUpper : cK ≤ 1 / 4608) (hSize : 4 ≤ a₃ * (n : ℝ))
    (A : Set (Fin n → ℂ)) (x : Fin n → ℂ) (hx : x ∈ sourceSpreadFamily n d L a₃ cK u)
    (hK1 : (n : ℝ) - cK * (thirdSteepScale n a₃ : ℝ) / 4 ≤
      profileSelectedMass (sourceScaleProfile d u x)
        (profileCutoffParts (sourceScaleProfile d u x) d (cK * a₃ / 16)))
    {c K : ℝ} (hc : 0 < c) (hK : (n : ℝ) / 2 ≤ K) :
    (Nat.card (CoordinateMultisetClassIn A (fun i => canonicalApprox (d ^ u) (x i))) : ℝ) *
      (∏ q, (truncatedProfileWeight (sourceScaleProfile d u x) d q ^
        profilePartSize (sourceScaleProfile d u x) q)⁻¹) *
      Real.exp (-c * K * pairDispersion (fun a =>
        dyadicWeight (truncatedProfileWeight (sourceScaleProfile d u x) d
          ((sourceScaleProfile d u x).part a)))) ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) *
        Real.rpow (d : ℝ) (-(cK * a₃ / 32) * n) := by
  have hEntropy := orderedCanonicalClassIn_weighted_dispersion hn A
    (fun i => canonicalApprox (d ^ u) (x i)) ((d : ℝ) / (d ^ u : ℕ)) hd hc hK
  exact hEntropy.trans (mul_le_mul_of_nonneg_left
    (source_K1_product_bound hn hd ha haHalf hcK hcKUpper hSize x hx hK1) (Real.exp_nonneg _))

theorem eventually_source_K1_product_uniform {a₃ cK C : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hcK : 0 ≤ cK)
    (hcKUpper : cK ≤ 1 / 4608) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → ∀ L u : ℕ,
      ∀ x : Fin n → ℂ, x ∈ sourceSpreadFamily n d L a₃ cK u →
      (n : ℝ) - cK * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d (cK * a₃ / 16)) →
      (∏ q, (((sourceScaleProfile d u x).height q : ℝ) /
        truncatedProfileWeight (sourceScaleProfile d u x) d q) ^
          profilePartSize (sourceScaleProfile d u x) q) ≤
        Real.rpow (d : ℝ) (-(cK * a₃ / 32) * n) := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈4 / a₃⌉₊,
    eventually_degree_property_uniform hC (eventually_ge_atTop 1)] with n hn hSize hDegree
  intro d hLower L u x hx hK1
  have hSizeR : 4 ≤ a₃ * (n : ℝ) := by
    have hN : (⌈4 / a₃⌉₊ : ℝ) ≤ n := by exact_mod_cast hSize
    have h := (div_le_iff₀ ha).mp ((Nat.le_ceil (4 / a₃)).trans hN)
    nlinarith
  exact source_K1_product_bound hn (hDegree d hLower) ha haHalf hcK hcKUpper hSizeR x hx hK1

end CircularLaw
