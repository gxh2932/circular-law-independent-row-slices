import CircularLaw.SourceK2Separation
import CircularLaw.SourcePvSeparation
import CircularLaw.UniformGradualClassCount

/-!
# The complete deterministic LLTTY package

All five manuscript conclusions use the literal normalized gradual class,
spread and high-height families, canonical approximations and profiles.
The common constants are `cK=1/4608`, `cP=1/65536`, `C=4096`,
`c0=cP*a3/4`, and `c1=cK*a3/16384`. The admissible density range is
`0<a3<=1/65536`. One dimension threshold applies simultaneously to both
codimensions and all scales in the standing lower degree band.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology Nat

namespace CircularLaw

/-- Part (iv) with the same constants used in the other four parts. -/
def SourceSpreadPackageConclusions {n : ℕ} (d u : ℕ) (x : Fin n → ℂ)
    (a₃ cK c₀ c₁ C : ℝ) : Prop :=
  let P := sourceScaleProfile d u x
  let κ := cK * a₃ / 16
  let R := cK * (thirdSteepScale n a₃ : ℝ)
  R ≤ profileSelectedMass P (profileSpreadParts P) ∧
    ((n : ℝ) - R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ) ∨
      R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ)ᶜ) ∧
    (((n : ℝ) - R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ)) →
      (∏ q, (P.height q : ℝ) ^ profilePartSize P q) *
        (∏ q, (truncatedProfileWeight P d q ^ profilePartSize P q)⁻¹) ≤
          C ^ n * Real.rpow (d : ℝ) (-c₁ * n)) ∧
    ((R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ)ᶜ) →
      ∃ b₁ b₂ : ℤ, b₁ ≤ b₂ ∧
        c₀ ≤ uniformProbability (fun i => dyadicProfilePartOrder P d (P.part i) ≤ b₁) ∧
        c₀ ≤ uniformProbability (fun i => b₂ ≤ dyadicProfilePartOrder P d (P.part i)) ∧
        c₁ * Real.rpow (d : ℝ) κ ≤ (b₂ : ℝ) - b₁)

theorem source_spread_branch_common_constants {n d u : ℕ} {x : Fin n → ℂ}
    {a₃ cK c₀ C : ℝ} (hC : 1 ≤ C) (hTail : c₀ ≤ cK * a₃ / 32)
    (h : SourceSpreadBranchConclusions d u x a₃ cK) :
    SourceSpreadPackageConclusions d u x a₃ cK c₀ (cK * a₃ / 16384) C := by
  obtain ⟨hSpread, hEither, hProduct, hSeparation⟩ := h
  refine ⟨hSpread, hEither, ?_, ?_⟩
  · intro hMass
    apply (hProduct hMass).trans
    have hPow : 1 ≤ C ^ n := one_le_pow₀ hC
    have h := mul_le_mul_of_nonneg_right hPow
      (Real.rpow_nonneg (Nat.cast_nonneg d) (-(cK * a₃ / 16384) * n))
    simpa only [one_mul] using h
  · intro hMass
    obtain ⟨b₁, b₂, hOrder, hLow, hHigh, hGap⟩ := hSeparation hMass
    exact ⟨b₁, b₂, hOrder, hTail.trans hLow, hTail.trans hHigh, hGap⟩

/-- The five clauses of `prop:LLTTY-package`. The class-count fields retain
the displayed scale conditions. The cardinality and local-bin fields are
proved for all reference vectors, hence also every nonempty source class. -/
structure LLTTYPackageConclusions (n d L : ℕ) (a₃ cK cP c₀ c₁ C : ℝ) : Prop where
  kappa_range : 0 < cK * a₃ / 16 ∧ cK * a₃ / 16 < 1 / 3
  spread_subsets : ∀ u : ℕ, sourceSpreadFamily n d L a₃ cK u ⊆ sourceGradual n d L a₃
  height_subsets : ∀ u : ℕ, sourceHighHeightFamily n d L a₃ cP u ⊆ sourceGradual n d L a₃
  decomposition : ∀ v : ℕ, 5 ≤ v → sourceGradual n d L a₃ =
    (⋃ u ∈ Set.Icc 4 v, sourceSpreadFamily n d L a₃ cK u) ∪ sourceHighHeightFamily n d L a₃ cP v
  class_count : ∀ k : ℕ, 0 < k → (d : ℝ) ≤ Real.rpow (n : ℝ) (1 / 3) →
    (k : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) →
    (canonicalApproxFamily k (sourceGradual n d L a₃)).Finite ∧
    (coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))).Finite ∧
    (Nat.card {m : Multiset ℂ // m ∈
      coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))} : ℝ) ≤ Real.exp n
  restricted_class_count : ∀ k : ℕ, 0 < k → (d : ℝ) ≤ Real.rpow (n : ℝ) (1 / 3) →
    (k : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) →
    ∀ X : Set (Fin n → ℂ), X ⊆ sourceGradual n d L a₃ →
    (canonicalApproxFamily k X).Finite ∧
    (Nat.card {m : Multiset ℂ // m ∈
      coordinateMultisetClasses (canonicalApproxFamily k X)} : ℝ) ≤ Real.exp n
  class_cardinality : ∀ (k : ℕ) (X : Set (Fin n → ℂ)) (y : Fin n → ℂ),
    let P := orderedCanonicalRowProfile y ((d : ℝ) / k)
    (Nat.card (CoordinateMultisetClassIn (canonicalApproxFamily k X) y) : ℝ) ≤
      ((n)! : ℝ) / (∏ q, ((profilePartSize P q)! : ℝ)) *
        (∏ q, (P.height q : ℝ) ^ profilePartSize P q)
  factorial_compression : ∀ (y : Fin n → ℂ) (η : ℝ),
    ProfileBinFactorialCompression (orderedCanonicalRowProfile y η) d C
  small_bin_mass : ∀ (y : Fin n → ℂ) (η : ℝ) (b : ℤ)
    (S : Finset (Fin (Fintype.card (CanonicalLabel y η)))),
    S ⊆ dyadicProfileBinParts (orderedCanonicalRowProfile y η) d b →
    (∀ q ∈ S, (profilePartSize (orderedCanonicalRowProfile y η) q : ℝ) <
      Real.rpow (d : ℝ) (-(cK * a₃ / 16)) * n) →
    ((S.biUnion (fun q => taggedPart y η (canonicalEnumeration y η q).val)).card : ℝ) ≤
      C * Real.rpow (d : ℝ) (-(cK * a₃ / 16)) * n
  spread_branches : ∀ (u : ℕ) (x : Fin n → ℂ), x ∈ sourceSpreadFamily n d L a₃ cK u →
    SourceSpreadPackageConclusions d u x a₃ cK c₀ c₁ C
  clustered_height : ∀ v : ℕ, 5 ≤ v → ∀ ρ : ℝ, ρ ≤ Real.rpow (d : ℝ) (-(v : ℝ)) →
    ∀ δ : ℝ, 0 < δ → δ ≤ 36 * cP * a₃ →
    cP * a₃ * ((v : ℝ) - 4) ≥ 2 * Real.logb 2 d +
      2 * Real.logb 2 (72 * Real.sqrt d / δ) + 2 - Real.logb 2 (cP * a₃) →
    ∀ x : Fin n → ℂ, x ∈ sourceHighHeightFamily n d L a₃ cP v → ∀ c : ℂ,
    δ * n ≤ ((Finset.univ.filter (fun i => ‖x i - c‖ ≤ ρ)).card : ℝ) →
    SourceClusterSeparationConclusions d v x a₃ cP δ c₀

theorem eventually_source_LLTTY_package_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hLowerConstant : 0 < Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
      LLTTYPackageConclusions n d L a₃ (1 / 4608) (1 / 65536)
        ((1 / 65536) * a₃ / 4) ((1 / 4608) * a₃ / 16384) 4096 := by
  have haHalf : a₃ ≤ 1 / 2 := by linarith
  have hκ := source_Ku_branch_constants ha haHalf
    (by norm_num : (0 : ℝ) < 1 / 4608) (by norm_num : (1 / 4608 : ℝ) ≤ 1 / 4608)
  have hCommonTail : (1 / 65536) * a₃ / 4 ≤ (1 / 4608) * a₃ / 32 := by linarith
  filter_upwards [eventually_source_gradual_decomposition_absolute ha haHalf hLowerConstant,
    eventually_sourceGradualApproxClasses_exp_n_uniform ha hSmall hLowerConstant σ,
    eventually_restrictedGradualApproxClasses_exp_n_uniform ha hSmall hLowerConstant σ,
    eventually_source_Ku_branches_absolute ha haHalf hLowerConstant,
    eventually_source_Pv_cluster_separation_absolute ha haHalf hLowerConstant,
    eventually_degree_property_uniform hLowerConstant (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with n hDecomposition hCount hRestricted hSpread hCluster hDegree hn
  intro d hBand L hL
  have hd : 0 < d := hDegree d hBand.1
  refine ⟨⟨hκ.1, hκ.2.1⟩, (fun _ => sourceSpreadFamily_subset _ _),
    (fun _ => sourceHighHeightFamily_subset _ _), hDecomposition d hBand.1 L,
    (fun k hk _ hRange => hCount d hBand L hL k hk hRange),
    (fun k hk _ hRange => hRestricted d hBand L hL k hk hRange),
    (fun k X y => canonicalApprox_class_cardinality k X y ((d : ℝ) / k)),
    (fun y η => orderedCanonical_bin_factorial_compression hn y η hd), ?_, ?_, ?_⟩
  · intro y η b S hSubset hSizes
    apply (orderedCanonical_small_bin_cutoff hn y η hd b ((1 / 4608) * a₃ / 16) S
      hSubset hSizes).trans
    have hNonneg : 0 ≤ Real.rpow (d : ℝ) (-((1 / 4608) * a₃ / 16)) * n :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (Nat.cast_nonneg n)
    nlinarith
  · intro u x hx
    exact source_spread_branch_common_constants (by norm_num) hCommonTail (hSpread d hBand.1 L u x hx)
  · intro v hv ρ hρ δ hδ _ hSep x hx c hCoordinates
    exact hCluster d hBand.1 L v hv x hx c δ ρ hδ hρ hCoordinates hSep

/-- Full named manuscript proposition, strengthened to a fixed positive
range of `a3`. Choosing any one value in that range gives the absolute
constants in the paper. All constants precede sigma and the dimension,
degree, codimension, scales, classes and vectors. -/
def LLTTYDeterministicPackage : Prop :=
  ∃ a₀ cK cP C : ℝ, 0 < a₀ ∧ 0 < cK ∧ 0 < cP ∧ 1 ≤ C ∧
    ∀ a₃ : ℝ, 0 < a₃ → a₃ ≤ a₀ → ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ Clower : ℝ, 0 < Clower → ∀ σ : ℝ, 0 < σ → σ < 1 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand Clower σ n d →
          ∀ L : ℕ, IsKernelCodimension n d L → LLTTYPackageConclusions n d L a₃ cK cP c₀ c₁ C

theorem LLTTY_deterministic_package : LLTTYDeterministicPackage := by
  refine ⟨1 / 65536, 1 / 4608, 1 / 65536, 4096,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro a₃ ha hSmall
  refine ⟨(1 / 65536) * a₃ / 4, (1 / 4608) * a₃ / 16384,
    by positivity, by positivity, ?_⟩
  intro Clower hClower σ _ _
  exact eventually_atTop.mp (eventually_source_LLTTY_package_uniform ha hSmall hClower σ)

end CircularLaw
