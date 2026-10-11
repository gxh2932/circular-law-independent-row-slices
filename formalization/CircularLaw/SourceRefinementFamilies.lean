import CircularLaw.GradualRefinementDichotomy
import CircularLaw.AlmostConstantRanks
import CircularLaw.LowerBandEventually

/-!
# The literal spread and high-height gradual families

The families retain the actual source definitions: spread coordinate
mass for `Ku`, and mass of parts above the exponentially growing height
threshold for `Pu`. The one-step dichotomy for `Ku` is proved from the
gradual-class hypotheses. The multi-scale `Pu` conclusion is separate.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def sourceSpreadFamily (n d L : ℕ) (a₃ cK : ℝ) (u : ℕ) : Set (Fin n → ℂ) :=
  {x | x ∈ sourceGradual n d L a₃ ∧ cK * (thirdSteepScale n a₃ : ℝ) ≤
    (spreadCoordinates (fun i => canonicalApprox (d ^ u) (x i))
      ((d : ℝ) / (d ^ u : ℕ))).card}

def highHeightCoordinates {n : ℕ} (y : Fin n → ℂ) (δ H : ℝ) : Finset (Fin n) :=
  (Finset.univ.filter (fun q : Bool × Fin (n + 2) =>
    H ≤ ((taggedValues y δ q).card : ℝ))).biUnion (taggedPart y δ)

def sourceHeightThreshold (a₃ cP : ℝ) (u : ℕ) : ℝ :=
  cP * a₃ * Real.rpow 2 (cP * ((u : ℝ) - 4) * a₃)

def sourceHighHeightFamily (n d L : ℕ) (a₃ cP : ℝ) (u : ℕ) : Set (Fin n → ℂ) :=
  {x | x ∈ sourceGradual n d L a₃ ∧ cP * (thirdSteepScale n a₃ : ℝ) ≤
    (highHeightCoordinates (fun i => canonicalApprox (d ^ u) (x i))
      ((d : ℝ) / (d ^ u : ℕ)) (sourceHeightThreshold a₃ cP u)).card}

theorem sourceSpreadFamily_subset {n d L u : ℕ} (a₃ cK : ℝ) :
    sourceSpreadFamily n d L a₃ cK u ⊆ sourceGradual n d L a₃ := fun _ h => h.1

theorem sourceHighHeightFamily_subset {n d L u : ℕ} (a₃ cP : ℝ) :
    sourceHighHeightFamily n d L a₃ cP u ⊆ sourceGradual n d L a₃ := fun _ h => h.1

theorem highHeightCoordinates_eq_univ_of_le_one {n : ℕ} (y : Fin n → ℂ)
    (δ : ℝ) {H : ℝ} (hH : H ≤ 1) : highHeightCoordinates y δ H = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  obtain ⟨q, hi⟩ := taggedParts_cover y δ i
  have hHeight : 0 < (taggedValues y δ q).card := Finset.card_pos.mpr
    ((levelPart_nonempty_iff y q.2.val _ (taggedValues_subset y δ q)).mp ⟨i, hi⟩)
  have hHeightR : (1 : ℝ) ≤ (taggedValues y δ q).card := by exact_mod_cast hHeight
  exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_filter.mpr
    ⟨Finset.mem_univ q, hH.trans hHeightR⟩, hi⟩

theorem sourceHighHeightFamily_eq_gradual_of_small_threshold {n d L u : ℕ} {a₃ cP : ℝ}
    (hThird : thirdSteepScale n a₃ ≤ n) (hc : cP ≤ 1)
    (hHeight : sourceHeightThreshold a₃ cP u ≤ 1) :
    sourceHighHeightFamily n d L a₃ cP u = sourceGradual n d L a₃ := by
  apply Set.Subset.antisymm (sourceHighHeightFamily_subset a₃ cP)
  intro x hx
  refine ⟨hx, ?_⟩
  rw [highHeightCoordinates_eq_univ_of_le_one _ _ hHeight, Finset.card_univ, Fintype.card_fin]
  have hThirdR : (thirdSteepScale n a₃ : ℝ) ≤ n := by exact_mod_cast hThird
  nlinarith [Nat.cast_nonneg (thirdSteepScale n a₃) (α := ℝ)]

theorem source_gradual_one_step_families {n d L u : ℕ} {a₃ cK : ℝ}
    (hn : 2 ≤ n) (hd : 3 ≤ d) (hu : 4 ≤ u)
    (hr : 0 < thirdSteepScale n a₃) (hrn : thirdSteepScale n a₃ ≤ n)
    (hc : cK ≤ 1 / 4608) (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    x ∈ sourceSpreadFamily n d L a₃ cK u ∪ sourceSpreadFamily n d L a₃ cK (u + 1) ∨
      (thirdSteepScale n a₃ : ℝ) / 656 ≤
        (shrinkingCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
          (fun i => canonicalApprox (d ^ u) (x i))).card := by
  have hMass : cK * (thirdSteepScale n a₃ : ℝ) ≤ (thirdSteepScale n a₃ : ℝ) / 4608 := by
    have h := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (thirdSteepScale n a₃) : (0 : ℝ) ≤ _)
    nlinarith
  rcases source_gradual_scale_spread_or_shrinking hn hd hu hr hrn x hx with hCoarse | hFine | hShrink
  · exact Or.inl (Or.inl ⟨hx, hMass.trans (by linarith)⟩)
  · exact Or.inl (Or.inr ⟨hx, hMass.trans hFine⟩)
  · exact Or.inr hShrink

theorem source_gradual_shrinking_of_not_families {n d L u : ℕ} {a₃ cK : ℝ}
    (hn : 2 ≤ n) (hd : 3 ≤ d) (hu : 4 ≤ u)
    (hr : 0 < thirdSteepScale n a₃) (hrn : thirdSteepScale n a₃ ≤ n)
    (hc : cK ≤ 1 / 4608) (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃)
    (hCoarse : x ∉ sourceSpreadFamily n d L a₃ cK u)
    (hFine : x ∉ sourceSpreadFamily n d L a₃ cK (u + 1)) :
    (thirdSteepScale n a₃ : ℝ) / 656 ≤
      (shrinkingCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
        (fun i => canonicalApprox (d ^ u) (x i))).card := by
  rcases source_gradual_one_step_families hn hd hu hr hrn hc x hx with hFamily | hShrink
  · rcases hFamily with hC | hF
    · exact (hCoarse hC).elim
    · exact (hFine hF).elim
  · exact hShrink

theorem eventually_source_gradual_one_step_uniform {a₃ cK C : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hc : cK ≤ 1 / 4608) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → ∀ L u : ℕ, 4 ≤ u →
      ∀ x ∈ sourceGradual n d L a₃,
        x ∈ sourceSpreadFamily n d L a₃ cK u ∪ sourceSpreadFamily n d L a₃ cK (u + 1) ∨
          (thirdSteepScale n a₃ : ℝ) / 656 ≤
            (shrinkingCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
              (fun i => canonicalApprox (d ^ u) (x i))).card := by
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop ⌈2 / a₃⌉₊,
    eventually_degree_property_uniform hC (eventually_ge_atTop 3)] with n hn hSize hDegree
  intro d hLower L u hu x hx
  have hSizeR : 2 ≤ a₃ * (n : ℝ) := by
    have hN : (⌈2 / a₃⌉₊ : ℝ) ≤ n := by exact_mod_cast hSize
    have h := (Nat.le_ceil (2 / a₃)).trans hN
    have hMul := (div_le_iff₀ ha).mp h
    nlinarith
  have hThird := (thirdSteepScale_bounds ha hSizeR).1
  have hThirdN : thirdSteepScale n a₃ ≤ n := by
    have h := thirdSteepScale_half (n := n) ha.le haHalf
    omega
  exact source_gradual_one_step_families hn (hDegree d hLower) hu hThird hThirdN hc x hx

end CircularLaw
