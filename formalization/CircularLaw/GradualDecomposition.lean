import CircularLaw.GradualLevelAccumulation
import CircularLaw.LowHeightCoordinates

/-!
# Decomposition of the actual normalized gradual class

Avoiding every spread family through scale `v` forces the literal
high-height condition of `Pv`. The resulting equality is uniform in
the codimension and all `v >= 5`. Positive absolute constants up to
`cK = 1/4608` and `cP = 1/65536` are supplied by checked proofs.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem sourceHeightThreshold_after_four (a₃ cP : ℝ) (T : ℕ) :
    sourceHeightThreshold a₃ cP (4 + T) = cP * a₃ * Real.rpow 2 (cP * (T : ℝ) * a₃) := by
  unfold sourceHeightThreshold
  congr 1
  congr 1
  push_cast
  ring

theorem sourceHeightThreshold_nonneg {a₃ cP : ℝ} (ha : 0 ≤ a₃) (hc : 0 ≤ cP) (u : ℕ) :
    0 ≤ sourceHeightThreshold a₃ cP u :=
  mul_nonneg (mul_nonneg hc ha) (Real.rpow_nonneg (by norm_num) _)

theorem decomposition_low_height_mass_budget {n r T : ℕ} {a₃ cP : ℝ}
    (ha : 0 ≤ a₃) (hc : 0 ≤ cP) (hcUpper : cP ≤ 1 / 65536)
    (hThird : a₃ * (n : ℝ) / 2 ≤ (r : ℝ)) :
    16 * ((n : ℝ) * Real.rpow 2 (-(a₃ * (T : ℝ) / 5248))) *
      sourceHeightThreshold a₃ cP (4 + T) ≤ 32 * cP * (r : ℝ) := by
  have hScale : cP * (T : ℝ) * a₃ ≤ a₃ * (T : ℝ) / 5248 := by
    have hcRelax : cP ≤ 1 / 5248 := by linarith
    have h := mul_le_mul_of_nonneg_right hcRelax
      (mul_nonneg ha (Nat.cast_nonneg T : (0 : ℝ) ≤ T))
    nlinarith
  have hAdd : Real.rpow 2 (-(a₃ * (T : ℝ) / 5248)) * Real.rpow 2 (cP * (T : ℝ) * a₃) =
      Real.rpow 2 (-(a₃ * (T : ℝ) / 5248) + cP * (T : ℝ) * a₃) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
  have hPower : Real.rpow 2 (-(a₃ * (T : ℝ) / 5248)) *
      Real.rpow 2 (cP * (T : ℝ) * a₃) ≤ 1 := by
    rw [hAdd]
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show -(a₃ * (T : ℝ) / 5248) + cP * (T : ℝ) * a₃ ≤ 0 by linarith)
  have hCoefficient : 0 ≤ cP * a₃ * (n : ℝ) :=
    mul_nonneg (mul_nonneg hc ha) (Nat.cast_nonneg n)
  calc
    _ = 16 * (cP * a₃ * (n : ℝ)) *
        (Real.rpow 2 (-(a₃ * (T : ℝ) / 5248)) * Real.rpow 2 (cP * (T : ℝ) * a₃)) := by
      rw [sourceHeightThreshold_after_four]
      ring
    _ ≤ 16 * (cP * a₃ * (n : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left hPower (mul_nonneg (by norm_num) hCoefficient)
    _ ≤ 32 * cP * (r : ℝ) := by nlinarith

theorem source_gradual_high_height_of_avoiding_spread {n d L T : ℕ} {a₃ cK cP : ℝ}
    (hn : 2 ≤ n) (hd : 3 ≤ d) (hT : 0 < T) (ha : 0 < a₃)
    (hr : 0 < thirdSteepScale n a₃) (hrn : thirdSteepScale n a₃ ≤ n)
    (hThird : a₃ * (n : ℝ) / 2 ≤ thirdSteepScale n a₃)
    (hcK : cK ≤ 1 / 4608) (hcP : 0 < cP) (hcPUpper : cP ≤ 1 / 65536)
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃)
    (hAvoid : ∀ u : ℕ, 4 ≤ u → u ≤ 4 + T → x ∉ sourceSpreadFamily n d L a₃ cK u) :
    x ∈ sourceHighHeightFamily n d L a₃ cP (4 + T) := by
  obtain ⟨G, hG, hLevels⟩ := source_gradual_many_small_levels hn hd hT hr hrn hThird hcK x hx hAvoid
  let M := (n : ℝ) * Real.rpow 2 (-(a₃ * (T : ℝ) / 5248))
  let H := sourceHeightThreshold a₃ cP (4 + T)
  have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (by norm_num) _)
  have hH : 0 ≤ H := sourceHeightThreshold_nonneg ha.le hcP.le _
  have hMass := coordinates_mass_le_highHeight_add
    (fun i => canonicalApprox (d ^ (4 + T)) (x i))
    ((d : ℝ) / (d ^ (4 + T) : ℕ)) G hM hH hLevels
  have hBudget := decomposition_low_height_mass_budget ha.le hcP.le hcPUpper hThird (T := T)
  have hConstant : 33 * cP ≤ 3 / 2624 := by linarith
  have hScaled := mul_le_mul_of_nonneg_right hConstant
    (Nat.cast_nonneg (thirdSteepScale n a₃) : (0 : ℝ) ≤ _)
  refine ⟨hx, ?_⟩
  dsimp only [M, H] at hMass
  linarith

theorem source_gradual_decomposition {n d L v : ℕ} {a₃ cK cP : ℝ}
    (hn : 2 ≤ n) (hd : 3 ≤ d) (hv : 5 ≤ v) (ha : 0 < a₃)
    (hr : 0 < thirdSteepScale n a₃) (hrn : thirdSteepScale n a₃ ≤ n)
    (hThird : a₃ * (n : ℝ) / 2 ≤ thirdSteepScale n a₃)
    (hcK : cK ≤ 1 / 4608) (hcP : 0 < cP) (hcPUpper : cP ≤ 1 / 65536) :
    sourceGradual n d L a₃ =
      (⋃ u ∈ Set.Icc 4 v, sourceSpreadFamily n d L a₃ cK u) ∪
        sourceHighHeightFamily n d L a₃ cP v := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hExists : ∃ u : ℕ, 4 ≤ u ∧ u ≤ v ∧ x ∈ sourceSpreadFamily n d L a₃ cK u
    · obtain ⟨u, hu, huv, hxK⟩ := hExists
      exact Or.inl (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨⟨hu, huv⟩, hxK⟩⟩)
    · have hAvoid : ∀ u : ℕ, 4 ≤ u → u ≤ 4 + (v - 4) →
          x ∉ sourceSpreadFamily n d L a₃ cK u := by
        intro u hu huv hxK
        exact hExists ⟨u, hu, by omega, hxK⟩
      have hHeight := source_gradual_high_height_of_avoiding_spread hn hd
        (by omega : 0 < v - 4) ha hr hrn hThird hcK hcP hcPUpper x hx hAvoid
      have hIndex : 4 + (v - 4) = v := by omega
      rw [hIndex] at hHeight
      exact Or.inr hHeight
  · intro x hx
    rcases hx with hxK | hxP
    · obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hxK
      obtain ⟨huv, hMember⟩ := Set.mem_iUnion.mp hu
      exact hMember.1
    · exact hxP.1

theorem eventually_source_gradual_decomposition_uniform {a₃ cK cP C : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hcK : cK ≤ 1 / 4608)
    (hcP : 0 < cP) (hcPUpper : cP ≤ 1 / 65536) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → ∀ L v : ℕ, 5 ≤ v →
      sourceGradual n d L a₃ =
        (⋃ u ∈ Set.Icc 4 v, sourceSpreadFamily n d L a₃ cK u) ∪
          sourceHighHeightFamily n d L a₃ cP v := by
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop ⌈2 / a₃⌉₊,
    eventually_degree_property_uniform hC (eventually_ge_atTop 3)] with n hn hSize hDegree
  intro d hLower L v hv
  have hSizeR : 2 ≤ a₃ * (n : ℝ) := by
    have hN : (⌈2 / a₃⌉₊ : ℝ) ≤ n := by exact_mod_cast hSize
    have h := (Nat.le_ceil (2 / a₃)).trans hN
    have hMul := (div_le_iff₀ ha).mp h
    nlinarith
  have hThird := thirdSteepScale_bounds ha hSizeR
  have hThirdN : thirdSteepScale n a₃ ≤ n := by
    have h := thirdSteepScale_half (n := n) ha.le haHalf
    omega
  exact source_gradual_decomposition hn (hDegree d hLower) hv ha hThird.1 hThirdN hThird.2.1
    hcK hcP hcPUpper

theorem eventually_source_gradual_decomposition_absolute {a₃ C : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → ∀ L v : ℕ, 5 ≤ v →
      sourceGradual n d L a₃ =
        (⋃ u ∈ Set.Icc 4 v, sourceSpreadFamily n d L a₃ (1 / 4608) u) ∪
          sourceHighHeightFamily n d L a₃ (1 / 65536) v :=
  eventually_source_gradual_decomposition_uniform ha haHalf (by norm_num)
    (by norm_num) (by norm_num) hC

end CircularLaw
