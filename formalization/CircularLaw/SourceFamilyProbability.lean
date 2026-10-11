import CircularLaw.CanonicalFamilyProbability

/-!
# Actual gradual-family probability sums in the three source branches

Every represented class reference is an actual canonical approximation
of a member of the restricted source family. Thus the checked K1, K2
and clustered-Pv energy bounds discharge the class-energy input to the
whole-family probability sum. All conditioning, missing-row and net
cardinality costs remain explicit for the later parameter budgets.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def sourceK1ClassEnergyUpper (n d L : ℕ) (a₃ : ℝ) : ℝ :=
  Real.exp ((4096 + entropyPenaltyConstant (averagedProfileRate / 2)) * n) *
    Real.rpow (d : ℝ) (-((1 / 4608) * a₃ / 32) * n) * ((n : ℝ) * Real.sqrt d) ^ L

def sourceK2ClassEnergyUpper (n d L : ℕ) (a₃ : ℝ) : ℝ :=
  Real.exp ((4096 + entropyPenaltyConstant (averagedProfileRate / 4)) * n) * (d : ℝ) ^ n *
    ((n : ℝ) * Real.sqrt d) ^ L * Real.exp (-(averagedProfileRate / 2) * ((n - L : ℕ) : ℝ) *
      ((2 * ((1 / 65536) * a₃ / 4) ^ 2 * ((1 / 4608) * a₃ / 16384)) *
        Real.rpow (d : ℝ) ((1 / 4608) * a₃ / 16)))

def sourcePvClassEnergyUpper (n d L v : ℕ) (a₃ δ : ℝ) : ℝ :=
  Real.exp ((4096 + entropyPenaltyConstant (averagedProfileRate / 4)) * n) * (d : ℝ) ^ n *
    ((n : ℝ) * Real.sqrt d) ^ L * Real.exp (-(averagedProfileRate / 2) * ((n - L : ℕ) : ℝ) *
      ((δ * ((1 / 65536) * a₃ / 4) * ((1 / 65536) * a₃) / 36) * ((v : ℝ) - 4)))

theorem sourceK1ClassEnergyUpper_nonneg (n d L : ℕ) (a₃ : ℝ) :
    0 ≤ sourceK1ClassEnergyUpper n d L a₃ :=
  mul_nonneg (mul_nonneg (Real.exp_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg d) _))
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)) L)

theorem sourceK2ClassEnergyUpper_nonneg (n d L : ℕ) (a₃ : ℝ) :
    0 ≤ sourceK2ClassEnergyUpper n d L a₃ := by
  unfold sourceK2ClassEnergyUpper
  positivity

theorem sourcePvClassEnergyUpper_nonneg (n d L v : ℕ) (a₃ δ : ℝ) :
    0 ≤ sourcePvClassEnergyUpper n d L v a₃ δ := by
  unfold sourcePvClassEnergyUpper
  positivity

theorem canonicalApprox_class_energy_bound_of_family_bound {n : ℕ} (k d K : ℕ)
    (X : Set (Fin n → ℂ)) {E : ℝ}
    (hFamily : ∀ x ∈ X,
      canonicalClassRowEnergy (canonicalApproxFamily k X) (fun i => canonicalApprox k (x i))
        ((d : ℝ) / k) d K averagedProfileRate ≤ E)
    (m : CoordinateMultisetClassesOf (canonicalApproxFamily k X)) :
    canonicalClassRowEnergy (canonicalApproxFamily k X)
      (coordinateClassRepresentative (canonicalApproxFamily k X) m).val
        ((d : ℝ) / k) d K averagedProfileRate ≤ E := by
  obtain ⟨x, hx, hApprox⟩ := (coordinateClassRepresentative (canonicalApproxFamily k X) m).property
  rw [← hApprox]
  exact hFamily x hx

theorem eventually_source_K1_family_probability_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ,
      ((d ^ u : ℕ) : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (∀ x ∈ X, (n : ℝ) - (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))) →
      ∃ hA : (canonicalApproxFamily (d ^ u) X).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L → ∀ R : ℝ, 1 ≤ R →
      ∀ V : (Fin n → ℂ) → I → ℂ,
      canonicalFamilyProbabilitySum (canonicalApproxFamily (d ^ u) X) I (d ^ u) d R V ≤
        fixedNetSplitCost n d (n - L) R *
          ((4 : ℝ) ^ (n - L) * (Real.exp n * sourceK1ClassEnergyUpper n d L a₃) +
          (Nat.card (canonicalApproxFamily (d ^ u) X) : ℝ) *
            Real.exp (-averagedProfileRate * ((n - L : ℕ) : ℝ) * Real.rpow (d : ℝ) (2 / 3))) := by
  have hCPos : 0 < Clower := by linarith
  have haHalf : a₃ ≤ 1 / 2 := by linarith
  filter_upwards [eventually_restricted_gradual_probability_sum_uniform ha hSmall hC σ,
    eventually_source_K1_class_row_energy_uniform ha haHalf hCPos σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hSum hEnergy hConditions
  intro d hBand L hL u hRange X hX hK1
  have hd := (source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)).2.1
  obtain ⟨hA, hBound⟩ := hSum d hBand L hL (d ^ u) (pow_pos hd u) hRange X
    (hX.trans (sourceSpreadFamily_subset a₃ (1 / 4608)))
  refine ⟨hA, ?_⟩
  letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
  intro I hI R hR V
  have hFamily (x : Fin n → ℂ) (hx : x ∈ X) :
      canonicalClassRowEnergy (canonicalApproxFamily (d ^ u) X)
        (fun i => canonicalApprox (d ^ u) (x i)) ((d : ℝ) / (d ^ u : ℕ)) d I.card
          averagedProfileRate ≤ sourceK1ClassEnergyUpper n d L a₃ := by
    rw [hI]
    exact hEnergy d hBand L hL u (canonicalApproxFamily (d ^ u) X) x (hX hx) (hK1 x hx)
      averagedProfileRate averagedProfileRate_pos
  have h := hBound I R hR V (sourceK1ClassEnergyUpper n d L a₃)
    (sourceK1ClassEnergyUpper_nonneg n d L a₃)
    (canonicalApprox_class_energy_bound_of_family_bound (d ^ u) d I.card X hFamily)
  simpa only [hI] using h

theorem eventually_source_K2_family_probability_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ,
      ((d ^ u : ℕ) : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (∀ x ∈ X, (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))ᶜ) →
      ∃ hA : (canonicalApproxFamily (d ^ u) X).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L → ∀ R : ℝ, 1 ≤ R →
      ∀ V : (Fin n → ℂ) → I → ℂ,
      canonicalFamilyProbabilitySum (canonicalApproxFamily (d ^ u) X) I (d ^ u) d R V ≤
        fixedNetSplitCost n d (n - L) R *
          ((4 : ℝ) ^ (n - L) * (Real.exp n * sourceK2ClassEnergyUpper n d L a₃) +
          (Nat.card (canonicalApproxFamily (d ^ u) X) : ℝ) *
            Real.exp (-averagedProfileRate * ((n - L : ℕ) : ℝ) * Real.rpow (d : ℝ) (2 / 3))) := by
  have hCPos : 0 < Clower := by linarith
  filter_upwards [eventually_restricted_gradual_probability_sum_uniform ha hSmall hC σ,
    eventually_source_K2_class_row_energy_uniform ha hSmall hCPos σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hSum hEnergy hConditions
  intro d hBand L hL u hRange X hX hK2
  have hd := (source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)).2.1
  obtain ⟨hA, hBound⟩ := hSum d hBand L hL (d ^ u) (pow_pos hd u) hRange X
    (hX.trans (sourceSpreadFamily_subset a₃ (1 / 4608)))
  refine ⟨hA, ?_⟩
  letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
  intro I hI R hR V
  have hFamily (x : Fin n → ℂ) (hx : x ∈ X) :
      canonicalClassRowEnergy (canonicalApproxFamily (d ^ u) X)
        (fun i => canonicalApprox (d ^ u) (x i)) ((d : ℝ) / (d ^ u : ℕ)) d I.card
          averagedProfileRate ≤ sourceK2ClassEnergyUpper n d L a₃ := by
    rw [hI]
    exact hEnergy d hBand L hL u (canonicalApproxFamily (d ^ u) X) x (hX hx) (hK2 x hx)
      averagedProfileRate averagedProfileRate_pos
  have h := hBound I R hR V (sourceK2ClassEnergyUpper n d L a₃)
    (sourceK2ClassEnergyUpper_nonneg n d L a₃)
    (canonicalApprox_class_energy_bound_of_family_bound (d ^ u) d I.card X hFamily)
  simpa only [hI] using h

theorem eventually_source_Pv_family_probability_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ v : ℕ, 5 ≤ v →
      ((d ^ v : ℕ) : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) →
      ∀ (ρ δ : ℝ), ρ ≤ Real.rpow (d : ℝ) (-(v : ℝ)) → 0 < δ →
      δ ≤ 36 * (1 / 65536) * a₃ →
      (1 / 65536) * a₃ * ((v : ℝ) - 4) ≥ 2 * Real.logb 2 d +
        2 * Real.logb 2 (72 * Real.sqrt d / δ) + 2 - Real.logb 2 ((1 / 65536) * a₃) →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceHighHeightFamily n d L a₃ (1 / 65536) v →
      (∀ x ∈ X, ∃ c₀ : ℂ,
        δ * n ≤ ((Finset.univ.filter (fun i => ‖x i - c₀‖ ≤ ρ)).card : ℝ)) →
      ∃ hA : (canonicalApproxFamily (d ^ v) X).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ v) X) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L → ∀ R : ℝ, 1 ≤ R →
      ∀ V : (Fin n → ℂ) → I → ℂ,
      canonicalFamilyProbabilitySum (canonicalApproxFamily (d ^ v) X) I (d ^ v) d R V ≤
        fixedNetSplitCost n d (n - L) R *
          ((4 : ℝ) ^ (n - L) * (Real.exp n * sourcePvClassEnergyUpper n d L v a₃ δ) +
          (Nat.card (canonicalApproxFamily (d ^ v) X) : ℝ) *
            Real.exp (-averagedProfileRate * ((n - L : ℕ) : ℝ) * Real.rpow (d : ℝ) (2 / 3))) := by
  have hCPos : 0 < Clower := by linarith
  filter_upwards [eventually_restricted_gradual_probability_sum_uniform ha hSmall hC σ,
    eventually_source_Pv_class_row_energy_uniform ha hSmall hCPos σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hSum hEnergy hConditions
  intro d hBand L hL v hv hRange ρ δ hρ hδ hδUpper hSep X hX hCluster
  have hd := (source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)).2.1
  obtain ⟨hA, hBound⟩ := hSum d hBand L hL (d ^ v) (pow_pos hd v) hRange X
    (hX.trans (sourceHighHeightFamily_subset a₃ (1 / 65536)))
  refine ⟨hA, ?_⟩
  letI : Fintype (canonicalApproxFamily (d ^ v) X) := hA.fintype
  intro I hI R hR V
  have hFamily (x : Fin n → ℂ) (hx : x ∈ X) :
      canonicalClassRowEnergy (canonicalApproxFamily (d ^ v) X)
        (fun i => canonicalApprox (d ^ v) (x i)) ((d : ℝ) / (d ^ v : ℕ)) d I.card
          averagedProfileRate ≤ sourcePvClassEnergyUpper n d L v a₃ δ := by
    rw [hI]
    obtain ⟨c₀, hc₀⟩ := hCluster x hx
    exact hEnergy d hBand L hL v hv ρ δ hρ hδ hδUpper hSep (canonicalApproxFamily (d ^ v) X)
      x (hX hx) c₀ hc₀ averagedProfileRate averagedProfileRate_pos
  have h := hBound I R hR V (sourcePvClassEnergyUpper n d L v a₃ δ)
    (sourcePvClassEnergyUpper_nonneg n d L v a₃ δ)
    (canonicalApprox_class_energy_bound_of_family_bound (d ^ v) d I.card X hFamily)
  simpa only [hI] using h

end CircularLaw
