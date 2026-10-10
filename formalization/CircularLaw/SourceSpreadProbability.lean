import CircularLaw.StructuralBranchEnergy
import CircularLaw.FiniteProbabilitySupremum

/-!
# Closing the two mass cases of the structural spread families

Both branch sums use the actual finite family and the supremum over
all deterministic shifts at each vector. A common degree-logarithmic
rate is derived from the checked K1, K2 and profile-exception decays.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

theorem eventually_sourceSpread_log_decay_comparison {a₃ : ℝ} (ha : 0 < a₃) :
    ∀ᶠ d : ℕ in atTop,
      (sourceK1DecayExponent a₃ / 2) * Real.log d ≤
        sourceK2DecayRate a₃ * Real.rpow (d : ℝ) (sourceK2DispersionExponent a₃) ∧
      (sourceK1DecayExponent a₃ / 2) * Real.log d ≤
      (averagedProfileRate / 4) * Real.rpow (d : ℝ) (2 / 3) := by
  have hc := averagedProfileRate_pos
  have hK1 : 0 < sourceK1DecayExponent a₃ / 2 :=
    div_pos (sourceK1DecayExponent_pos ha) (by norm_num)
  filter_upwards [eventually_log_power_degree_budget (sourceK2DispersionExponent_pos ha)
    (sourceK2DecayRate_pos ha) 0 (sourceK1DecayExponent a₃ / 2) hK1,
    eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 2 / 3)
      (by positivity : 0 < averagedProfileRate / 4) 0 (sourceK1DecayExponent a₃ / 2) hK1]
    with d hK2 hException
  exact ⟨by simpa only [zero_add] using hK2, by simpa only [zero_add] using hException⟩

theorem exp_dimension_decay_mono (n : ℕ) {a b : ℝ} (h : a ≤ b) :
    Real.exp (-b * n) ≤ Real.exp (-a * n) := by
  apply Real.exp_le_exp.mpr
  have hScaled := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  linarith

theorem eventually_source_K1_probability_decay_uniform {a₃ C σ : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1)
    (R : ℝ) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ,
      u ≤ structuralTerminalExponent n d L →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (∀ x ∈ X, (n : ℝ) - (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))) →
      ∃ hA : (canonicalApproxFamily (d ^ u) X).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L →
      canonicalFamilySupProbabilitySum (canonicalApproxFamily (d ^ u) X) I (d ^ u) d R ≤
        2 * Real.exp (-(sourceK1DecayExponent a₃ / 2) * n * Real.log d) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_source_K1_terminal_probability_uniform ha hSmall hC hσ R hR,
    eventually_sourceK1_mainTerm_absorbed_uniform ha (by linarith : 1 ≤ C) σ R,
    eventually_degree_property_uniform hCPos (eventually_sourceSpread_log_decay_comparison ha)]
    with n hSum hMain hCompare
  intro d hBand L hL u hu X hX hMass
  obtain ⟨hA, hBound⟩ := hSum d hBand L hL u hu X hX hMass
  refine ⟨hA, ?_⟩
  letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
  intro I hI
  apply canonicalFamilySupProbabilitySum_le _ I (d ^ u) d R _
  intro V
  have hEnergy := hMain d hBand L hL
  have hError := exp_dimension_decay_mono n (hCompare d hBand.1).2
  apply (hBound I hI V).trans
  change structuralMainTerm n d L R (sourceK1ClassEnergyUpper n d L a₃) + _ ≤ _
  have hError' : Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) ≤
      Real.exp (-(sourceK1DecayExponent a₃ / 2) * n * Real.log d) := by
    convert hError using 1 <;> congr 1 <;> ring
  nlinarith only [hEnergy, hError']

theorem eventually_source_K2_probability_decay_uniform {a₃ C σ : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1)
    (R : ℝ) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ,
      u ≤ structuralTerminalExponent n d L →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (∀ x ∈ X, (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))ᶜ) →
      ∃ hA : (canonicalApproxFamily (d ^ u) X).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L →
      canonicalFamilySupProbabilitySum (canonicalApproxFamily (d ^ u) X) I (d ^ u) d R ≤
        2 * Real.exp (-(sourceK1DecayExponent a₃ / 2) * n * Real.log d) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_source_K2_terminal_probability_uniform ha hSmall hC hσ R hR,
    eventually_sourceK2_mainTerm_absorbed_uniform ha (by linarith : 1 ≤ C) σ R,
    eventually_degree_property_uniform hCPos (eventually_sourceSpread_log_decay_comparison ha)]
    with n hSum hMain hCompare
  intro d hBand L hL u hu X hX hMass
  obtain ⟨hA, hBound⟩ := hSum d hBand L hL u hu X hX hMass
  refine ⟨hA, ?_⟩
  letI : Fintype (canonicalApproxFamily (d ^ u) X) := hA.fintype
  intro I hI
  apply canonicalFamilySupProbabilitySum_le _ I (d ^ u) d R _
  intro V
  have hEnergy := hMain d hBand L hL
  have hComparison := hCompare d hBand.1
  have hMainDecay := exp_dimension_decay_mono n hComparison.1
  have hErrorDecay := exp_dimension_decay_mono n hComparison.2
  have hMain' : structuralMainTerm n d L R (sourceK2ClassEnergyUpper n d L a₃) ≤
      Real.exp (-(sourceK1DecayExponent a₃ / 2) * n * Real.log d) := by
    apply hEnergy.trans
    convert hMainDecay using 1 <;> congr 1 <;> ring
  have hError' : Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) ≤
      Real.exp (-(sourceK1DecayExponent a₃ / 2) * n * Real.log d) := by
    convert hErrorDecay using 1 <;> congr 1 <;> ring
  apply (hBound I hI V).trans
  change structuralMainTerm n d L R (sourceK2ClassEnergyUpper n d L a₃) + _ ≤ _
  nlinarith only [hMain', hError']

def sourceSpreadCaseOne (n d L : ℕ) (a₃ : ℝ) (u : ℕ) : Set (Fin n → ℂ) :=
  {x | x ∈ sourceSpreadFamily n d L a₃ (1 / 4608) u ∧
    (n : ℝ) - (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
      profileSelectedMass (sourceScaleProfile d u x)
        (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))}

def sourceSpreadCaseTwo (n d L : ℕ) (a₃ : ℝ) (u : ℕ) : Set (Fin n → ℂ) :=
  {x | x ∈ sourceSpreadFamily n d L a₃ (1 / 4608) u ∧
    (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
      profileSelectedMass (sourceScaleProfile d u x)
        (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))ᶜ}

theorem sourceSpreadFamily_cases (n d L : ℕ) (a₃ : ℝ) (u : ℕ) :
    sourceSpreadFamily n d L a₃ (1 / 4608) u =
      sourceSpreadCaseOne n d L a₃ u ∪ sourceSpreadCaseTwo n d L a₃ u := by
  ext x
  constructor
  · intro hx
    have h := profileCutoff_mass_dichotomy (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16)
      ((1 / 4608) * (thirdSteepScale n a₃ : ℝ))
    simp only [Fintype.card_fin] at h
    rcases h with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (h | h) <;> exact h.1

theorem canonicalApproxFamily_union {n : ℕ} (k : ℕ) (X Y : Set (Fin n → ℂ)) :
    canonicalApproxFamily k (X ∪ Y) = canonicalApproxFamily k X ∪ canonicalApproxFamily k Y :=
  Set.image_union _ _ _

theorem eventually_sourceSpread_probability_decay_uniform {a₃ C σ : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1)
    (R : ℝ) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ,
      u ≤ structuralTerminalExponent n d L →
      ∃ hA : (canonicalApproxFamily (d ^ u) (sourceSpreadFamily n d L a₃ (1 / 4608) u)).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ u) (sourceSpreadFamily n d L a₃ (1 / 4608) u)) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L →
      canonicalFamilySupProbabilitySum (canonicalApproxFamily (d ^ u)
        (sourceSpreadFamily n d L a₃ (1 / 4608) u)) I (d ^ u) d R ≤
        4 * Real.exp (-(sourceK1DecayExponent a₃ / 2) * n * Real.log d) := by
  filter_upwards [eventually_source_K1_probability_decay_uniform ha hSmall hC hσ R hR,
    eventually_source_K2_probability_decay_uniform ha hSmall hC hσ R hR] with n hK1 hK2
  intro d hBand L hL u hu
  obtain ⟨hA1, hBound1⟩ := hK1 d hBand L hL u hu (sourceSpreadCaseOne n d L a₃ u)
    (fun _ h => h.1) (fun _ h => h.2)
  obtain ⟨hA2, hBound2⟩ := hK2 d hBand L hL u hu (sourceSpreadCaseTwo n d L a₃ u)
    (fun _ h => h.1) (fun _ h => h.2)
  have hUnion : canonicalApproxFamily (d ^ u) (sourceSpreadFamily n d L a₃ (1 / 4608) u) =
      canonicalApproxFamily (d ^ u) (sourceSpreadCaseOne n d L a₃ u) ∪
        canonicalApproxFamily (d ^ u) (sourceSpreadCaseTwo n d L a₃ u) := by
    rw [sourceSpreadFamily_cases, canonicalApproxFamily_union]
  have hA := hUnion ▸ hA1.union hA2
  refine ⟨hA, ?_⟩
  letI := hA.fintype
  letI := hA1.fintype
  letI := hA2.fintype
  letI := (hA1.union hA2).fintype
  intro I hI
  have h1 := hBound1 I hI
  have h2 := hBound2 I hI
  have h := canonicalFamilySupProbabilitySum_union_le
    (canonicalApproxFamily (d ^ u) (sourceSpreadCaseOne n d L a₃ u))
    (canonicalApproxFamily (d ^ u) (sourceSpreadCaseTwo n d L a₃ u)) I (d ^ u) d R
  have h' : canonicalFamilySupProbabilitySum (canonicalApproxFamily (d ^ u)
      (sourceSpreadFamily n d L a₃ (1 / 4608) u)) I (d ^ u) d R ≤
      canonicalFamilySupProbabilitySum (canonicalApproxFamily (d ^ u)
        (sourceSpreadCaseOne n d L a₃ u)) I (d ^ u) d R +
      canonicalFamilySupProbabilitySum (canonicalApproxFamily (d ^ u)
        (sourceSpreadCaseTwo n d L a₃ u)) I (d ^ u) d R := by
    rw [canonicalFamilySupProbabilitySum_congr_set hUnion I (d ^ u) d R]
    exact h
  nlinarith only [h1, h2, h']

end CircularLaw
