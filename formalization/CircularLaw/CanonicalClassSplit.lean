import CircularLaw.CanonicalClassProbability
import CircularLaw.FixedNetSplit
import CircularLaw.SourceClassRowEnergy

/-!
# The two-term class probability bound in each source branch

Class probability sums now use the proved class energies, with the
literal retained row count and all finite conditions supplied uniformly.
The profile-exception term is kept for subsequent summation over the
whole approximation family.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def canonicalClassProbabilityUpperBound {n : ℕ} (A : Set (Fin n → ℂ)) (y : Fin n → ℂ)
    (d K : ℕ) (R E : ℝ) : ℝ :=
  fixedNetSplitCost n d K R * ((4 : ℝ) ^ K * E +
    (Nat.card (CoordinateMultisetClassIn A y) : ℝ) *
      Real.exp (-averagedProfileRate * (K : ℝ) * Real.rpow (d : ℝ) (2 / 3)))

theorem canonicalClassProbabilityUpperBound_mono {n : ℕ} (A : Set (Fin n → ℂ))
    (y : Fin n → ℂ) (d K : ℕ) (R : ℝ) {E F : ℝ} (h : E ≤ F) :
    canonicalClassProbabilityUpperBound A y d K R E ≤
      canonicalClassProbabilityUpperBound A y d K R F :=
  mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) K)) le_rfl)
      (fixedNetSplitCost_nonneg n d K R)

theorem canonicalClass_probability_split_bounds {n d k : ℕ} (hd : 0 < d)
    (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (I : Finset (Fin n)) (R : ℝ)
    (V : CoordinateMultisetClassIn A y → I → ℂ)
    (hPoint : ∀ z : CoordinateMultisetClassIn A y,
      uniformProbability (fun rows : RowSliceMatrix n d =>
        indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) z.val (V z) ≤
          R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
        fixedNetSliceEstimate k d I.card z.val R) :
    canonicalClassProbabilitySum A y I k d R V ≤
      canonicalClassProbabilityUpperBound A y d I.card R
        (canonicalClassRowEnergy A y ((d : ℝ) / k) d I.card averagedProfileRate) ∧
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ z : CoordinateMultisetClassIn A y,
        indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) z.val (V z) ≤
          R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
      canonicalClassProbabilityUpperBound A y d I.card R
        (canonicalClassRowEnergy A y ((d : ℝ) / k) d I.card averagedProfileRate) := by
  have hSplit := canonicalClass_fixed_estimate_split hd A y k I.card R
  exact ⟨(canonicalClassProbabilitySum_le hd A y I R V hPoint).trans hSplit,
    (canonicalClass_probability_exists_le hd A y I R V hPoint).trans hSplit⟩

theorem eventually_canonical_class_probability_split_uniform {Clower : ℝ}
    (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ k : ℕ, 0 < k → ∀ X : Set (Fin n → ℂ), ∀ y : Fin n → ℂ,
        ∀ I : Finset (Fin n), ∀ R : ℝ, 1 ≤ R →
          ∀ V : CoordinateMultisetClassIn (canonicalApproxFamily k X) y → I → ℂ,
          canonicalClassProbabilitySum (canonicalApproxFamily k X) y I k d R V ≤
            canonicalClassProbabilityUpperBound (canonicalApproxFamily k X) y d I.card R
              (canonicalClassRowEnergy (canonicalApproxFamily k X) y ((d : ℝ) / k) d I.card
                averagedProfileRate) ∧
          uniformProbability (fun rows : RowSliceMatrix n d =>
            ∃ z : CoordinateMultisetClassIn (canonicalApproxFamily k X) y,
              indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) z.val (V z) ≤
                R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
            canonicalClassProbabilityUpperBound (canonicalApproxFamily k X) y d I.card R
              (canonicalClassRowEnergy (canonicalApproxFamily k X) y ((d : ℝ) / k) d I.card
                averagedProfileRate) := by
  have hCPos : 0 < Clower := by linarith
  filter_upwards [eventually_full_matrix_fixed_net_estimate_uniform hC σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hFixed hConditions
  intro d hBand k hk X y I R hR V
  have hd := (source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)).2.1
  have hPoint (z : CoordinateMultisetClassIn (canonicalApproxFamily k X) y) :=
    hFixed d hBand k hk I z.val (canonicalApproxFamily_isKVector k X z.property.1) R hR (V z)
  exact canonicalClass_probability_split_bounds hd (canonicalApproxFamily k X) y I R V hPoint

theorem eventually_source_K1_class_probability_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ, ∀ X : Set (Fin n → ℂ),
      ∀ x : Fin n → ℂ, x ∈ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (n : ℝ) - (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16)) →
      ∀ I : Finset (Fin n), I.card = n - L → ∀ R : ℝ, 1 ≤ R →
      ∀ V : CoordinateMultisetClassIn (canonicalApproxFamily (d ^ u) X)
        (fun i => canonicalApprox (d ^ u) (x i)) → I → ℂ,
      canonicalClassProbabilitySum (canonicalApproxFamily (d ^ u) X)
        (fun i => canonicalApprox (d ^ u) (x i)) I (d ^ u) d R V ≤
      canonicalClassProbabilityUpperBound (canonicalApproxFamily (d ^ u) X)
        (fun i => canonicalApprox (d ^ u) (x i)) d (n - L) R
        (Real.exp ((4096 + entropyPenaltyConstant (averagedProfileRate / 2)) * n) *
          Real.rpow (d : ℝ) (-((1 / 4608) * a₃ / 32) * n) * ((n : ℝ) * Real.sqrt d) ^ L) := by
  have hCPos : 0 < Clower := by linarith
  have haHalf : a₃ ≤ 1 / 2 := by linarith
  filter_upwards [eventually_canonical_class_probability_split_uniform hC σ,
    eventually_source_K1_class_row_energy_uniform ha haHalf hCPos σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hSplit hEnergy hConditions
  intro d hBand L hL u X x hx hK1 I hI R hR V
  have hd := (source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)).2.1
  have h := (hSplit d hBand (d ^ u) (pow_pos hd u) X
    (fun i => canonicalApprox (d ^ u) (x i)) I R hR V).1
  rw [hI] at h
  exact h.trans (canonicalClassProbabilityUpperBound_mono _ _ d (n - L) R
    (hEnergy d hBand L hL u (canonicalApproxFamily (d ^ u) X) x hx hK1
      averagedProfileRate averagedProfileRate_pos))

theorem eventually_source_K2_class_probability_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ, ∀ X : Set (Fin n → ℂ),
      ∀ x : Fin n → ℂ, x ∈ sourceSpreadFamily n d L a₃ (1 / 4608) u →
      (1 / 4608) * (thirdSteepScale n a₃ : ℝ) / 4 ≤
        profileSelectedMass (sourceScaleProfile d u x)
          (profileCutoffParts (sourceScaleProfile d u x) d ((1 / 4608) * a₃ / 16))ᶜ →
      ∀ I : Finset (Fin n), I.card = n - L → ∀ R : ℝ, 1 ≤ R →
      ∀ V : CoordinateMultisetClassIn (canonicalApproxFamily (d ^ u) X)
        (fun i => canonicalApprox (d ^ u) (x i)) → I → ℂ,
      canonicalClassProbabilitySum (canonicalApproxFamily (d ^ u) X)
        (fun i => canonicalApprox (d ^ u) (x i)) I (d ^ u) d R V ≤
      canonicalClassProbabilityUpperBound (canonicalApproxFamily (d ^ u) X)
        (fun i => canonicalApprox (d ^ u) (x i)) d (n - L) R
        (Real.exp ((4096 + entropyPenaltyConstant (averagedProfileRate / 4)) * n) * (d : ℝ) ^ n *
          ((n : ℝ) * Real.sqrt d) ^ L *
          Real.exp (-(averagedProfileRate / 2) * ((n - L : ℕ) : ℝ) *
            ((2 * ((1 / 65536) * a₃ / 4) ^ 2 * ((1 / 4608) * a₃ / 16384)) *
              Real.rpow (d : ℝ) ((1 / 4608) * a₃ / 16)))) := by
  have hCPos : 0 < Clower := by linarith
  filter_upwards [eventually_canonical_class_probability_split_uniform hC σ,
    eventually_source_K2_class_row_energy_uniform ha hSmall hCPos σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hSplit hEnergy hConditions
  intro d hBand L hL u X x hx hK2 I hI R hR V
  have hd := (source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)).2.1
  have h := (hSplit d hBand (d ^ u) (pow_pos hd u) X
    (fun i => canonicalApprox (d ^ u) (x i)) I R hR V).1
  rw [hI] at h
  exact h.trans (canonicalClassProbabilityUpperBound_mono _ _ d (n - L) R
    (hEnergy d hBand L hL u (canonicalApproxFamily (d ^ u) X) x hx hK2
      averagedProfileRate averagedProfileRate_pos))

theorem eventually_source_Pv_class_probability_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ v : ℕ, 5 ≤ v →
      ∀ (ρ δ : ℝ), ρ ≤ Real.rpow (d : ℝ) (-(v : ℝ)) → 0 < δ →
      δ ≤ 36 * (1 / 65536) * a₃ →
      (1 / 65536) * a₃ * ((v : ℝ) - 4) ≥ 2 * Real.logb 2 d +
        2 * Real.logb 2 (72 * Real.sqrt d / δ) + 2 - Real.logb 2 ((1 / 65536) * a₃) →
      ∀ X : Set (Fin n → ℂ), ∀ x : Fin n → ℂ,
      x ∈ sourceHighHeightFamily n d L a₃ (1 / 65536) v →
      ∀ c₀ : ℂ, δ * n ≤ ((Finset.univ.filter (fun i => ‖x i - c₀‖ ≤ ρ)).card : ℝ) →
      ∀ I : Finset (Fin n), I.card = n - L → ∀ R : ℝ, 1 ≤ R →
      ∀ V : CoordinateMultisetClassIn (canonicalApproxFamily (d ^ v) X)
        (fun i => canonicalApprox (d ^ v) (x i)) → I → ℂ,
      canonicalClassProbabilitySum (canonicalApproxFamily (d ^ v) X)
        (fun i => canonicalApprox (d ^ v) (x i)) I (d ^ v) d R V ≤
      canonicalClassProbabilityUpperBound (canonicalApproxFamily (d ^ v) X)
        (fun i => canonicalApprox (d ^ v) (x i)) d (n - L) R
        (Real.exp ((4096 + entropyPenaltyConstant (averagedProfileRate / 4)) * n) * (d : ℝ) ^ n *
          ((n : ℝ) * Real.sqrt d) ^ L * Real.exp (-(averagedProfileRate / 2) * ((n - L : ℕ) : ℝ) *
            ((δ * ((1 / 65536) * a₃ / 4) * ((1 / 65536) * a₃) / 36) * ((v : ℝ) - 4)))) := by
  have hCPos : 0 < Clower := by linarith
  filter_upwards [eventually_canonical_class_probability_split_uniform hC σ,
    eventually_source_Pv_class_row_energy_uniform ha hSmall hCPos σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hSplit hEnergy hConditions
  intro d hBand L hL v hv ρ δ hρ hδ hδUpper hSep X x hx c₀ hCluster I hI R hR V
  have hd := (source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)).2.1
  have h := (hSplit d hBand (d ^ v) (pow_pos hd v) X
    (fun i => canonicalApprox (d ^ v) (x i)) I R hR V).1
  rw [hI] at h
  exact h.trans (canonicalClassProbabilityUpperBound_mono _ _ d (n - L) R
    (hEnergy d hBand L hL v hv ρ δ hρ hδ hδUpper hSep (canonicalApproxFamily (d ^ v) X)
      x hx c₀ hCluster averagedProfileRate averagedProfileRate_pos))

end CircularLaw
