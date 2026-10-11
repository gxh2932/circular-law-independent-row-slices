import CircularLaw.CanonicalClassStatistics
import CircularLaw.FullMatrixFixedNet

/-!
# Probability sums over actual canonical classes

Each class is finite and its checked fixed-vector bound is constant.
The shifts may be chosen separately for every class member. The uniform
estimate applies to every restricted canonical approximation family and
the original full independent row-slice matrix law.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def canonicalClassProbabilitySum {n : ℕ} (A : Set (Fin n → ℂ)) (y : Fin n → ℂ)
    (I : Finset (Fin n)) (k d : ℕ) (R : ℝ)
    (V : CoordinateMultisetClassIn A y → I → ℂ) : ℝ :=
  letI : Fintype (CoordinateMultisetClassIn A y) := Fintype.ofFinite _
  ∑ z : CoordinateMultisetClassIn A y,
    uniformProbability (fun rows : RowSliceMatrix n d =>
      indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) z.val (V z) ≤
        R * Real.log d * Real.sqrt ((d : ℝ) * n) / k)

theorem canonicalClassProbabilitySum_le {n d k : ℕ} (hd : 0 < d)
    (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (I : Finset (Fin n)) (R : ℝ)
    (V : CoordinateMultisetClassIn A y → I → ℂ)
    (hPoint : ∀ z : CoordinateMultisetClassIn A y,
      uniformProbability (fun rows : RowSliceMatrix n d =>
        indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) z.val (V z) ≤
          R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
        fixedNetSliceEstimate k d I.card z.val R) :
    canonicalClassProbabilitySum A y I k d R V ≤
      (Nat.card (CoordinateMultisetClassIn A y) : ℝ) * fixedNetSliceEstimate k d I.card y R := by
  letI : Fintype (CoordinateMultisetClassIn A y) := Fintype.ofFinite _
  calc
    canonicalClassProbabilitySum A y I k d R V ≤
        ∑ _z : CoordinateMultisetClassIn A y, fixedNetSliceEstimate k d I.card y R := by
      apply Finset.sum_le_sum
      intro z _
      exact (hPoint z).trans_eq (fixedNetSliceEstimate_multiset_eq y z.val z.property.2 k I.card hd R)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem canonicalClass_probability_exists_le {n d k : ℕ} (hd : 0 < d)
    (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (I : Finset (Fin n)) (R : ℝ)
    (V : CoordinateMultisetClassIn A y → I → ℂ)
    (hPoint : ∀ z : CoordinateMultisetClassIn A y,
      uniformProbability (fun rows : RowSliceMatrix n d =>
        indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) z.val (V z) ≤
          R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
        fixedNetSliceEstimate k d I.card z.val R) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ z : CoordinateMultisetClassIn A y,
        indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) z.val (V z) ≤
          R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
      (Nat.card (CoordinateMultisetClassIn A y) : ℝ) * fixedNetSliceEstimate k d I.card y R := by
  letI : Fintype (CoordinateMultisetClassIn A y) := Fintype.ofFinite _
  have hUnion := uniformProbability_finset_exists_le
    (Finset.univ : Finset (CoordinateMultisetClassIn A y))
    (fun z (rows : RowSliceMatrix n d) => indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) z.val (V z) ≤
      R * Real.log d * Real.sqrt ((d : ℝ) * n) / k)
  simp only [Finset.mem_univ, true_and] at hUnion
  exact hUnion.trans (canonicalClassProbabilitySum_le hd A y I R V hPoint)

theorem eventually_canonical_class_probability_bounds_uniform {Clower : ℝ}
    (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ k : ℕ, 0 < k → ∀ X : Set (Fin n → ℂ), ∀ y : Fin n → ℂ,
        ∀ I : Finset (Fin n), ∀ R : ℝ, 1 ≤ R →
          ∀ V : CoordinateMultisetClassIn (canonicalApproxFamily k X) y → I → ℂ,
          canonicalClassProbabilitySum (canonicalApproxFamily k X) y I k d R V ≤
            (Nat.card (CoordinateMultisetClassIn (canonicalApproxFamily k X) y) : ℝ) *
              fixedNetSliceEstimate k d I.card y R ∧
          uniformProbability (fun rows : RowSliceMatrix n d =>
            ∃ z : CoordinateMultisetClassIn (canonicalApproxFamily k X) y,
              indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) z.val (V z) ≤
                R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
            (Nat.card (CoordinateMultisetClassIn (canonicalApproxFamily k X) y) : ℝ) *
              fixedNetSliceEstimate k d I.card y R := by
  have hCPos : 0 < Clower := by linarith
  filter_upwards [eventually_full_matrix_fixed_net_estimate_uniform hC σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hFixed hConditions
  intro d hBand k hk X y I R hR V
  have hd := (source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)).2.1
  have hPoint (z : CoordinateMultisetClassIn (canonicalApproxFamily k X) y) :=
    hFixed d hBand k hk I z.val (canonicalApproxFamily_isKVector k X z.property.1) R hR (V z)
  exact ⟨canonicalClassProbabilitySum_le hd (canonicalApproxFamily k X) y I R V hPoint,
    canonicalClass_probability_exists_le hd (canonicalApproxFamily k X) y I R V hPoint⟩

end CircularLaw
