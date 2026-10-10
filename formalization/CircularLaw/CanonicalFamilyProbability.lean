import CircularLaw.CanonicalClassSplit
import CircularLaw.CoordinateClassSummation

/-!
# Summing the fixed-vector bounds over the represented family

The original family sum is regrouped by its actual multiset classes.
The dispersion energies are summed over classes, while the additive
profile-exception term costs exactly the number of net vectors.
The standing gradual setting supplies finiteness and the `exp(n)`
class count; the subsequent branch budgets remain separate.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def canonicalFamilyProbabilitySum {n : ℕ} (A : Set (Fin n → ℂ)) [Fintype A]
    (I : Finset (Fin n)) (k d : ℕ) (R : ℝ) (V : (Fin n → ℂ) → I → ℂ) : ℝ :=
  ∑ y : A, uniformProbability (fun rows : RowSliceMatrix n d =>
    indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val (V y.val) ≤
      R * Real.log d * Real.sqrt ((d : ℝ) * n) / k)

theorem canonicalFamilyProbabilitySum_by_classes {n : ℕ}
    (A : Set (Fin n → ℂ)) [Fintype A] [Fintype (CoordinateMultisetClassesOf A)]
    (I : Finset (Fin n)) (k d : ℕ) (R : ℝ) (V : (Fin n → ℂ) → I → ℂ) :
    canonicalFamilyProbabilitySum A I k d R V =
      ∑ m : CoordinateMultisetClassesOf A,
        canonicalClassProbabilitySum A (coordinateClassRepresentative A m).val I k d R
          (fun z => V z.val) := by
  exact coordinate_family_sum_by_classes A (fun y =>
    uniformProbability (fun rows : RowSliceMatrix n d =>
      indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y (V y) ≤
        R * Real.log d * Real.sqrt ((d : ℝ) * n) / k))

theorem canonicalFamily_probability_exists_le {n : ℕ} (A : Set (Fin n → ℂ)) [Fintype A]
    (I : Finset (Fin n)) (k d : ℕ) (R : ℝ) (V : (Fin n → ℂ) → I → ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ y : A, indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val (V y.val) ≤
        R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
      canonicalFamilyProbabilitySum A I k d R V := by
  have h := uniformProbability_finset_exists_le (Finset.univ : Finset A)
    (fun y (rows : RowSliceMatrix n d) =>
      indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val (V y.val) ≤
        R * Real.log d * Real.sqrt ((d : ℝ) * n) / k)
  simpa only [Finset.mem_univ, true_and] using h

theorem canonicalFamilyProbabilitySum_split {n d k : ℕ} (hd : 0 < d)
    (A : Set (Fin n → ℂ)) [Fintype A] [Fintype (CoordinateMultisetClassesOf A)]
    (I : Finset (Fin n)) (R : ℝ) (V : (Fin n → ℂ) → I → ℂ)
    (hPoint : ∀ y : A,
      uniformProbability (fun rows : RowSliceMatrix n d =>
        indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val (V y.val) ≤
          R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
        fixedNetSliceEstimate k d I.card y.val R) :
    canonicalFamilyProbabilitySum A I k d R V ≤ fixedNetSplitCost n d I.card R *
      ((4 : ℝ) ^ I.card * (∑ m : CoordinateMultisetClassesOf A,
        canonicalClassRowEnergy A (coordinateClassRepresentative A m).val
          ((d : ℝ) / k) d I.card averagedProfileRate) +
      (Nat.card A : ℝ) * Real.exp (-averagedProfileRate * (I.card : ℝ) *
        Real.rpow (d : ℝ) (2 / 3))) := by
  rw [canonicalFamilyProbabilitySum_by_classes]
  calc
    _ ≤ ∑ m : CoordinateMultisetClassesOf A,
        canonicalClassProbabilityUpperBound A (coordinateClassRepresentative A m).val d I.card R
          (canonicalClassRowEnergy A (coordinateClassRepresentative A m).val
            ((d : ℝ) / k) d I.card averagedProfileRate) := by
      apply Finset.sum_le_sum
      intro m _
      apply (canonicalClass_probability_split_bounds hd A
        (coordinateClassRepresentative A m).val I R (fun z => V z.val) ?_).1
      intro z
      exact hPoint ⟨z.val, z.property.1⟩
    _ = _ := by
      dsimp only [canonicalClassProbabilityUpperBound]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, coordinate_class_card_sum]

theorem canonicalFamilyProbabilitySum_class_energy_bound {n d k : ℕ} (hd : 0 < d)
    (A : Set (Fin n → ℂ)) [Fintype A] [Fintype (CoordinateMultisetClassesOf A)]
    (I : Finset (Fin n)) (R : ℝ) (V : (Fin n → ℂ) → I → ℂ)
    (hPoint : ∀ y : A,
      uniformProbability (fun rows : RowSliceMatrix n d =>
        indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val (V y.val) ≤
          R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
        fixedNetSliceEstimate k d I.card y.val R)
    {E : ℝ} (hEnergy : ∀ m : CoordinateMultisetClassesOf A,
      canonicalClassRowEnergy A (coordinateClassRepresentative A m).val
        ((d : ℝ) / k) d I.card averagedProfileRate ≤ E) :
    canonicalFamilyProbabilitySum A I k d R V ≤ fixedNetSplitCost n d I.card R *
      ((4 : ℝ) ^ I.card * ((Nat.card (CoordinateMultisetClassesOf A) : ℝ) * E) +
      (Nat.card A : ℝ) * Real.exp (-averagedProfileRate * (I.card : ℝ) *
        Real.rpow (d : ℝ) (2 / 3))) := by
  have hSum : (∑ m : CoordinateMultisetClassesOf A,
      canonicalClassRowEnergy A (coordinateClassRepresentative A m).val
        ((d : ℝ) / k) d I.card averagedProfileRate) ≤
        (Nat.card (CoordinateMultisetClassesOf A) : ℝ) * E := by
    apply (Finset.sum_le_sum (fun m _ => hEnergy m)).trans_eq
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  exact (canonicalFamilyProbabilitySum_split hd A I R V hPoint).trans
    (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hSum (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) I.card)) le_rfl)
        (fixedNetSplitCost_nonneg n d I.card R))

theorem eventually_restricted_gradual_probability_sum_uniform {a₃ Clower : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceGradual n d L a₃ →
      ∃ hA : (canonicalApproxFamily k X).Finite,
      letI : Fintype (canonicalApproxFamily k X) := hA.fintype
      letI : Fintype (CoordinateMultisetClassesOf (canonicalApproxFamily k X)) :=
        (coordinateMultisetClasses_finite hA).fintype
      ∀ I : Finset (Fin n), ∀ R : ℝ, 1 ≤ R → ∀ V : (Fin n → ℂ) → I → ℂ,
      ∀ E : ℝ, 0 ≤ E →
      (∀ m : CoordinateMultisetClassesOf (canonicalApproxFamily k X),
        canonicalClassRowEnergy (canonicalApproxFamily k X)
          (coordinateClassRepresentative (canonicalApproxFamily k X) m).val
          ((d : ℝ) / k) d I.card averagedProfileRate ≤ E) →
      canonicalFamilyProbabilitySum (canonicalApproxFamily k X) I k d R V ≤
        fixedNetSplitCost n d I.card R * ((4 : ℝ) ^ I.card * (Real.exp n * E) +
          (Nat.card (canonicalApproxFamily k X) : ℝ) *
            Real.exp (-averagedProfileRate * (I.card : ℝ) * Real.rpow (d : ℝ) (2 / 3))) := by
  have hCPos : 0 < Clower := by linarith
  filter_upwards [eventually_full_matrix_fixed_net_estimate_uniform hC σ,
    eventually_restrictedGradualApproxClasses_exp_n_uniform ha hSmall hCPos σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hFixed hCount hConditions
  intro d hBand L hL k hk hRange X hX
  obtain ⟨hA, hClasses⟩ := hCount d hBand L hL k hk hRange X hX
  refine ⟨hA, ?_⟩
  letI : Fintype (canonicalApproxFamily k X) := hA.fintype
  letI : Fintype (CoordinateMultisetClassesOf (canonicalApproxFamily k X)) :=
    (coordinateMultisetClasses_finite hA).fintype
  intro I R hR V E hE hEnergy
  have hd := (source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)).2.1
  have hPoint (y : canonicalApproxFamily k X) :=
    hFixed d hBand k hk I y.val (canonicalApproxFamily_isKVector k X y.property) R hR (V y.val)
  have h := canonicalFamilyProbabilitySum_class_energy_bound hd (canonicalApproxFamily k X)
    I R V hPoint hEnergy
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hClasses hE)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) I.card)) le_rfl)
        (fixedNetSplitCost_nonneg n d I.card R))

end CircularLaw
