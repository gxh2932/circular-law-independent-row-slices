import CircularLaw.CanonicalNetKernelCover
import CircularLaw.FiniteProbabilitySupremum
import CircularLaw.RowLoadFailure
import CircularLaw.UniformSourceKernelConditions

/-!
# Probability reduction for continuous kernel vectors

The actual canonical image and actual scalar mean grid give the
manuscript's sum of fixed-vector shift suprema. The only remaining
probabilistic input to this reusable reduction is the failure probability
of the actual retained centered norm event. `NetReductionTheorem` supplies
the checked tail and closes all parts of the named lemma.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

theorem canonicalFamilyProbabilitySum_le_sup {n : ℕ}
    (A : Set (Fin n → ℂ)) [Fintype A] (I : Finset (Fin n)) (k d : ℕ) (R : ℝ)
    (V : (Fin n → ℂ) → I → ℂ) :
    canonicalFamilyProbabilitySum A I k d R V ≤ canonicalFamilySupProbabilitySum A I k d R := by
  unfold canonicalFamilyProbabilitySum canonicalFamilySupProbabilitySum
  apply Finset.sum_le_sum
  intro y _
  have hBdd : BddAbove (Set.range (fun W : I → ℂ => uniformProbability (fun rows : RowSliceMatrix n d =>
      indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val W ≤
        R * Real.log d * Real.sqrt ((d : ℝ) * n) / k))) := by
    refine ⟨1, ?_⟩
    rintro p ⟨W, rfl⟩
    exact uniformProbability_le_one _
  exact le_ciSup hBdd (V y.val)

theorem canonicalFamily_scalar_probability_union_le {n : ℕ} (A : Set (Fin n → ℂ)) [Fintype A]
    (I : Finset (Fin n)) (k d : ℕ) (R : ℝ) (ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d => ∃ β ∈ scalarMeanGrid k d,
      ∃ y : A, indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val
        (canonicalNetShift I d ζ y.val β) ≤ R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤
      (d : ℝ) ^ 2 * canonicalFamilySupProbabilitySum A I k d R := by
  let E := fun (β : ℂ) (rows : RowSliceMatrix n d) => ∃ y : A,
    indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val (canonicalNetShift I d ζ y.val β) ≤
      R * Real.log d * Real.sqrt ((d : ℝ) * n) / k
  have hPoint (β : ℂ) : uniformProbability (E β) ≤ canonicalFamilySupProbabilitySum A I k d R :=
    (canonicalFamily_probability_exists_le A I k d R (fun y => canonicalNetShift I d ζ y β)).trans
      (canonicalFamilyProbabilitySum_le_sup _ I k d R _)
  apply (uniformProbability_finset_exists_le (scalarMeanGrid k d) E).trans
  calc
    _ ≤ ∑ _β ∈ scalarMeanGrid k d, canonicalFamilySupProbabilitySum A I k d R :=
      Finset.sum_le_sum (fun β _ => hPoint β)
    _ = ((scalarMeanGrid k d).card : ℝ) * canonicalFamilySupProbabilitySum A I k d R := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast scalarMeanGrid_card_le k d)
      (canonicalFamilySupProbabilitySum_nonneg _ I k d R)

theorem canonical_kernel_on_norm_event_probability_reduction {n d k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) {B Z₀ R : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z₀)
    (hDegree : canonicalNetCoverCoefficient B Z₀ ≤ R * Real.log d)
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d)
    (X : Set (Fin n → ℂ)) [Fintype (canonicalApproxFamily k X)] :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      (∃ x ∈ X, (retainedShiftedMatrix I ζ rows).mulVec x = 0) ∧ RetainedCenteredNormBound I rows B) ≤
      (d : ℝ) ^ 2 * canonicalFamilySupProbabilitySum (canonicalApproxFamily k X) I k d R := by
  apply (uniformProbability_mono ?_).trans
    (canonicalFamily_scalar_probability_union_le (canonicalApproxFamily k X) I k d R ζ)
  intro rows hEvent
  obtain ⟨x, hx, hKernel⟩ := hEvent.1
  obtain ⟨y, hy, β, hβ, hSmall⟩ :=
    canonical_kernel_net_cover hn hd hk hB hZ hDegree I ζ hShift rows hEvent.2 X x hx hKernel
  exact ⟨β, hβ, ⟨y, hy⟩, hSmall⟩

theorem canonical_kernel_probability_net_reduction {n d k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) {B Z₀ R : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z₀)
    (hDegree : canonicalNetCoverCoefficient B Z₀ ≤ R * Real.log d)
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d)
    (X : Set (Fin n → ℂ)) [Fintype (canonicalApproxFamily k X)] :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ x ∈ X, (retainedShiftedMatrix I ζ rows).mulVec x = 0) ≤
      (d : ℝ) ^ 2 * canonicalFamilySupProbabilitySum (canonicalApproxFamily k X) I k d R +
        uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B) := by
  let E := fun (β : ℂ) (rows : RowSliceMatrix n d) =>
    ∃ y : canonicalApproxFamily k X,
      indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val (canonicalNetShift I d ζ y.val β) ≤
        R * Real.log d * Real.sqrt ((d : ℝ) * n) / k
  have hCover : ∀ rows : RowSliceMatrix n d,
      (∃ x ∈ X, (retainedShiftedMatrix I ζ rows).mulVec x = 0) →
      ¬RetainedCenteredNormBound I rows B ∨ ∃ β ∈ scalarMeanGrid k d, E β rows := by
    intro rows hEvent
    by_cases hNorm : RetainedCenteredNormBound I rows B
    · obtain ⟨x, hx, hKernel⟩ := hEvent
      obtain ⟨y, hy, β, hβ, hSmall⟩ :=
        canonical_kernel_net_cover hn hd hk hB hZ hDegree I ζ hShift rows hNorm X x hx hKernel
      exact Or.inr ⟨β, hβ, ⟨y, hy⟩, hSmall⟩
    · exact Or.inl hNorm
  have hSum : uniformProbability (fun rows => ∃ β ∈ scalarMeanGrid k d, E β rows) ≤
      (d : ℝ) ^ 2 * canonicalFamilySupProbabilitySum (canonicalApproxFamily k X) I k d R := by
    exact canonicalFamily_scalar_probability_union_le (canonicalApproxFamily k X) I k d R ζ
  apply (uniformProbability_mono hCover).trans
  apply (uniformProbability_or_le _ _).trans
  have h := add_le_add (le_refl (uniformProbability (fun rows : RowSliceMatrix n d =>
    ¬RetainedCenteredNormBound I rows B))) hSum
  convert h using 1
  ring

theorem canonical_kernel_probability_displayed_reduction {n d k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) {B Z₀ R : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z₀)
    (hDegree : canonicalNetCoverCoefficient B Z₀ ≤ R * Real.log d)
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d)
    (X : Set (Fin n → ℂ)) [Fintype (canonicalApproxFamily k X)] :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ x ∈ X, (retainedShiftedMatrix I ζ rows).mulVec x = 0) ≤
      2 * (d : ℝ) ^ 2 * canonicalFamilySupProbabilitySum (canonicalApproxFamily k X) I k d R +
        uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B) := by
  apply (canonical_kernel_probability_net_reduction hn hd hk hB hZ hDegree I ζ hShift X).trans
  have hNonneg := canonicalFamilySupProbabilitySum_nonneg (canonicalApproxFamily k X) I k d R
  nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) hNonneg]

theorem eventually_canonical_net_degree_budget_uniform {C : ℝ} (hC : 0 < C)
    (B Z₀ R : ℝ) (hB : 0 ≤ B) (hZ : 0 ≤ Z₀) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) →
      canonicalNetCoverCoefficient B Z₀ ≤ R * Real.log d := by
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop
      (canonicalNetCoverCoefficient B Z₀)
  filter_upwards [eventually_degree_property_uniform hC hLog] with n hBudget
  intro d hLower
  have hLogDegree := hBudget d hLower
  change canonicalNetCoverCoefficient B Z₀ ≤ Real.log d at hLogDegree
  exact hLogDegree.trans (le_mul_of_one_le_left
    ((canonicalNetCoverCoefficient_pos hB hZ).le.trans hLogDegree) hR)

theorem eventually_canonical_kernel_probability_reduction_uniform {C : ℝ} (hC : 0 < C)
    (σ B Z₀ R : ℝ) (hB : 0 ≤ B) (hZ : 0 ≤ Z₀) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ k : ℕ, 0 < k → ∀ X : Set (Fin n → ℂ),
      ∀ hA : (canonicalApproxFamily k X).Finite,
      letI : Fintype (canonicalApproxFamily k X) := hA.fintype
      ∀ I : Finset (Fin n), ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
      uniformProbability (fun rows : RowSliceMatrix n d =>
        ∃ x ∈ X, (retainedShiftedMatrix I ζ rows).mulVec x = 0) ≤
        2 * (d : ℝ) ^ 2 * canonicalFamilySupProbabilitySum (canonicalApproxFamily k X) I k d R +
          uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B) := by
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_canonical_net_degree_budget_uniform hC B Z₀ R hB hZ hR] with n hConditions hBudget
  intro d hBand k hk X hA
  letI : Fintype (canonicalApproxFamily k X) := hA.fintype
  intro I ζ hShift
  have hCon := source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)
  exact canonical_kernel_probability_displayed_reduction hCon.1 hCon.2.1 hk hB hZ
    (hBudget d hBand.1) I ζ hShift X

end CircularLaw
