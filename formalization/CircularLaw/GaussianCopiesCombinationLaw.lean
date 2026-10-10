import CircularLaw.GaussianCombinationClusters
import CircularLaw.GaussianInnerLaw
import CircularLaw.ProjectedGaussianCopies

/-!
# Exact law of a fixed combination of Gaussian copies

The raw combination of independent standard complex Gaussian vectors has
the law of one standard vector scaled by the Euclidean coefficient norm.
Orthogonal projection commutes with that combination. In particular, every
fixed unit coefficient vector gives the actual projected Gaussian law.
These identities do not assert a uniform estimate over coefficient vectors.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CircularLaw

def gaussianVectorVarianceCoefficient {n : ℕ} (L : (Fin n → ℂ) →L[ℝ] ℝ) : ℝ :=
  ∑ j, ((L (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j 1)) ^ 2 +
    (L (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j Complex.I)) ^ 2)

theorem standardComplexGaussianVectorLaw_charFunDual {n : ℕ}
    (L : (Fin n → ℂ) →L[ℝ] ℝ) :
    charFunDual (standardComplexGaussianVectorLaw n) L =
      Complex.exp (-((gaussianVectorVarianceCoefficient L / 4 : ℝ) : ℂ)) := by
  rw [standardComplexGaussianVectorLaw, charFunDual_pi]
  simp only [standardComplexGaussianLaw_charFunDual, ContinuousLinearMap.comp_apply]
  rw [← Complex.exp_sum, Finset.sum_neg_distrib, ← Complex.ofReal_sum, ← Finset.sum_div]
  rfl

def gaussianRawCopiesCombination {n p : ℕ} (x : EuclideanSpace ℂ (Fin p)) :
    (Fin p → (Fin n → ℂ)) →L[ℂ] (Fin n → ℂ) :=
  ∑ k, x k • ContinuousLinearMap.proj k

theorem gaussianRawCopiesCombination_apply {n p : ℕ}
    (x : EuclideanSpace ℂ (Fin p)) (z : Fin p → (Fin n → ℂ)) (j : Fin n) :
    gaussianRawCopiesCombination x z j = ∑ k, x k * z k j := by
  simp [gaussianRawCopiesCombination, Finset.sum_apply]

theorem gaussianRawCopiesCombination_single {n p : ℕ}
    (x : EuclideanSpace ℂ (Fin p)) (k : Fin p) (a : Fin n → ℂ) :
    gaussianRawCopiesCombination x
      (ContinuousLinearMap.single ℝ (fun _ : Fin p => (Fin n → ℂ)) k a) = x k • a := by
  ext j
  simp [gaussianRawCopiesCombination_apply, ContinuousLinearMap.single_apply,
    Pi.single_apply, ite_apply]

theorem gaussianRawCopiesCombination_double_single {n p : ℕ}
    (x : EuclideanSpace ℂ (Fin p)) (k : Fin p) (j : Fin n) (a : ℂ) :
    gaussianRawCopiesCombination x
      (ContinuousLinearMap.single ℝ (fun _ : Fin p => (Fin n → ℂ)) k
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j a)) =
      ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j (x k * a) := by
  rw [gaussianRawCopiesCombination_single]
  ext i
  simp [ContinuousLinearMap.single_apply, Pi.single_apply]

theorem gaussianRawCopiesCombination_variance {n p : ℕ}
    (x : EuclideanSpace ℂ (Fin p)) (L : (Fin n → ℂ) →L[ℝ] ℝ) :
    (∑ k : Fin p, gaussianVectorVarianceCoefficient
      ((L.comp ((gaussianRawCopiesCombination x).restrictScalars ℝ)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin p => (Fin n → ℂ)) k))) =
      gaussianVectorVarianceCoefficient L * ‖x‖ ^ 2 := by
  simp only [gaussianVectorVarianceCoefficient, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  simp_rw [gaussianRawCopiesCombination_double_single]
  simp only [mul_one]
  have hRotate (k : Fin p) (j : Fin n) :
      (L (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j (x k))) ^ 2 +
        (L (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j (x k * Complex.I))) ^ 2 =
      ((L (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j 1)) ^ 2 +
        (L (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j Complex.I)) ^ 2) * ‖x k‖ ^ 2 := by
    simpa only [ContinuousLinearMap.comp_apply, mul_comm (x k) Complex.I] using
      complex_realForm_rotated_norm_sq
        (L.comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)) (x k)
  simp_rw [hRotate, ← Finset.sum_mul]
  rw [← Finset.mul_sum, EuclideanSpace.norm_sq_eq]

theorem gaussianVectorVarianceCoefficient_scale {n : ℕ}
    (L : (Fin n → ℂ) →L[ℝ] ℝ) (a : ℝ) :
    gaussianVectorVarianceCoefficient (L.comp (a • ContinuousLinearMap.id ℝ (Fin n → ℂ))) =
      a ^ 2 * gaussianVectorVarianceCoefficient L := by
  simp only [gaussianVectorVarianceCoefficient, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, mul_pow]
  simp_rw [← mul_add]
  rw [← Finset.mul_sum]

theorem gaussianRawCopiesCombination_law {n p : ℕ} (x : EuclideanSpace ℂ (Fin p)) :
    (standardGaussianCopiesLaw n p).map (gaussianRawCopiesCombination x) =
      (standardComplexGaussianVectorLaw n).map
        (‖x‖ • ContinuousLinearMap.id ℝ (Fin n → ℂ)) := by
  let F := (gaussianRawCopiesCombination (n := n) x).restrictScalars ℝ
  let S : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    ‖x‖ • ContinuousLinearMap.id ℝ (Fin n → ℂ)
  haveI : IsProbabilityMeasure ((standardGaussianCopiesLaw n p).map F) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure ((standardComplexGaussianVectorLaw n).map S) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  change (standardGaussianCopiesLaw n p).map F = (standardComplexGaussianVectorLaw n).map S
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, standardGaussianCopiesLaw, charFunDual_pi]
  simp only [standardComplexGaussianVectorLaw_charFunDual]
  rw [← Complex.exp_sum, charFunDual_map, standardComplexGaussianVectorLaw_charFunDual]
  change Complex.exp (∑ k : Fin p, -((gaussianVectorVarianceCoefficient
      ((L.comp ((gaussianRawCopiesCombination x).restrictScalars ℝ)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin p => (Fin n → ℂ)) k)) / 4 : ℝ) : ℂ)) =
    Complex.exp (-((gaussianVectorVarianceCoefficient
      (L.comp (‖x‖ • ContinuousLinearMap.id ℝ (Fin n → ℂ))) / 4 : ℝ) : ℂ))
  rw [Finset.sum_neg_distrib, ← Complex.ofReal_sum, ← Finset.sum_div,
    gaussianRawCopiesCombination_variance, gaussianVectorVarianceCoefficient_scale]
  congr 3
  ring

theorem gaussianRawCopiesCombination_unit_law {n p : ℕ}
    (x : EuclideanSpace ℂ (Fin p)) (hx : ‖x‖ = 1) :
    (standardGaussianCopiesLaw n p).map (gaussianRawCopiesCombination x) =
      standardComplexGaussianVectorLaw n := by
  rw [gaussianRawCopiesCombination_law, hx]
  simp

theorem projectedGaussianCopiesCombination_eq {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin p))
    (z : Fin p → (Fin n → ℂ)) :
    gaussianCopiesCombination (projectedGaussianCopies E z) x =
      projectedComplexGaussian E (gaussianRawCopiesCombination x z) := by
  let P : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    (Eᗮ.starProjection : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap
  change gaussianCopiesCombination (fun k => P (z k)) x = P (gaussianRawCopiesCombination x z)
  rw [gaussianCopiesCombination_apply]
  simp [gaussianRawCopiesCombination]

theorem projectedGaussianCopiesCombination_continuous {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin p)) :
    Continuous (fun z => gaussianCopiesCombination (projectedGaussianCopies E z) x) := by
  simp_rw [projectedGaussianCopiesCombination_eq]
  exact (projectedComplexGaussian_continuous E).comp (gaussianRawCopiesCombination x).continuous

theorem projectedComplexGaussian_real_smul {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (a : ℝ) (z : Fin n → ℂ) :
    projectedComplexGaussian E (a • z) = a • projectedComplexGaussian E z := by
  let P : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    (Eᗮ.starProjection : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap
  exact P.map_smul_of_tower a z

theorem projectedGaussianCopiesCombination_law {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin p)) :
    (standardGaussianCopiesLaw n p).map
      (fun z => gaussianCopiesCombination (projectedGaussianCopies E z) x) =
      (projectedComplexGaussianLaw E).map
        (‖x‖ • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))) := by
  simp_rw [projectedGaussianCopiesCombination_eq]
  change (standardGaussianCopiesLaw n p).map
    (projectedComplexGaussian E ∘ gaussianRawCopiesCombination x) = _
  rw [← Measure.map_map (projectedComplexGaussian_continuous E).measurable
    (gaussianRawCopiesCombination x).measurable, gaussianRawCopiesCombination_law,
    Measure.map_map (projectedComplexGaussian_continuous E).measurable (by fun_prop)]
  unfold projectedComplexGaussianLaw
  rw [Measure.map_map (by fun_prop) (projectedComplexGaussian_continuous E).measurable]
  congr 1
  funext z
  exact projectedComplexGaussian_real_smul E ‖x‖ z

theorem projectedGaussianCopiesCombination_unit_law {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin p))
    (hx : ‖x‖ = 1) :
    (standardGaussianCopiesLaw n p).map
      (fun z => gaussianCopiesCombination (projectedGaussianCopies E z) x) =
      projectedComplexGaussianLaw E := by
  rw [projectedGaussianCopiesCombination_law, hx]
  simp

theorem projectedGaussianCopiesCombination_hasGaussianLaw {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin p)) :
    HasGaussianLaw (fun z => gaussianCopiesCombination (projectedGaussianCopies E z) x)
      (standardGaussianCopiesLaw n p) := by
  let S : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    ‖x‖ • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))
  haveI : IsGaussian ((projectedComplexGaussianLaw E).map S) :=
    ((IsGaussian.hasGaussianLaw_id (μ := projectedComplexGaussianLaw E)).map_fun S).isGaussian_map
  exact (show HasLaw (fun z => gaussianCopiesCombination (projectedGaussianCopies E z) x)
      ((projectedComplexGaussianLaw E).map S) (standardGaussianCopiesLaw n p) from
    ⟨(projectedGaussianCopiesCombination_continuous E x).measurable.aemeasurable,
      projectedGaussianCopiesCombination_law E x⟩).hasGaussianLaw

theorem projectedGaussianCopiesCombination_unit_event {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin p))
    (hx : ‖x‖ = 1) (A : Set (EuclideanSpace ℂ (Fin n))) (hA : MeasurableSet A) :
    (standardGaussianCopiesLaw n p) {z | gaussianCopiesCombination (projectedGaussianCopies E z) x ∈ A} =
      projectedComplexGaussianLaw E A := by
  have h := Measure.map_apply (μ := standardGaussianCopiesLaw n p)
    (projectedGaussianCopiesCombination_continuous E x).measurable hA
  rw [projectedGaussianCopiesCombination_unit_law E x hx] at h
  exact h.symm

theorem projectedGaussianCopiesCombination_unit_event_real {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin p))
    (hx : ‖x‖ = 1) (A : Set (EuclideanSpace ℂ (Fin n))) (hA : MeasurableSet A) :
    (standardGaussianCopiesLaw n p).real
      {z | gaussianCopiesCombination (projectedGaussianCopies E z) x ∈ A} =
      (projectedComplexGaussianLaw E).real A :=
  congrArg ENNReal.toReal (projectedGaussianCopiesCombination_unit_event E x hx A hA)

end CircularLaw
