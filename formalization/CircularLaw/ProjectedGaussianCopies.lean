import CircularLaw.ProjectedComplexGaussian

/-!
# Independent copies of the actual projected complex Gaussian

The sample law is the finite product of the existing Gaussian vector law.
Each projected copy has the actual projected marginal, and the copies are
independent. All statements use the same finite-dimensional sample space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace CircularLaw

def standardGaussianCopiesLaw (n p : ℕ) : Measure (Fin p → (Fin n → ℂ)) :=
  Measure.pi (fun _ => standardComplexGaussianVectorLaw n)

instance standardGaussianCopiesLaw_probability (n p : ℕ) :
    IsProbabilityMeasure (standardGaussianCopiesLaw n p) := by
  unfold standardGaussianCopiesLaw
  infer_instance

theorem standardGaussianCopiesLaw_coordinate {n p : ℕ} (k : Fin p) :
    (standardGaussianCopiesLaw n p).map (fun z => z k) = standardComplexGaussianVectorLaw n :=
  (measurePreserving_eval (fun _ : Fin p => standardComplexGaussianVectorLaw n) k).map_eq

theorem standardGaussianCopiesLaw_independent (n p : ℕ) :
    iIndepFun (fun k (z : Fin p → (Fin n → ℂ)) => z k) (standardGaussianCopiesLaw n p) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)

def projectedGaussianCopies {n p : ℕ} (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (z : Fin p → (Fin n → ℂ)) (k : Fin p) : EuclideanSpace ℂ (Fin n) :=
  projectedComplexGaussian E (z k)

theorem projectedGaussianCopies_continuous {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (k : Fin p) :
    Continuous (fun z => projectedGaussianCopies E z k) :=
  (projectedComplexGaussian_continuous E).comp (continuous_apply k)

theorem projectedGaussianCopies_independent {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    iIndepFun (fun k (z : Fin p → (Fin n → ℂ)) => projectedGaussianCopies E z k)
      (standardGaussianCopiesLaw n p) :=
  iIndepFun_pi (X := fun _ => projectedComplexGaussian E)
    (fun _ => (projectedComplexGaussian_continuous E).measurable.aemeasurable)

theorem projectedGaussianCopies_law {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (k : Fin p) :
    (standardGaussianCopiesLaw n p).map (fun z => projectedGaussianCopies E z k) =
      projectedComplexGaussianLaw E := by
  unfold projectedGaussianCopies projectedComplexGaussianLaw
  change (standardGaussianCopiesLaw n p).map
    (projectedComplexGaussian E ∘ (fun z => z k)) = _
  rw [← Measure.map_map (projectedComplexGaussian_continuous E).measurable
    (measurable_pi_apply k), standardGaussianCopiesLaw_coordinate]

theorem projectedGaussianCopies_hasGaussianLaw {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (k : Fin p) :
    HasGaussianLaw (fun z => projectedGaussianCopies E z k) (standardGaussianCopiesLaw n p) := by
  exact (show HasLaw (fun z => projectedGaussianCopies E z k)
    (projectedComplexGaussianLaw E) (standardGaussianCopiesLaw n p) from
      ⟨(projectedGaussianCopies_continuous E k).measurable.aemeasurable,
        projectedGaussianCopies_law E k⟩).hasGaussianLaw

theorem projectedGaussianCopies_jointGaussian {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    HasGaussianLaw (fun z k => projectedGaussianCopies E z k) (standardGaussianCopiesLaw n p) :=
  (projectedGaussianCopies_independent E).hasGaussianLaw
    (fun k => projectedGaussianCopies_hasGaussianLaw E k)

theorem projectedGaussianCopies_pair_tail {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (k : Fin p) (i j : Fin n) (α : ℝ) :
    (standardGaussianCopiesLaw n p).real
      {z | α ≤ ‖projectedGaussianCopies E z k i - projectedGaussianCopies E z k j‖} =
    (standardComplexGaussianVectorLaw n).real
      {z | α ≤ ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j‖} := by
  have hMeas : MeasurableSet
      {z | α ≤ ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j‖} :=
    (isClosed_le continuous_const
      (((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).comp
        (projectedComplexGaussian_continuous E)).sub
          ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
            (projectedComplexGaussian_continuous E))).norm).measurableSet
  have h := map_measureReal_apply (μ := standardGaussianCopiesLaw n p)
    (measurable_pi_apply k) hMeas
  rw [standardGaussianCopiesLaw_coordinate] at h
  exact h.symm

end CircularLaw
