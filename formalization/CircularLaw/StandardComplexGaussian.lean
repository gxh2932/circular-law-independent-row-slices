import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Analysis.Complex.Basic

/-!
# The source normalization of a standard complex Gaussian

The law is the image of two independent real Gaussians with mean zero and
variance one half. Both marginals and their independence are checked for
this actual measure, rather than assumed as properties of an abstract law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace CircularLaw

def standardGaussianPairLaw : Measure (ℝ × ℝ) :=
  (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))

instance standardGaussianPairLaw_probability : IsProbabilityMeasure standardGaussianPairLaw := by
  unfold standardGaussianPairLaw
  infer_instance

theorem standardGaussianPairLaw_fst :
    standardGaussianPairLaw.map Prod.fst = gaussianReal 0 (1 / 2) := by
  simp [standardGaussianPairLaw]

theorem standardGaussianPairLaw_snd :
    standardGaussianPairLaw.map Prod.snd = gaussianReal 0 (1 / 2) := by
  simp [standardGaussianPairLaw]

theorem standardGaussianPairLaw_independent :
    IndepFun Prod.fst Prod.snd standardGaussianPairLaw :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

theorem standardGaussianPairLaw_hasGaussianLaw :
    HasGaussianLaw id standardGaussianPairLaw := by
  have hfst : HasGaussianLaw Prod.fst standardGaussianPairLaw :=
    (show HasLaw Prod.fst (gaussianReal 0 (1 / 2)) standardGaussianPairLaw from
      ⟨measurable_fst.aemeasurable, standardGaussianPairLaw_fst⟩).hasGaussianLaw
  have hsnd : HasGaussianLaw Prod.snd standardGaussianPairLaw :=
    (show HasLaw Prod.snd (gaussianReal 0 (1 / 2)) standardGaussianPairLaw from
      ⟨measurable_snd.aemeasurable, standardGaussianPairLaw_snd⟩).hasGaussianLaw
  exact standardGaussianPairLaw_independent.hasGaussianLaw hfst hsnd

def standardComplexGaussianLaw : Measure ℂ :=
  standardGaussianPairLaw.map Complex.equivRealProdCLM.symm

instance standardComplexGaussianLaw_probability : IsProbabilityMeasure standardComplexGaussianLaw :=
  Measure.isProbabilityMeasure_map (by fun_prop)

instance standardComplexGaussianLaw_gaussian : IsGaussian standardComplexGaussianLaw := by
  exact (standardGaussianPairLaw_hasGaussianLaw.map_equiv
    Complex.equivRealProdCLM.symm).isGaussian_map

theorem standardComplexGaussianLaw_re :
    standardComplexGaussianLaw.map Complex.re = gaussianReal 0 (1 / 2) := by
  rw [standardComplexGaussianLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  convert standardGaussianPairLaw_fst using 1

theorem standardComplexGaussianLaw_im :
    standardComplexGaussianLaw.map Complex.im = gaussianReal 0 (1 / 2) := by
  rw [standardComplexGaussianLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  convert standardGaussianPairLaw_snd using 1

theorem standardComplexGaussianLaw_real_prod :
    standardComplexGaussianLaw.map (fun z => (z.re, z.im)) = standardGaussianPairLaw := by
  rw [standardComplexGaussianLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  convert (Measure.map_id (μ := standardGaussianPairLaw)) using 1

theorem standardComplexGaussianLaw_independent :
    IndepFun Complex.re Complex.im standardComplexGaussianLaw := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mpr
  rw [standardComplexGaussianLaw_real_prod, standardComplexGaussianLaw_re,
    standardComplexGaussianLaw_im]
  rfl

theorem standardComplexGaussianLaw_re_mean :
    (∫ z, z.re ∂standardComplexGaussianLaw) = 0 := by
  change (∫ z, id (z.re) ∂standardComplexGaussianLaw) = 0
  rw [← integral_map (by fun_prop : AEMeasurable Complex.re standardComplexGaussianLaw)
    (by fun_prop : AEStronglyMeasurable id (standardComplexGaussianLaw.map Complex.re)),
    standardComplexGaussianLaw_re]
  exact integral_id_gaussianReal

theorem standardComplexGaussianLaw_im_mean :
    (∫ z, z.im ∂standardComplexGaussianLaw) = 0 := by
  change (∫ z, id (z.im) ∂standardComplexGaussianLaw) = 0
  rw [← integral_map (by fun_prop : AEMeasurable Complex.im standardComplexGaussianLaw)
    (by fun_prop : AEStronglyMeasurable id (standardComplexGaussianLaw.map Complex.im)),
    standardComplexGaussianLaw_im]
  exact integral_id_gaussianReal

theorem standardComplexGaussianLaw_re_variance :
    Var[Complex.re; standardComplexGaussianLaw] = (1 / 2 : ℝ) := by
  rw [← variance_id_map (by fun_prop), standardComplexGaussianLaw_re,
    variance_id_gaussianReal]
  norm_num

theorem standardComplexGaussianLaw_im_variance :
    Var[Complex.im; standardComplexGaussianLaw] = (1 / 2 : ℝ) := by
  rw [← variance_id_map (by fun_prop), standardComplexGaussianLaw_im,
    variance_id_gaussianReal]
  norm_num

end CircularLaw
