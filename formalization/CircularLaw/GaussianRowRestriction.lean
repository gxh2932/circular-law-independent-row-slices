import CircularLaw.GaussianProductCurry
import Mathlib.Probability.Independence.Basic

/-!
# Every selected set of Gaussian matrix rows has its actual product law

Injective coordinate selection preserves a finite identical probability
product. The exact uncurrying law applies this to any row restriction of
the independent-entry square Gaussian matrix.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory

namespace CircularLaw

theorem finite_probability_product_select_law {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν] (f : κ ↪ ι) :
    (Measure.pi (fun _ : ι => ν)).map (fun x j => x (f j)) =
      Measure.pi (fun _ : κ => ν) := by
  have hInd : iIndepFun (fun i : ι => fun x : ι → E => x i) (Measure.pi (fun _ : ι => ν)) :=
    iIndepFun_pi (X := fun _ : ι => id) (fun _ => measurable_id.aemeasurable)
  have hSelect := iIndepFun.precomp f.injective hInd
  have hLaw := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j : κ => (measurable_pi_apply (f j)).aemeasurable)).mp hSelect
  have hMarg (j : κ) :
      (Measure.pi (fun _ : ι => ν)).map (fun x => x (f j)) = ν :=
    (measurePreserving_eval (fun _ : ι => ν) (f j)).map_eq
  simpa only [hMarg] using hLaw

theorem gaussian_square_row_restriction_law {m n : ℕ} (f : Fin m ↪ Fin n) :
    (gaussianSquareMatrixLaw n).map (fun x i j => x (f i, j)) = gaussianRowsLaw m n := by
  have hUncurry : Measurable (fun x : GaussianRowsSample n n => fun p : Fin n × Fin n => x p.1 p.2) :=
    measurable_pi_iff.mpr (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  have hSelect : Measurable (fun x : GaussianSquareSample n => fun i : Fin m => fun j => x (f i, j)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j => measurable_pi_apply (f i, j)))
  rw [← gaussian_square_rows_uncurry_law, Measure.map_map hSelect hUncurry]
  exact finite_probability_product_select_law (standardComplexGaussianVectorLaw n) f

end CircularLaw
