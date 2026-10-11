import CircularLaw.GaussianSquareMatrixLaw
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The actual independent Gaussian entry law grouped by rows

Uncurrying a product of finite row product measures is exactly the product
measure on all ordered entries. The proof checks every measurable product
rectangle. This identifies the row-exposure law with the Gaussian matrix
law already used in the singular-value calculations.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem finite_product_uncurry_law {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace E] (μ : ι × κ → Measure E) [∀ p, SigmaFinite (μ p)] :
    (Measure.pi (fun i => Measure.pi (fun j => μ (i, j)))).map
      (fun x : ι → κ → E => fun p : ι × κ => x p.1 p.2) = Measure.pi μ := by
  symm
  apply Measure.pi_eq
  intro s hs
  have hUncurry : Measurable (fun x : ι → κ → E => fun p : ι × κ => x p.1 p.2) :=
    measurable_pi_iff.mpr (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  rw [Measure.map_apply hUncurry (MeasurableSet.univ_pi hs)]
  have hPreimage : (fun x : ι → κ → E => fun p : ι × κ => x p.1 p.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Prod.forall]
  rw [hPreimage, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_prod_type]

abbrev GaussianRowsSample (m n : ℕ) := Fin m → Fin n → ℂ

def gaussianRowsLaw (m n : ℕ) : Measure (GaussianRowsSample m n) :=
  Measure.pi (fun _ => standardComplexGaussianVectorLaw n)

instance gaussianRowsLaw_probability (m n : ℕ) : IsProbabilityMeasure (gaussianRowsLaw m n) := by
  unfold gaussianRowsLaw
  infer_instance

theorem gaussian_rows_uncurry_law (m n : ℕ) :
    (gaussianRowsLaw m n).map (fun x => fun p : Fin m × Fin n => x p.1 p.2) =
      standardComplexGaussianProductLaw (Fin m × Fin n) :=
  finite_product_uncurry_law (fun _ => standardComplexGaussianLaw)

theorem gaussian_square_rows_uncurry_law (n : ℕ) :
    (gaussianRowsLaw n n).map (fun x => fun p : Fin n × Fin n => x p.1 p.2) =
      gaussianSquareMatrixLaw n := gaussian_rows_uncurry_law n n

end CircularLaw
