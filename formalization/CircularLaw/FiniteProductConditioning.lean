import CircularLaw.FiniteLawTransport
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Conditioning a finite product on all other coordinates

The expected value of any function is the iterated integral over the
selected coordinate and the literal remaining coordinates. No uniformity
or positive mass at every outcome is needed.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem finite_product_integral_split {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {m : ℕ}
    (ν : Measure α) [IsProbabilityMeasure ν] (i : Fin (m + 1))
    (f : (Fin (m + 1) → α) → ℝ) :
    (∫ rows, f rows ∂Measure.pi (fun _ : Fin (m + 1) => ν)) =
      ∫ rest, ∫ x, f (i.insertNth x rest) ∂ν ∂Measure.pi (fun _ : Fin m => ν) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i
  have hPres := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) i
  have h := hPres.symm.integral_comp e.symm.measurableEmbedding f
  rw [← h]
  exact integral_prod_symm _ Integrable.of_finite

theorem finite_product_integral_le_of_coordinate_bound {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {m : ℕ}
    (ν : Measure α) [IsProbabilityMeasure ν] (i : Fin (m + 1))
    (f : (Fin (m + 1) → α) → ℝ) (B : ℝ)
    (hB : ∀ rest, (∫ x, f (i.insertNth x rest) ∂ν) ≤ B) :
    (∫ rows, f rows ∂Measure.pi (fun _ : Fin (m + 1) => ν)) ≤ B := by
  rw [finite_product_integral_split ν i f]
  calc
    _ ≤ ∫ _ : Fin m → α, B ∂Measure.pi (fun _ : Fin m => ν) :=
      integral_mono Integrable.of_finite (integrable_const _) hB
    _ = B := by simp

end CircularLaw
