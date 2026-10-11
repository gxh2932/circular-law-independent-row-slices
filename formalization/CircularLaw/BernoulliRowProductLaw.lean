import CircularLaw.BernoulliCubeLaw
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Grouping the actual Bernoulli entry law into rows

Currying entry samples gives the product of the actual row laws. This
allows exact factorization for arbitrary functions of disjoint rows.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_row_product_map {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliCubeLaw (ρ × ι) p hp).map (Function.curry : (ρ × ι → Bool) → ρ → ι → Bool) =
      Measure.pi (fun _ : ρ => bernoulliCubeLaw ι p hp) := by
  simpa only [Measure.infinitePi_eq_pi, bernoulliCubeLaw] using
    Measure.infinitePi_map_curry (fun _ : ρ => fun _ : ι => bernoulliCoordinateLaw p hp)

theorem bernoulli_row_product_measure_preserving {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) :
    MeasurePreserving (Function.curry : (ρ × ι → Bool) → ρ → ι → Bool)
      (bernoulliCubeLaw (ρ × ι) p hp) (Measure.pi (fun _ : ρ => bernoulliCubeLaw ι p hp)) :=
  ⟨measurable_of_countable _, bernoulli_row_product_map p hp⟩

theorem bernoulli_row_product_integral {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (f : ρ → (ι → Bool) → ℝ) :
    (∫ x : ρ × ι → Bool, (∏ i, f i (fun j => x (i, j))) ∂bernoulliCubeLaw (ρ × ι) p hp) =
      ∏ i, ∫ row, f i row ∂bernoulliCubeLaw ι p hp := by
  have hIntegral := integral_map (μ := bernoulliCubeLaw (ρ × ι) p hp)
    ((bernoulli_row_product_measure_preserving (ρ := ρ) (ι := ι) p hp).measurable.aemeasurable)
    ((measurable_of_countable (fun y : ρ → ι → Bool => ∏ i, f i (y i))).aestronglyMeasurable)
  rw [bernoulli_row_product_map] at hIntegral
  exact hIntegral.symm.trans (integral_fintype_prod_eq_prod f)

theorem bernoulli_row_coordinate_measure_preserving {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (i : ρ) :
    MeasurePreserving (fun x : ρ × ι → Bool => fun j => x (i, j))
      (bernoulliCubeLaw (ρ × ι) p hp) (bernoulliCubeLaw ι p hp) :=
  (measurePreserving_eval (fun _ : ρ => bernoulliCubeLaw ι p hp) i).comp
    (bernoulli_row_product_measure_preserving p hp)

theorem bernoulli_row_coordinate_integral {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (i : ρ) (f : (ι → Bool) → ℝ) :
    (∫ x : ρ × ι → Bool, f (fun j => x (i, j)) ∂bernoulliCubeLaw (ρ × ι) p hp) =
      ∫ row, f row ∂bernoulliCubeLaw ι p hp := by
  have hIntegral := integral_map (μ := bernoulliCubeLaw (ρ × ι) p hp)
    ((bernoulli_row_coordinate_measure_preserving p hp i).measurable.aemeasurable)
    ((measurable_of_countable f).aestronglyMeasurable)
  rw [(bernoulli_row_coordinate_measure_preserving p hp i).map_eq] at hIntegral
  exact hIntegral.symm

end CircularLaw
