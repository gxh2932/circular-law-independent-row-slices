import CircularLaw.BoundedDensity
import Mathlib.Analysis.MeanInequalities

/-!
# Products of bounded-density Fourier transforms

The equal-exponent Holder step follows from pointwise arithmetic-geometric
mean and the individual Fourier-power bounds. Both integrability and the
`200/m` integral bound are proved. Relating this product to a bounded
density of a sum is a further obligation.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform BigOperators

namespace CircularLaw

theorem prod_le_mean_powers {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hm : 0 < Fintype.card ι) :
    (∏ i, u i) ≤ (1 / (Fintype.card ι : ℝ)) * ∑ i, u i ^ Fintype.card ι := by
  classical
  have hm0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
  have hw : (∑ _ : ι, 1 / (Fintype.card ι : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => 1 / (Fintype.card ι : ℝ)) (fun i => u i ^ Fintype.card ι)
    (fun _ _ => by positivity) hw (fun i _ => pow_nonneg (hu i) _)
  have hroot (i : ι) : (u i ^ Fintype.card ι) ^ (1 / (Fintype.card ι : ℝ)) = u i := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hu i)]
    rw [mul_one_div_cancel (ne_of_gt hm0), Real.rpow_one]
  simpa only [hroot, ← Finset.mul_sum] using h

theorem bounded_density_fourier_nat_power_integrable {p : ℂ → ℝ}
    (hp : UnitBoundedDensity p) {m : ℕ} (hm : 2 ≤ m) :
    Integrable (fun t => ‖𝓕 (fun x => (p x : ℂ)) t‖ ^ m) volume := by
  have h := bounded_density_fourier_power_integrable hp (q := (m : ℝ)) (by exact_mod_cast hm)
  simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using h

theorem bounded_density_fourier_product_integrable {ι : Type*} [Fintype ι]
    (p : ι → ℂ → ℝ) (hp : ∀ i, UnitBoundedDensity (p i))
    (hm : 2 ≤ Fintype.card ι) :
    Integrable (fun t => ∏ i, ‖𝓕 (fun x => (p i x : ℂ)) t‖) volume := by
  classical
  have hsum := (integrable_finset_sum Finset.univ (fun i _ =>
    bounded_density_fourier_nat_power_integrable (hp i) hm)).const_mul
      (1 / (Fintype.card ι : ℝ))
  have hmeas : Measurable (fun t => ∏ i, ‖𝓕 (fun x => (p i x : ℂ)) t‖) :=
    Finset.measurable_prod _ (fun i _ =>
      (continuous_pointwise_fourier (hp i).integrable.ofReal).norm.measurable)
  apply hsum.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_of_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _))]
  exact prod_le_mean_powers _ (fun _ => norm_nonneg _) (by omega)

theorem bounded_density_fourier_product_bound {ι : Type*} [Fintype ι]
    (p : ι → ℂ → ℝ) (hp : ∀ i, UnitBoundedDensity (p i))
    (hm : 2 ≤ Fintype.card ι) :
    (∫ t, ∏ i, ‖𝓕 (fun x => (p i x : ℂ)) t‖) ≤ 200 / (Fintype.card ι : ℝ) := by
  classical
  have hm0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (show 0 < Fintype.card ι by omega)
  have hpow (i : ι) := bounded_density_fourier_nat_power_integrable (hp i) hm
  have hsum := (integrable_finset_sum Finset.univ (fun i _ => hpow i)).const_mul
    (1 / (Fintype.card ι : ℝ))
  calc
    _ ≤ ∫ t, (1 / (Fintype.card ι : ℝ)) *
        ∑ i, ‖𝓕 (fun x => (p i x : ℂ)) t‖ ^ Fintype.card ι := by
      apply integral_mono (bounded_density_fourier_product_integrable p hp hm) hsum
      intro t
      exact prod_le_mean_powers _ (fun _ => norm_nonneg _) (by omega)
    _ = (1 / (Fintype.card ι : ℝ)) *
        ∑ i, ∫ t, ‖𝓕 (fun x => (p i x : ℂ)) t‖ ^ Fintype.card ι := by
      rw [integral_const_mul, integral_finset_sum _ (fun i _ => hpow i)]
    _ ≤ (1 / (Fintype.card ι : ℝ)) * ∑ _ : ι, 200 / (Fintype.card ι : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      have h := bounded_density_fourier_power (hp i) (q := (Fintype.card ι : ℝ))
        (by exact_mod_cast hm)
      simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using h
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

end CircularLaw
