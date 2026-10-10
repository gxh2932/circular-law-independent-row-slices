import CircularLaw.BernoulliUniqueRowLaw
import CircularLaw.BernoulliRowProductLaw
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Actual unique-neighbourhood exponential moments and lower tails

The selected-row indicators factor under the actual entry law. Their
exact exponential moment gives a fixed-set lower tail with no assumed
independence or concentration estimate.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def bernoulliUniqueNeighbourhoodMean {ρ ι : Type*} [Fintype ρ]
    (p : ℝ≥0) (e : ρ ↪ ι) (S : Finset ι) : ℝ :=
  ∑ i, bernoulliUniqueRowProbability p (e i) S

theorem bernoulli_unique_neighbourhood_card_eq_sum {ρ ι : Type*} [Fintype ρ]
    (x : ρ × ι → Bool) (e : ρ ↪ ι) (S : Finset ι)
    {β : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) :
    ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) =
      ∑ i, bernoulliUniqueRowIndicator (e i) S (fun j => x (i, j)) := by
  simp only [matrixUniqueNeighbourhood, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have hEvent := bernoulli_unique_neighbourhood_row_event x e S i hβ hβOne
  simp only [matrixUniqueNeighbourhood, Finset.mem_filter, Finset.mem_univ, true_and] at hEvent
  simp only [hEvent, bernoulliUniqueRowIndicator]
  split_ifs <;> norm_num

theorem bernoulli_unique_neighbourhood_mean_nonneg {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (e : ρ ↪ ι) (S : Finset ι) :
    0 ≤ bernoulliUniqueNeighbourhoodMean p e S :=
  Finset.sum_nonneg (fun i _ => (bernoulli_unique_row_probability_bounds p hp (e i) S).1)

theorem bernoulli_unique_neighbourhood_exponential_integral
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (e : ρ ↪ ι) (S : Finset ι) {β : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) (t : ℝ) :
    (∫ x, Real.exp (-t * ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ))
      ∂bernoulliCubeLaw (ρ × ι) p hp) =
        ∏ i, (1 + (Real.exp (-t) - 1) * bernoulliUniqueRowProbability p (e i) S) := by
  simp_rw [bernoulli_unique_neighbourhood_card_eq_sum _ e S hβ hβOne]
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [bernoulli_row_product_integral p hp
    (fun i row => Real.exp (-t * bernoulliUniqueRowIndicator (e i) S row))]
  simp_rw [bernoulli_unique_row_exponential_integral]

theorem bernoulli_unique_neighbourhood_exponential_integral_le
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (e : ρ ↪ ι) (S : Finset ι) {β : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) (t : ℝ) :
    (∫ x, Real.exp (-t * ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ))
      ∂bernoulliCubeLaw (ρ × ι) p hp) ≤
        Real.exp ((Real.exp (-t) - 1) * bernoulliUniqueNeighbourhoodMean p e S) := by
  rw [bernoulli_unique_neighbourhood_exponential_integral p hp e S hβ hβOne t]
  have hNonneg (i : ρ) : 0 ≤ 1 + (Real.exp (-t) - 1) * bernoulliUniqueRowProbability p (e i) S := by
    obtain ⟨hZero, hOne⟩ := bernoulli_unique_row_probability_bounds p hp (e i) S
    have h := mul_nonneg (Real.exp_pos (-t)).le hZero
    nlinarith
  calc
    _ ≤ ∏ i, Real.exp ((Real.exp (-t) - 1) * bernoulliUniqueRowProbability p (e i) S) :=
      Finset.prod_le_prod (fun i _ => hNonneg i) (fun i _ => by
        simpa only [add_comm] using Real.add_one_le_exp
          ((Real.exp (-t) - 1) * bernoulliUniqueRowProbability p (e i) S))
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]; rfl

theorem bernoulli_unique_neighbourhood_lower_tail
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (e : ρ ↪ ι) (S : Finset ι) {β t : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) (ht : 0 ≤ t) (u : ℝ) :
    (bernoulliCubeLaw (ρ × ι) p hp).real {x |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) ≤ u} ≤
        Real.exp (t * u + (Real.exp (-t) - 1) * bernoulliUniqueNeighbourhoodMean p e S) := by
  let X := fun x : ρ × ι → Bool =>
    ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ)
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (bernoulliCubeLaw (ρ × ι) p hp) (fun x => (Real.exp_pos (-t * X x)).le))
    (Integrable.of_finite : Integrable (fun x => Real.exp (-t * X x))
      (bernoulliCubeLaw (ρ × ι) p hp)) (Real.exp (-t * u))
  have hSubset : {x | X x ≤ u} ⊆ {x | Real.exp (-t * u) ≤ Real.exp (-t * X x)} := by
    intro x hx
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr ht))
  have hEvent := measureReal_mono (μ := bernoulliCubeLaw (ρ × ι) p hp) hSubset
  have hBound := ((mul_le_mul_of_nonneg_left hEvent (Real.exp_pos (-t * u)).le).trans hMark).trans
    (bernoulli_unique_neighbourhood_exponential_integral_le p hp e S hβ hβOne t)
  calc
    _ ≤ Real.exp ((Real.exp (-t) - 1) * bernoulliUniqueNeighbourhoodMean p e S) /
        Real.exp (-t * u) := (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hBound)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

theorem bernoulli_unique_neighbourhood_half_mean_lower_tail
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (e : ρ ↪ ι) (S : Finset ι) {β u : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) (hu : u ≤ bernoulliUniqueNeighbourhoodMean p e S / 2) :
    (bernoulliCubeLaw (ρ × ι) p hp).real {x |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) ≤ u} ≤
        Real.exp (-bernoulliUniqueNeighbourhoodMean p e S / 8) := by
  apply (bernoulli_unique_neighbourhood_lower_tail p hp e S hβ hβOne (by norm_num : (0 : ℝ) ≤ 1) u).trans
  apply Real.exp_le_exp.mpr
  have hExp : Real.exp (-1) ≤ 3 / 8 := by linarith [Real.exp_neg_one_lt_d9]
  have hMean := bernoulli_unique_neighbourhood_mean_nonneg p hp e S
  nlinarith [mul_le_mul_of_nonneg_right hExp hMean]

theorem bernoulli_unique_neighbourhood_card_integral
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (e : ρ ↪ ι) (S : Finset ι) {β : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) :
    (∫ x, ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ)
      ∂bernoulliCubeLaw (ρ × ι) p hp) = bernoulliUniqueNeighbourhoodMean p e S := by
  simp_rw [bernoulli_unique_neighbourhood_card_eq_sum _ e S hβ hβOne]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  have hCoordinate (i : ρ) :
      (∫ x : ρ × ι → Bool, bernoulliUniqueRowIndicator (e i) S (fun j => x (i, j))
        ∂bernoulliCubeLaw (ρ × ι) p hp) = bernoulliUniqueRowProbability p (e i) S := by
    rw [bernoulli_row_coordinate_integral p hp i (bernoulliUniqueRowIndicator (e i) S),
      bernoulli_unique_row_indicator_integral]
  simp_rw [hCoordinate]
  rfl

end CircularLaw
