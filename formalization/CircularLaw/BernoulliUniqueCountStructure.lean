import CircularLaw.BernoulliUniqueCountLaplace

/-!
# The two actual row contributions to a unique-neighbourhood count

The diagonal embedding determines how many rows use the zero pattern and
how many use the single-one pattern. Their exact mean and exponential
moment retain both contributions for the uniform expansion calculation.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def bernoulliUniqueInsideRows {ρ ι : Type*} [Fintype ρ]
    (e : ρ ↪ ι) (S : Finset ι) : Finset ρ := Finset.univ.filter (fun i => e i ∈ S)

theorem bernoulli_unique_inside_rows_card_le {ρ ι : Type*} [Fintype ρ]
    (e : ρ ↪ ι) (S : Finset ι) : (bernoulliUniqueInsideRows e S).card ≤ S.card := by
  have hSubset : (bernoulliUniqueInsideRows e S).image e ⊆ S := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hi).2
  calc
    _ = ((bernoulliUniqueInsideRows e S).image e).card :=
      (Finset.card_image_of_injective _ e.injective).symm
    _ ≤ _ := Finset.card_le_card hSubset

theorem bernoulli_unique_neighbourhood_mean_formula {ρ ι : Type*} [Fintype ρ]
    (p : ℝ≥0) (e : ρ ↪ ι) (S : Finset ι) :
    bernoulliUniqueNeighbourhoodMean p e S =
      ((bernoulliUniqueInsideRows e S).card : ℝ) * (1 - (p : ℝ)) ^ S.card +
        ((Fintype.card ρ - (bernoulliUniqueInsideRows e S).card : ℕ) : ℝ) *
          ((S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1)) := by
  have hOutside : (Finset.univ : Finset ρ).filter (fun i => ¬ e i ∈ S) =
      Finset.univ \ bernoulliUniqueInsideRows e S := by
    ext i
    simp [bernoulliUniqueInsideRows]
  rw [bernoulliUniqueNeighbourhoodMean]
  simp only [bernoulliUniqueRowProbability, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
  rw [hOutside, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  rfl

theorem bernoulli_unique_neighbourhood_mean_outside_lower {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1) (e : ρ ↪ ι) (S : Finset ι) :
    ((Fintype.card ρ - S.card : ℕ) : ℝ) *
      ((S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1)) ≤
        bernoulliUniqueNeighbourhoodMean p e S := by
  have hCard : ((Fintype.card ρ - S.card : ℕ) : ℝ) ≤
      ((Fintype.card ρ - (bernoulliUniqueInsideRows e S).card : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_left (bernoulli_unique_inside_rows_card_le e S) (Fintype.card ρ)
  have hpReal : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hZero : 0 ≤ (1 - (p : ℝ)) ^ S.card := pow_nonneg (sub_nonneg.mpr hpReal) _
  have hSingle : 0 ≤ (S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) p.coe_nonneg)
      (pow_nonneg (sub_nonneg.mpr hpReal) _)
  rw [bernoulli_unique_neighbourhood_mean_formula]
  exact (mul_le_mul_of_nonneg_right hCard hSingle).trans
    (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hZero))

theorem bernoulli_unique_neighbourhood_exponential_two_factors
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (e : ρ ↪ ι) (S : Finset ι) {β : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) (t : ℝ) :
    (∫ x, Real.exp (-t * ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ))
      ∂bernoulliCubeLaw (ρ × ι) p hp) =
        (1 + (Real.exp (-t) - 1) * (1 - (p : ℝ)) ^ S.card) ^
          (bernoulliUniqueInsideRows e S).card *
        (1 + (Real.exp (-t) - 1) * ((S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1))) ^
          (Fintype.card ρ - (bernoulliUniqueInsideRows e S).card) := by
  rw [bernoulli_unique_neighbourhood_exponential_integral p hp e S hβ hβOne t]
  have hPoint (i : ρ) :
      1 + (Real.exp (-t) - 1) * bernoulliUniqueRowProbability p (e i) S =
        if e i ∈ S then 1 + (Real.exp (-t) - 1) * (1 - (p : ℝ)) ^ S.card else
          1 + (Real.exp (-t) - 1) * ((S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1)) := by
    by_cases hi : e i ∈ S <;> simp only [bernoulliUniqueRowProbability, hi, if_true, if_false]
  have hOutside : (Finset.univ : Finset ρ).filter (fun i => ¬ e i ∈ S) =
      Finset.univ \ bernoulliUniqueInsideRows e S := by
    ext i
    simp [bernoulliUniqueInsideRows]
  simp_rw [hPoint]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [hOutside, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  rfl

theorem bernoulli_unique_neighbourhood_lower_tail_two_factors
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (e : ρ ↪ ι) (S : Finset ι) {β t : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) (ht : 0 ≤ t) (u : ℝ) :
    (bernoulliCubeLaw (ρ × ι) p hp).real {x |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) ≤ u} ≤
        Real.exp (t * u) *
        (1 + (Real.exp (-t) - 1) * (1 - (p : ℝ)) ^ S.card) ^
          (bernoulliUniqueInsideRows e S).card *
        (1 + (Real.exp (-t) - 1) * ((S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1))) ^
          (Fintype.card ρ - (bernoulliUniqueInsideRows e S).card) := by
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
  have hBound := (mul_le_mul_of_nonneg_left hEvent (Real.exp_pos (-t * u)).le).trans hMark
  have hMoment := bernoulli_unique_neighbourhood_exponential_two_factors p hp e S hβ hβOne t
  change (∫ x, Real.exp (-t * X x) ∂bernoulliCubeLaw (ρ × ι) p hp) = _ at hMoment
  rw [hMoment] at hBound
  calc
    _ ≤ ((1 + (Real.exp (-t) - 1) * (1 - (p : ℝ)) ^ S.card) ^
          (bernoulliUniqueInsideRows e S).card *
        (1 + (Real.exp (-t) - 1) * ((S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1))) ^
          (Fintype.card ρ - (bernoulliUniqueInsideRows e S).card)) / Real.exp (-t * u) :=
      (le_div_iff₀ (Real.exp_pos (-t * u))).mpr (by simpa only [mul_comm] using hBound)
    _ = _ := by
      rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul, neg_neg]
      ring

end CircularLaw
