import CircularLaw.TalagrandHolder
import CircularLaw.TalagrandSliceOptimization

/-!
# Talagrand's exponential moment under finite product laws

For every positive-mass set in an arbitrary finite product law,
`E exp(d_c(x,A)^2/64) <= 1/P(A)`. The induction uses the actual
slice/projection distance recursion and weighted Holder interpolation.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

variable {α : Type*} [Fintype α] {n : ℕ}

theorem talagrand_relative_probability_factor {p b : ℝ} (hp : 0 < p) (hb : 0 < b) (a : ℝ) :
    Real.exp ((1 - a) ^ 2 / 64) * ((1 / p) ^ a * (1 / b) ^ (1 - a)) =
      (1 / b) * Real.exp ((1 - a) ^ 2 / 64 - a * Real.log (p / b)) := by
  rw [Real.rpow_def_of_pos (one_div_pos.mpr hp), Real.rpow_def_of_pos (one_div_pos.mpr hb),
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hp.ne',
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hb.ne', Real.log_one,
    Real.log_div hp.ne' hb.ne']
  have hInv : 1 / b = Real.exp (-Real.log b) := by
    rw [Real.exp_neg, Real.exp_log hb, one_div]
  rw [hInv, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem talagrand_positive_slice_moment_step {μ : Fin n → α → ℝ}
    (hμ : ∀ i t, 0 ≤ μ i t) (hNorm : ∀ i, ∑ t, μ i t = 1)
    {A : Set (Fin (n + 1) → α)} {t : α}
    (hSlice : 0 < finiteProductEventMass μ (talagrandSlice A t))
    (hProjection : 0 < finiteProductEventMass μ (talagrandProjection A))
    (hSliceMoment : finiteProductExpectation μ
      (fun x => Real.exp (talagrandConvexDistance (talagrandSlice A t) x ^ 2 / 64)) ≤
        1 / finiteProductEventMass μ (talagrandSlice A t))
    (hProjectionMoment : finiteProductExpectation μ
      (fun x => Real.exp (talagrandConvexDistance (talagrandProjection A) x ^ 2 / 64)) ≤
        1 / finiteProductEventMass μ (talagrandProjection A)) :
    finiteProductExpectation μ (fun x => Real.exp (talagrandConvexDistance A (Fin.cons t x) ^ 2 / 64)) ≤
      (1 / finiteProductEventMass μ (talagrandProjection A)) *
        (2 - finiteProductEventMass μ (talagrandSlice A t) / finiteProductEventMass μ (talagrandProjection A)) := by
  let p := finiteProductEventMass μ (talagrandSlice A t)
  let b := finiteProductEventMass μ (talagrandProjection A)
  have hRatio : p / b ≤ 1 := (div_le_one hProjection).mpr
    (finiteProductEventMass_mono hμ (talagrandSlice_subset_projection A t))
  let a := talagrandSliceWeight (p / b)
  have ha := (talagrandSliceWeight_bounds hRatio).1
  have ha1 := (talagrandSliceWeight_bounds hRatio).2
  let f := fun x => talagrandConvexDistance (talagrandSlice A t) x ^ 2 / 64
  let g := fun x => talagrandConvexDistance (talagrandProjection A) x ^ 2 / 64
  have hf : ∀ x, 0 ≤ f x := fun x => div_nonneg (sq_nonneg _) (by norm_num)
  have hg : ∀ x, 0 ≤ g x := fun x => div_nonneg (sq_nonneg _) (by norm_num)
  have hPointwise (x : Fin n → α) :
      Real.exp (talagrandConvexDistance A (Fin.cons t x) ^ 2 / 64) ≤
        Real.exp ((1 - a) ^ 2 / 64) * Real.exp (a * f x + (1 - a) * g x) := by
    have hRec := talagrandConvexDistance_slice_recursion
      (finiteProductEventMass_pos_nonempty hSlice) x ha ha1
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [f, g]
    linarith
  have hHolder := finiteProductExpectation_exp_interpolation hμ hNorm hf hg ha ha1
  have hBound := mul_le_mul
    (Real.rpow_le_rpow (finiteProductExpectation_nonneg hμ (fun x => (Real.exp_pos (f x)).le))
      hSliceMoment ha)
    (Real.rpow_le_rpow (finiteProductExpectation_nonneg hμ (fun x => (Real.exp_pos (g x)).le))
      hProjectionMoment (sub_nonneg.mpr ha1))
    (Real.rpow_nonneg (finiteProductExpectation_nonneg hμ (fun x => (Real.exp_pos (g x)).le)) _)
    (Real.rpow_nonneg (one_div_nonneg.mpr hSlice.le) _)
  calc
    _ ≤ finiteProductExpectation μ
        (fun x => Real.exp ((1 - a) ^ 2 / 64) * Real.exp (a * f x + (1 - a) * g x)) :=
      finiteProductExpectation_mono hμ hPointwise
    _ = Real.exp ((1 - a) ^ 2 / 64) *
        finiteProductExpectation μ (fun x => Real.exp (a * f x + (1 - a) * g x)) :=
      finiteProductExpectation_const_mul _ _ _
    _ ≤ Real.exp ((1 - a) ^ 2 / 64) *
        (finiteProductExpectation μ (fun x => Real.exp (f x)) ^ a *
          finiteProductExpectation μ (fun x => Real.exp (g x)) ^ (1 - a)) :=
      mul_le_mul_of_nonneg_left hHolder (Real.exp_pos _).le
    _ ≤ Real.exp ((1 - a) ^ 2 / 64) * ((1 / p) ^ a * (1 / b) ^ (1 - a)) :=
      mul_le_mul_of_nonneg_left hBound (Real.exp_pos _).le
    _ = (1 / b) * Real.exp ((1 - a) ^ 2 / 64 - a * Real.log (p / b)) :=
      talagrand_relative_probability_factor hSlice hProjection a
    _ ≤ (1 / b) * (2 - p / b) := mul_le_mul_of_nonneg_left
      (talagrandSliceWeight_exponential hRatio) (one_div_nonneg.mpr hProjection.le)

theorem talagrand_zero_slice_moment_step {μ : Fin n → α → ℝ}
    (hμ : ∀ i t, 0 ≤ μ i t) {A : Set (Fin (n + 1) → α)} (t : α)
    (hProjection : 0 < finiteProductEventMass μ (talagrandProjection A))
    (hProjectionMoment : finiteProductExpectation μ
      (fun x => Real.exp (talagrandConvexDistance (talagrandProjection A) x ^ 2 / 64)) ≤
        1 / finiteProductEventMass μ (talagrandProjection A)) :
    finiteProductExpectation μ (fun x => Real.exp (talagrandConvexDistance A (Fin.cons t x) ^ 2 / 64)) ≤
      (1 / finiteProductEventMass μ (talagrandProjection A)) * 2 := by
  have hPointwise (x : Fin n → α) :
      Real.exp (talagrandConvexDistance A (Fin.cons t x) ^ 2 / 64) ≤
        Real.exp (1 / 64) * Real.exp (talagrandConvexDistance (talagrandProjection A) x ^ 2 / 64) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := talagrandConvexDistance_projection_recursion
      (finiteProductEventMass_pos_nonempty hProjection) t x
    linarith
  calc
    _ ≤ finiteProductExpectation μ (fun x =>
        Real.exp (1 / 64) * Real.exp (talagrandConvexDistance (talagrandProjection A) x ^ 2 / 64)) :=
      finiteProductExpectation_mono hμ hPointwise
    _ = Real.exp (1 / 64) * finiteProductExpectation μ
        (fun x => Real.exp (talagrandConvexDistance (talagrandProjection A) x ^ 2 / 64)) :=
      finiteProductExpectation_const_mul _ _ _
    _ ≤ Real.exp (1 / 64) * (1 / finiteProductEventMass μ (talagrandProjection A)) :=
      mul_le_mul_of_nonneg_left hProjectionMoment (Real.exp_pos _).le
    _ ≤ _ := by
      have hExp : Real.exp (1 / 64) ≤ 2 := by
        simpa only [sub_zero] using talagrand_small_slice_exponential (r := 0) (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hExp (one_div_nonneg.mpr hProjection.le)]

theorem talagrand_finite_product_moment {μ : Fin n → α → ℝ}
    (hμ : ∀ i t, 0 ≤ μ i t) (hNorm : ∀ i, ∑ t, μ i t = 1)
    (A : Set (Fin n → α)) (hA : 0 < finiteProductEventMass μ A) :
    finiteProductExpectation μ (fun x => Real.exp (talagrandConvexDistance A x ^ 2 / 64)) ≤
      1 / finiteProductEventMass μ A := by
  induction n with
  | zero =>
    obtain ⟨x, hx⟩ := finiteProductEventMass_pos_nonempty hA
    have hMem : Fin.elim0 ∈ A := (Subsingleton.elim x Fin.elim0) ▸ hx
    have hMass : finiteProductEventMass μ A = 1 := by
      rw [finiteProductEventMass, finiteProductExpectation_zero_dim, if_pos hMem]
    rw [finiteProductExpectation_zero_dim, talagrandConvexDistance_zero_of_mem hMem, hMass]
    norm_num
  | succ n ih =>
    let ν := fun i : Fin n => μ i.succ
    have hν : ∀ i t, 0 ≤ ν i t := fun i t => hμ i.succ t
    have hνNorm : ∀ i, ∑ t, ν i t = 1 := fun i => hNorm i.succ
    let b := finiteProductEventMass ν (talagrandProjection A)
    let p := finiteProductEventMass μ A
    let s := fun t => finiteProductEventMass ν (talagrandSlice A t)
    have hMass : p = ∑ t, μ 0 t * s t := finiteProductEventMass_cons μ A
    have hSubset (t : α) : s t ≤ b := finiteProductEventMass_mono hν (talagrandSlice_subset_projection A t)
    have hPb : p ≤ b := by
      rw [hMass]
      calc
        _ ≤ ∑ t, μ 0 t * b := Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hSubset t) (hμ 0 t))
        _ = b := by rw [← Finset.sum_mul, hNorm 0, one_mul]
    have hb : 0 < b := lt_of_lt_of_le hA hPb
    have hProjectionMoment := ih hν hνNorm (talagrandProjection A) hb
    have hStep (t : α) : finiteProductExpectation ν
        (fun x => Real.exp (talagrandConvexDistance A (Fin.cons t x) ^ 2 / 64)) ≤ (1 / b) * (2 - s t / b) := by
      by_cases hs : 0 < s t
      · exact talagrand_positive_slice_moment_step hν hνNorm hs hb
          (ih hν hνNorm (talagrandSlice A t) hs) hProjectionMoment
      · have hsZero : s t = 0 := le_antisymm (le_of_not_gt hs)
          (finiteProductEventMass_nonneg hν _)
        simpa only [hsZero, zero_div, sub_zero] using
          talagrand_zero_slice_moment_step hν t hb hProjectionMoment
    rw [finiteProductExpectation_cons]
    calc
      _ ≤ ∑ t, μ 0 t * ((1 / b) * (2 - s t / b)) :=
        Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hStep t) (hμ 0 t))
      _ = ∑ t, ((2 / b) * μ 0 t - ((1 / b) * (1 / b)) * (μ 0 t * s t)) := by
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = (2 / b) * 1 - ((1 / b) * (1 / b)) * p := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hNorm 0, ← hMass]
      _ = (1 / b) * (2 - p / b) := by ring
      _ ≤ 1 / p := talagrand_probability_absorption hA hb

end CircularLaw
