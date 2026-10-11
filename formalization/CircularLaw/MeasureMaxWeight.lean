import CircularLaw.MaxWeight

/-!
# Max weights under an arbitrary probability law

The finite-coordinate argument extends to measurable, bounded observables.
All integrability obligations are discharged from boundedness. Product
measures encode independent copies; no moment or concentration estimate is
assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem integrable_of_abs_bound {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using hC x)

theorem integrable_of_diameter_bound {α : Type*} [MeasurableSpace α] [Nonempty α]
    (ν : Measure α) [IsFiniteMeasure ν] {b : α → ℝ} (hb : Measurable b)
    {R : ℝ} (hrange : ∀ x y, |b x - b y| ≤ R) : Integrable b ν := by
  let x₀ := Classical.choice (inferInstance : Nonempty α)
  apply integrable_of_abs_bound ν hb (C := R + |b x₀|)
  intro x
  calc
    |b x| = |(b x - b x₀) + b x₀| := by congr 1; ring
    _ ≤ |b x - b x₀| + |b x₀| := abs_add_le _ _
    _ ≤ _ := by gcongr; exact hrange x x₀

def measureDispersion {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (b : α → ℝ) : ℝ :=
  ∫ p : α × α, |b p.1 - b p.2| ∂ν.prod ν

theorem measureDispersion_nonneg {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (b : α → ℝ) : 0 ≤ measureDispersion ν b :=
  integral_nonneg fun _ => abs_nonneg _

theorem abs_sub_integral_le_range {α : Type*} [MeasurableSpace α] [Nonempty α]
    (ν : Measure α) [IsProbabilityMeasure ν] {b : α → ℝ} (hb : Measurable b)
    {R : ℝ} (hrange : ∀ x y, |b x - b y| ≤ R) (x : α) :
    |b x - ∫ y, b y ∂ν| ≤ R := by
  have hi := integrable_of_diameter_bound ν hb hrange
  have hid : (∫ y, b x - b y ∂ν) = b x - ∫ y, b y ∂ν := by
    rw [integral_sub (integrable_const _) hi]
    simp
  rw [← hid]
  calc
    _ ≤ ∫ y, |b x - b y| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ _y : α, R ∂ν := integral_mono ((integrable_const _).sub hi).abs
      (integrable_const _) (hrange x)
    _ = R := by simp

theorem integral_pair_max {α : Type*} [MeasurableSpace α] [Nonempty α]
    (ν : Measure α) [IsProbabilityMeasure ν] {b : α → ℝ} (hb : Measurable b)
    {R : ℝ} (hrange : ∀ x y, |b x - b y| ≤ R) :
    (∫ p : α × α, max (b p.1) (b p.2) ∂ν.prod ν) =
      (∫ x, b x ∂ν) + measureDispersion ν b / 2 := by
  have hi := integrable_of_diameter_bound ν hb hrange
  have hsum : (∫ p : α × α, b p.1 + b p.2 + |b p.1 - b p.2| ∂ν.prod ν) =
      (∫ p : α × α, b p.1 + b p.2 ∂ν.prod ν) + measureDispersion ν b :=
    integral_add ((hi.comp_fst ν).add (hi.comp_snd ν))
      ((hi.comp_fst ν).sub (hi.comp_snd ν)).abs
  have hsum' : (∫ p : α × α, b p.1 + b p.2 ∂ν.prod ν) =
      (∫ p : α × α, b p.1 ∂ν.prod ν) + ∫ p : α × α, b p.2 ∂ν.prod ν :=
    integral_add (hi.comp_fst ν) (hi.comp_snd ν)
  have hmax (x y : ℝ) : max x y = (x + y + |x - y|) / 2 := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp_rw [hmax, div_eq_mul_inv]
  rw [integral_mul_const, hsum, hsum',
    integral_fun_fst, integral_fun_snd]
  simp only [probReal_univ, one_smul]
  ring

theorem integral_exp_le_quadratic {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] {x : α → ℝ} (hx : Measurable x)
    (hbound : ∀ a, |x a| ≤ 1) :
    (∫ a, Real.exp (x a) ∂ν) ≤ 1 + (∫ a, x a ∂ν) + ∫ a, (x a) ^ 2 ∂ν := by
  have hi := integrable_of_abs_bound ν hx hbound
  have hisq : Integrable (fun a => (x a) ^ 2) ν := by
    apply integrable_of_abs_bound ν (hx.pow_const 2) (C := 1)
    intro a
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (x a), hbound a, abs_nonneg (x a)]
  have hie : Integrable (fun a => Real.exp (x a)) ν := by
    apply integrable_of_abs_bound ν hx.exp (C := Real.exp 1)
    intro a
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hbound a))
  have hsum : Integrable (fun a => (1 : ℝ) + x a) ν := (integrable_const 1).add hi
  calc
    _ ≤ ∫ a, 1 + x a + (x a) ^ 2 ∂ν := by
      apply integral_mono hie (hsum.add hisq)
      intro a
      change Real.exp (x a) ≤ 1 + x a + (x a) ^ 2
      have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hbound a))).2
      linarith
    _ = _ := by rw [integral_add hsum hisq,
      integral_add (integrable_const (1 : ℝ)) hi]; simp

theorem integrable_sq_of_abs_bound {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] {x : α → ℝ} (hx : Measurable x)
    {R : ℝ} (hbound : ∀ a, |x a| ≤ R) : Integrable (fun a => (x a) ^ 2) ν := by
  apply integrable_of_abs_bound ν (hx.pow_const 2) (C := R ^ 2)
  intro a
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (x a), hbound a, abs_nonneg (x a)]

theorem abs_max_sub_le {x y c R : ℝ} (hx : |x - c| ≤ R) (hy : |y - c| ≤ R) :
    |max x y - c| ≤ R := by
  rcases le_total x y with h | h
  · simpa only [max_eq_right h] using hy
  · simpa only [max_eq_left h] using hx

theorem integral_pair_sq_diff {α : Type*} [MeasurableSpace α] [Nonempty α]
    (ν : Measure α) [IsProbabilityMeasure ν] {b : α → ℝ} (hb : Measurable b)
    {R : ℝ} (hrange : ∀ x y, |b x - b y| ≤ R) :
    (∫ p : α × α, (b p.1 - b p.2) ^ 2 ∂ν.prod ν) =
      2 * ∫ x, (b x - ∫ y, b y ∂ν) ^ 2 ∂ν := by
  let X := fun x => b x - ∫ y, b y ∂ν
  have hX : Measurable X := hb.sub measurable_const
  have hi : Integrable X ν :=
    (integrable_of_diameter_bound ν hb hrange).sub (integrable_const _)
  have hisq := integrable_sq_of_abs_bound ν hX (abs_sub_integral_le_range ν hb hrange)
  have hzero : (∫ x, X x ∂ν) = 0 := by
    dsimp [X]
    rw [integral_sub (integrable_of_diameter_bound ν hb hrange) (integrable_const _)]
    simp
  have hexpand (p : α × α) : (b p.1 - b p.2) ^ 2 =
      (X p.1) ^ 2 + (X p.2) ^ 2 - 2 * (X p.1 * X p.2) := by dsimp [X]; ring
  have hsub : (∫ p : α × α, (X p.1) ^ 2 + (X p.2) ^ 2 -
      2 * (X p.1 * X p.2) ∂ν.prod ν) =
      (∫ p : α × α, (X p.1) ^ 2 + (X p.2) ^ 2 ∂ν.prod ν) -
        ∫ p : α × α, 2 * (X p.1 * X p.2) ∂ν.prod ν :=
    integral_sub ((hisq.comp_fst ν).add (hisq.comp_snd ν))
      ((hi.mul_prod hi).const_mul 2)
  have hadd : (∫ p : α × α, (X p.1) ^ 2 + (X p.2) ^ 2 ∂ν.prod ν) =
      (∫ p : α × α, (X p.1) ^ 2 ∂ν.prod ν) +
        ∫ p : α × α, (X p.2) ^ 2 ∂ν.prod ν :=
    integral_add (hisq.comp_fst ν) (hisq.comp_snd ν)
  simp_rw [hexpand]
  rw [hsub, hadd, integral_const_mul, integral_prod_mul, hzero,
    integral_fun_fst (fun x => (X x) ^ 2), integral_fun_snd (fun x => (X x) ^ 2)]
  simp only [probReal_univ, one_smul, mul_zero, sub_zero]
  dsimp [X]
  ring

theorem integral_max_centered_sq_le {α : Type*} [MeasurableSpace α] [Nonempty α]
    (ν : Measure α) [IsProbabilityMeasure ν] {b : α → ℝ} (hb : Measurable b)
    {R : ℝ} (hrange : ∀ x y, |b x - b y| ≤ R) :
    (∫ p : α × α, (max (b p.1) (b p.2) - ∫ y, b y ∂ν) ^ 2 ∂ν.prod ν) ≤
      ∫ p : α × α, (b p.1 - b p.2) ^ 2 ∂ν.prod ν := by
  let X := fun x => b x - ∫ y, b y ∂ν
  have hX : Measurable X := hb.sub measurable_const
  have hbound := abs_sub_integral_le_range ν hb hrange
  have hisq := integrable_sq_of_abs_bound ν hX hbound
  have himax : Integrable (fun p : α × α =>
      (max (b p.1) (b p.2) - ∫ y, b y ∂ν) ^ 2) (ν.prod ν) :=
    integrable_sq_of_abs_bound (ν.prod ν)
      (((hb.comp measurable_fst).max (hb.comp measurable_snd)).sub measurable_const)
      (fun p => abs_max_sub_le (hbound p.1) (hbound p.2))
  calc
    _ ≤ ∫ p : α × α, (X p.1) ^ 2 + (X p.2) ^ 2 ∂ν.prod ν := by
      apply integral_mono himax ((hisq.comp_fst ν).add (hisq.comp_snd ν))
      intro p
      change (max (b p.1) (b p.2) - ∫ y, b y ∂ν) ^ 2 ≤ (X p.1) ^ 2 + (X p.2) ^ 2
      dsimp [X]
      rcases le_total (b p.1) (b p.2) with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg (b p.1 - ∫ y, b y ∂ν)]
      · rw [max_eq_left h]; nlinarith [sq_nonneg (b p.2 - ∫ y, b y ∂ν)]
    _ = _ := by
      have hadd : (∫ p : α × α, (X p.1) ^ 2 + (X p.2) ^ 2 ∂ν.prod ν) =
          (∫ p : α × α, (X p.1) ^ 2 ∂ν.prod ν) +
            ∫ p : α × α, (X p.2) ^ 2 ∂ν.prod ν :=
        integral_add (hisq.comp_fst ν) (hisq.comp_snd ν)
      rw [hadd, integral_fun_fst (fun x => (X x) ^ 2),
        integral_fun_snd (fun x => (X x) ^ 2), integral_pair_sq_diff ν hb hrange]
      simp only [probReal_univ, one_smul]
      dsimp [X]
      ring

theorem integral_pair_sq_le_range_dispersion {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] {b : α → ℝ} (hb : Measurable b)
    {R : ℝ} (hrange : ∀ x y, |b x - b y| ≤ R) :
    (∫ p : α × α, (b p.1 - b p.2) ^ 2 ∂ν.prod ν) ≤ R * measureDispersion ν b := by
  rw [measureDispersion, ← integral_const_mul]
  have hm : Measurable (fun p : α × α => b p.1 - b p.2) :=
    (hb.comp measurable_fst).sub (hb.comp measurable_snd)
  apply integral_mono (integrable_sq_of_abs_bound (ν.prod ν) hm (fun p => hrange p.1 p.2))
    ((integrable_of_abs_bound (ν.prod ν) hm.abs (fun p => by
      simpa only [abs_abs] using hrange p.1 p.2)).const_mul R)
  intro p
  change (b p.1 - b p.2) ^ 2 ≤ R * |b p.1 - b p.2|
  have h := mul_le_mul_of_nonneg_right (hrange p.1 p.2) (abs_nonneg (b p.1 - b p.2))
  simpa only [← sq, sq_abs] using h

theorem measure_pair_max_mgf_le {α : Type*} [MeasurableSpace α] [Nonempty α]
    (ν : Measure α) [IsProbabilityMeasure ν] {b : α → ℝ} (hb : Measurable b)
    {R θ : ℝ} (hrange : ∀ x y, |b x - b y| ≤ R)
    (hθ : 0 ≤ θ) (hsmall : θ * R ≤ 1 / 4) :
    (∫ p : α × α, Real.exp (-θ * max (b p.1) (b p.2)) ∂ν.prod ν) ≤
      Real.exp (-θ * (∫ x, b x ∂ν) - θ * measureDispersion ν b / 4) := by
  let μ := ∫ x, b x ∂ν
  let D := measureDispersion ν b
  let Z := fun p : α × α => max (b p.1) (b p.2)
  have hZ : Measurable Z := (hb.comp measurable_fst).max (hb.comp measurable_snd)
  have hD : 0 ≤ D := measureDispersion_nonneg ν b
  have hbound (p : α × α) : |Z p - μ| ≤ R :=
    abs_max_sub_le (abs_sub_integral_le_range ν hb hrange p.1)
      (abs_sub_integral_le_range ν hb hrange p.2)
  have hZc : Integrable (fun p => Z p - μ) (ν.prod ν) :=
    integrable_of_abs_bound (ν.prod ν) (hZ.sub measurable_const) hbound
  have hZi : Integrable Z (ν.prod ν) := by
    have := hZc.add (integrable_const μ)
    convert this using 1
    funext p
    change Z p = Z p - μ + μ
    ring
  have hnorm (p : α × α) : |-θ * (Z p - μ)| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hθ]
    have := mul_le_mul_of_nonneg_left (hbound p) hθ
    linarith
  have hmean : (∫ p, -θ * (Z p - μ) ∂ν.prod ν) = -θ * D / 2 := by
    rw [integral_const_mul, integral_sub hZi (integrable_const μ)]
    simp only [integral_const, probReal_univ, one_smul]
    dsimp [Z, μ, D]
    rw [integral_pair_max ν hb hrange]
    ring
  have hsq : (∫ p, (-θ * (Z p - μ)) ^ 2 ∂ν.prod ν) ≤ θ ^ 2 * (R * D) := by
    have hidentity (p : α × α) : (-θ * (Z p - μ)) ^ 2 = θ ^ 2 * (Z p - μ) ^ 2 := by ring
    simp_rw [hidentity]
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg θ)
    exact le_trans (integral_max_centered_sq_le ν hb hrange)
      (integral_pair_sq_le_range_dispersion ν hb hrange)
  have hgain : (∫ p, Real.exp (-θ * (Z p - μ)) ∂ν.prod ν) ≤ Real.exp (-θ * D / 4) := by
    have hquad := integral_exp_le_quadratic (ν.prod ν)
      ((hZ.sub measurable_const).const_mul (-θ)) hnorm
    rw [hmean] at hquad
    have habsorb : θ ^ 2 * (R * D) ≤ θ * D / 4 := by
      have := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hθ hD)
      nlinarith
    have hexp := Real.add_one_le_exp (-θ * D / 4)
    linarith
  have hexp (p : α × α) : Real.exp (-θ * Z p) =
      Real.exp (-θ * μ) * Real.exp (-θ * (Z p - μ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change (∫ p, Real.exp (-θ * Z p) ∂ν.prod ν) ≤ _
  simp_rw [hexp]
  rw [integral_const_mul]
  calc
    _ ≤ Real.exp (-θ * μ) * Real.exp (-θ * D / 4) :=
      mul_le_mul_of_nonneg_left hgain (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      dsimp [μ, D]
      congr 1
      ring

theorem integrable_exp_of_abs_bound {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] {x : α → ℝ} (hx : Measurable x)
    {C : ℝ} (hC : ∀ a, |x a| ≤ C) : Integrable (fun a => Real.exp (x a)) ν := by
  apply integrable_of_abs_bound ν hx.exp (C := Real.exp C)
  intro a
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hC a))

/-- Independent product measures tensorize the pair bound. -/
theorem measure_paired_max_weight {α : Type*} [MeasurableSpace α] [Nonempty α]
    (ν : Measure α) [IsProbabilityMeasure ν] {b : α → ℝ} (hb : Measurable b)
    {t : ℕ} (ht : 0 < t) {R a : ℝ} (hrange : ∀ x y, |b x - b y| ≤ R)
    (ha : 0 ≤ a) (hsmall : (a / (t : ℝ)) * R ≤ 1 / 4)
    (W : (Fin t → α × α) → ℝ)
    (hW : ∀ samples i, max (b (samples i).1) (b (samples i).2) ≤ W samples) :
    (∫ samples, Real.exp (-a * W samples) ∂Measure.pi (fun _ => ν.prod ν)) ≤
      Real.exp (-a * (∫ x, b x ∂ν) - a * measureDispersion ν b / 4) := by
  let θ := a / (t : ℝ)
  let μ := ∫ x, b x ∂ν
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hθ : 0 ≤ θ := div_nonneg ha ht'.le
  have hθt : θ * t = a := by dsimp [θ]; field_simp
  have hbound (p : α × α) : |max (b p.1) (b p.2) - μ| ≤ R :=
    abs_max_sub_le (abs_sub_integral_le_range ν hb hrange p.1)
      (abs_sub_integral_le_range ν hb hrange p.2)
  have hipair : Integrable (fun p : α × α => Real.exp (-θ * max (b p.1) (b p.2)))
      (ν.prod ν) := by
    have hm : Measurable (fun p : α × α => -θ * max (b p.1) (b p.2)) := by fun_prop
    apply integrable_exp_of_abs_bound (ν.prod ν) hm (C := |θ| * (R + |μ|))
    intro p
    rw [abs_mul, abs_neg]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg θ)
    calc
      _ = |(max (b p.1) (b p.2) - μ) + μ| := by congr 1; ring
      _ ≤ |max (b p.1) (b p.2) - μ| + |μ| := abs_add_le _ _
      _ ≤ _ := by gcongr; exact hbound p
  have hiprod := Integrable.fintype_prod (fun _i : Fin t => hipair)
  have hpoint (samples : Fin t → α × α) : Real.exp (-a * W samples) ≤
      ∏ i, Real.exp (-θ * max (b (samples i).1) (b (samples i).2)) := by
    have hsum : (∑ i, max (b (samples i).1) (b (samples i).2)) ≤ (t : ℝ) * W samples := by
      calc
        _ ≤ ∑ _i : Fin t, W samples := Finset.sum_le_sum fun i _ => hW samples i
        _ = _ := by simp
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    rw [← Finset.mul_sum]
    have hmul := mul_le_mul_of_nonneg_left hsum hθ
    rw [← mul_assoc, hθt] at hmul
    nlinarith
  calc
    _ ≤ ∫ samples : Fin t → α × α,
        ∏ i, Real.exp (-θ * max (b (samples i).1) (b (samples i).2))
          ∂Measure.pi (fun _ => ν.prod ν) :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => Real.exp_nonneg _) hiprod
        (ae_of_all _ hpoint)
    _ = (∫ p : α × α, Real.exp (-θ * max (b p.1) (b p.2)) ∂ν.prod ν) ^ t := by
      simpa only [Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin t) (μ := ν.prod ν)
          (fun p : α × α => Real.exp (-θ * max (b p.1) (b p.2))))
    _ ≤ (Real.exp (-θ * (∫ x, b x ∂ν) - θ * measureDispersion ν b / 4)) ^ t :=
      pow_le_pow_left₀ (integral_nonneg fun _ => Real.exp_nonneg _)
        (measure_pair_max_mgf_le ν hb hrange hθ hsmall) t
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [θ]
      field_simp

/-- A measurable regrouping of the samples into two lists, paired pointwise,
and an unused remainder. The index bijection records every coordinate. -/
def measurePairSamplesEquiv {α : Type*} [MeasurableSpace α] {d t r : ℕ}
    (index : ((Fin t ⊕ Fin t) ⊕ Fin r) ≃ Fin d) :
    (Fin d → α) ≃ᵐ (Fin t → α × α) × (Fin r → α) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin d => α) index).symm |>.trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin t ⊕ Fin t) ⊕ Fin r => α)).trans
      ((MeasurableEquiv.prodCongr
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin t ⊕ Fin t => α))
        (MeasurableEquiv.refl (Fin r → α))).trans
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.arrowProdEquivProdArrow α α (Fin t)).symm
          (MeasurableEquiv.refl (Fin r → α)))))

theorem measurePairSamples_measurePreserving {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] {d t r : ℕ}
    (index : ((Fin t ⊕ Fin t) ⊕ Fin r) ≃ Fin d) :
    MeasurePreserving (measurePairSamplesEquiv (α := α) index)
      (Measure.pi (fun _ : Fin d => ν))
      ((Measure.pi (fun _ : Fin t => ν.prod ν)).prod
        (Measure.pi (fun _ : Fin r => ν))) := by
  exact (((measurePreserving_arrowProdEquivProdArrow α α (Fin t)
    (fun _ => ν) (fun _ => ν)).symm.prod (MeasurePreserving.id _)).comp
      (((measurePreserving_sumPiEquivProdPi (fun _ : Fin t ⊕ Fin t => ν)).prod
        (MeasurePreserving.id _)).comp
        ((measurePreserving_sumPiEquivProdPi
          (fun _ : (Fin t ⊕ Fin t) ⊕ Fin r => ν)).comp
          (measurePreserving_piCongrLeft (fun _ : Fin d => ν) index).symm)))

theorem measurePairSamples_first {α : Type*} [MeasurableSpace α] {d t r : ℕ}
    (index : ((Fin t ⊕ Fin t) ⊕ Fin r) ≃ Fin d) (samples : Fin d → α) (i : Fin t) :
    ((measurePairSamplesEquiv index samples).1 i).1 = samples (index (.inl (.inl i))) := rfl

theorem measurePairSamples_second {α : Type*} [MeasurableSpace α] {d t r : ℕ}
    (index : ((Fin t ⊕ Fin t) ⊕ Fin r) ≃ Fin d) (samples : Fin d → α) (i : Fin t) :
    ((measurePairSamplesEquiv index samples).1 i).2 = samples (index (.inl (.inr i))) := rfl

theorem measurable_sampleMaximum {α : Type*} [MeasurableSpace α]
    {b : α → ℝ} (hb : Measurable b) {d : ℕ} (hd : 0 < d) :
    Measurable (sampleMaximum b hd) := by
  unfold sampleMaximum
  have H := Finset.measurable_sup' (s := Finset.univ) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    (f := fun i (samples : Fin d → α) => b (samples i))
    (fun i _ => hb.comp (measurable_pi_apply i))
  convert H using 1
  funext samples
  exact (Finset.sup'_apply (C := fun _ : Fin d → α => ℝ)
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun i (samples : Fin d → α) => b (samples i)) samples).symm

theorem abs_sampleMaximum_sub_le {α : Type*} (b : α → ℝ) {d : ℕ} (hd : 0 < d)
    {c R : ℝ} (hbound : ∀ a, |b a - c| ≤ R) (samples : Fin d → α) :
    |sampleMaximum b hd samples - c| ≤ R := by
  apply abs_le.mpr
  constructor
  · have hl := (abs_le.mp (hbound (samples ⟨0, hd⟩))).1
    have hm := le_sampleMaximum b hd samples ⟨0, hd⟩
    linarith
  · have hu : sampleMaximum b hd samples ≤ c + R := by
      unfold sampleMaximum
      apply Finset.sup'_le
      intro i _
      have := (abs_le.mp (hbound (samples i))).2
      linarith
    linarith

/-- The general measurable version, under a pointwise support-diameter bound.
Odd sample sizes are included by integrating out the unused remainder. -/
theorem max_weight_measure {α : Type*} [MeasurableSpace α] [Nonempty α]
    (ν : Measure α) [IsProbabilityMeasure ν] {b : α → ℝ} (hb : Measurable b)
    {d : ℕ} (hd : 2 ≤ d) (hrange : ∀ x y, |b x - b y| ≤ (d : ℝ) / 12) :
    (∫ samples : Fin d → α, Real.exp (-Real.log 2 * sampleMaximum b (by omega) samples)
      ∂Measure.pi (fun _ => ν)) ≤
      Real.exp (-Real.log 2 * (∫ x, b x ∂ν) - (Real.log 2 / 4) * measureDispersion ν b) := by
  classical
  let t := d / 2
  let r := d % 2
  have ht : 0 < t := by dsimp [t]; omega
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hsplit : t + t + r = d := by dsimp [t, r]; omega
  let index : ((Fin t ⊕ Fin t) ⊕ Fin r) ≃ Fin d :=
    ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin r))).trans finSumFinEquiv).trans
      (finCongr hsplit)
  let e := measurePairSamplesEquiv (α := α) index
  let F := fun p : (Fin t → α × α) × (Fin r → α) =>
    Real.exp (-Real.log 2 * sampleMaximum b (by omega) (e.symm p))
  have hlog : (0 : ℝ) ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogle : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hd3 : (d : ℝ) ≤ 3 * t := by exact_mod_cast (show d ≤ 3 * t by dsimp [t]; omega)
  have hsmall : (Real.log 2 / (t : ℝ)) * ((d : ℝ) / 12) ≤ 1 / 4 := by
    have hratio : ((d : ℝ) / 12) / t ≤ 1 / 4 := by
      apply (div_le_iff₀ ht').mpr
      linarith
    calc
      _ = Real.log 2 * (((d : ℝ) / 12) / t) := by ring
      _ ≤ 1 * (1 / 4) := mul_le_mul hlogle hratio
        (div_nonneg (by positivity) ht'.le) (by norm_num)
      _ = _ := by norm_num
  have hmu := abs_sub_integral_le_range ν hb hrange
  have hmaxbound := abs_sampleMaximum_sub_le b (by omega : 0 < d) hmu
  have hiF : Integrable F
      ((Measure.pi (fun _ : Fin t => ν.prod ν)).prod (Measure.pi (fun _ : Fin r => ν))) := by
    apply integrable_exp_of_abs_bound _
      (((measurable_sampleMaximum hb (by omega)).comp e.symm.measurable).const_mul (-Real.log 2))
      (C := |Real.log 2| * ((d : ℝ) / 12 + |∫ x, b x ∂ν|))
    intro p
    change |-Real.log 2 * sampleMaximum b _ (e.symm p)| ≤ _
    rw [abs_mul, abs_neg]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      _ = |(sampleMaximum b _ (e.symm p) - ∫ x, b x ∂ν) + ∫ x, b x ∂ν| := by congr 1; ring
      _ ≤ |sampleMaximum b _ (e.symm p) - ∫ x, b x ∂ν| + |∫ x, b x ∂ν| := abs_add_le _ _
      _ ≤ _ := by gcongr; exact hmaxbound (e.symm p)
  have hinner (rest : Fin r → α) :
      (∫ pairs, F (pairs, rest) ∂Measure.pi (fun _ : Fin t => ν.prod ν)) ≤
      Real.exp (-Real.log 2 * (∫ x, b x ∂ν) - (Real.log 2 / 4) * measureDispersion ν b) := by
    have heq : (Real.log 2 / 4) * measureDispersion ν b =
        Real.log 2 * measureDispersion ν b / 4 := by ring
    rw [heq]
    dsimp only [F]
    apply measure_paired_max_weight ν hb ht hrange hlog hsmall
      (fun pairs => sampleMaximum b (by omega) (e.symm (pairs, rest)))
    intro pairs i
    apply max_le
    · have h := measurePairSamples_first index (e.symm (pairs, rest)) i
      rw [show measurePairSamplesEquiv index (e.symm (pairs, rest)) = (pairs, rest) from
        e.apply_symm_apply _] at h
      rw [h]
      exact le_sampleMaximum b (by omega) _ _
    · have h := measurePairSamples_second index (e.symm (pairs, rest)) i
      rw [show measurePairSamplesEquiv index (e.symm (pairs, rest)) = (pairs, rest) from
        e.apply_symm_apply _] at h
      rw [h]
      exact le_sampleMaximum b (by omega) _ _
  have he := measurePairSamples_measurePreserving ν index
  have hreindex := he.symm.integral_comp' (fun samples : Fin d → α =>
    Real.exp (-Real.log 2 * sampleMaximum b (by omega) samples))
  change _ ≤ _
  rw [← hreindex]
  change (∫ p, F p ∂_) ≤ _
  rw [integral_prod_symm F hiF]
  calc
    _ ≤ ∫ _rest : Fin r → α,
        Real.exp (-Real.log 2 * (∫ x, b x ∂ν) - (Real.log 2 / 4) * measureDispersion ν b)
          ∂Measure.pi (fun _ => ν) :=
      integral_mono hiF.integral_prod_right (integrable_const _) hinner
    _ = _ := by simp

/-- The support-diameter version for every real probability distribution.
Passing to the conull support is proved measure preserving, so values on
null sets cannot affect either the maximum law or the dispersion. -/
theorem max_weight_real_law (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {d : ℕ} (hd : 2 ≤ d) (hbounded : Bornology.IsBounded ν.support)
    (hdiam : Metric.diam ν.support ≤ (d : ℝ) / 12) :
    (∫ samples : Fin d → ℝ,
      Real.exp (-Real.log 2 * sampleMaximum id (by omega) samples)
        ∂Measure.pi (fun _ => ν)) ≤
      Real.exp (-Real.log 2 * (∫ x, x ∂ν) - (Real.log 2 / 4) * measureDispersion ν id) := by
  have hs : MeasurableSet ν.support := Measure.isClosed_support.measurableSet
  have hre : ν.restrict ν.support = ν :=
    Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  let νs : Measure ν.support := Measure.comap Subtype.val ν
  have hmap : νs.map (Subtype.val : ν.support → ℝ) = ν := by
    rw [map_comap_subtype_coe hs, hre]
  haveI : IsProbabilityMeasure νs := by
    constructor
    have hfull : ν ν.support = 1 := by
      have h := congrArg (fun μ : Measure ℝ => μ Set.univ) hre
      simpa using h
    rw [comap_subtype_coe_apply hs ν Set.univ]
    simpa only [Set.image_univ, Subtype.range_coe] using hfull
  haveI : Nonempty ν.support := by
    obtain ⟨x, hx⟩ := ν.nonempty_inter_support_of_pos (by simp : 0 < ν Set.univ)
    exact ⟨⟨x, hx.2⟩⟩
  have hf : MeasurePreserving (Subtype.val : ν.support → ℝ) νs ν :=
    ⟨measurable_subtype_coe, hmap⟩
  have hrange (x y : ν.support) : |(x : ℝ) - y| ≤ (d : ℝ) / 12 := by
    exact le_trans (by simpa only [Real.dist_eq] using
      Metric.dist_le_diam_of_mem hbounded x.property y.property) hdiam
  have h := max_weight_measure νs measurable_subtype_coe hd hrange
  have hmean : (∫ x : ν.support, (x : ℝ) ∂νs) = ∫ x, x ∂ν :=
    hf.integral_comp (MeasurableEmbedding.subtype_coe hs) id
  have hprod := hf.prod hf
  have hdisp : measureDispersion νs (Subtype.val : ν.support → ℝ) = measureDispersion ν id := by
    unfold measureDispersion
    rw [← hprod.map_eq, integral_map hprod.measurable.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun p : ℝ × ℝ => |id p.1 - id p.2|) _)]
    rfl
  have hpi := measurePreserving_pi (fun _ : Fin d => νs) (fun _ : Fin d => ν) (fun _ => hf)
  have hmaximum : (∫ samples : Fin d → ν.support,
      Real.exp (-Real.log 2 * sampleMaximum Subtype.val (by omega) samples)
        ∂Measure.pi (fun _ => νs)) =
      ∫ samples : Fin d → ℝ,
        Real.exp (-Real.log 2 * sampleMaximum id (by omega) samples)
          ∂Measure.pi (fun _ => ν) := by
    rw [← hpi.map_eq, integral_map hpi.measurable.aemeasurable
      (((measurable_sampleMaximum measurable_id (by omega)).const_mul (-Real.log 2)).exp.aestronglyMeasurable)]
    rfl
  rw [hmaximum, hmean, hdisp] at h
  exact h

/-- Convert the exponential used in the proof to the paper's power of two. -/
theorem exp_neg_log_two_mul (x : ℝ) : Real.exp (-Real.log 2 * x) = (2 : ℝ) ^ (-x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Exact full scope of manuscript Lemma `lem:max-weight`. The law of `B`
is an arbitrary real probability measure; product measures supply its iid
copies and the independent copy in `E |B-B'|`. Bounded support records that
the support diameter is finite, avoiding mathlib's totalized real diameter
of an unbounded set. -/
def MaxWeightLemma : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ∀ (d : ℕ) (hd : 2 ≤ d),
      Bornology.IsBounded ν.support → Metric.diam ν.support ≤ ε₀ * d →
        (∫ samples : Fin d → ℝ,
          (2 : ℝ) ^ (-sampleMaximum id (by omega) samples)
            ∂Measure.pi (fun _ => ν)) ≤
          (2 : ℝ) ^ (-(∫ x, x ∂ν)) * Real.exp (-c * measureDispersion ν id)

theorem max_weight_lemma : MaxWeightLemma := by
  refine ⟨1 / 12, by norm_num, Real.log 2 / 4,
    div_pos (Real.log_pos (by norm_num)) (by norm_num), ?_⟩
  intro ν hν d hd hbounded hdiam
  haveI := hν
  simp_rw [← exp_neg_log_two_mul]
  rw [← Real.exp_add]
  have hdiam' : Metric.diam ν.support ≤ (d : ℝ) / 12 := by nlinarith
  simpa only [sub_eq_add_neg, neg_mul] using max_weight_real_law ν hd hbounded hdiam'

/-- Transfer the bound to iid real random variables on any probability
space. Independence and equality of the individual laws prove the joint
product law; that joint law is not an additional hypothesis. -/
theorem max_weight_iid {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {d : ℕ} (hd : 2 ≤ d) (X : Fin d → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ) (hind : ProbabilityTheory.iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = ν) (hbounded : Bornology.IsBounded ν.support)
    (hdiam : Metric.diam ν.support ≤ (d : ℝ) / 12) :
    (∫ ω, Real.exp (-Real.log 2 * sampleMaximum id (by omega) (fun i => X i ω)) ∂μ) ≤
      Real.exp (-Real.log 2 * (∫ ω, X ⟨0, by omega⟩ ω ∂μ) -
        (Real.log 2 / 4) * measureDispersion ν id) := by
  have hjoint : AEMeasurable (fun ω i => X i ω) μ := by fun_prop
  have hmap : μ.map (fun ω i => X i ω) = Measure.pi (fun _ : Fin d => ν) := by
    rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hX).mp hind]
    congr 1
    funext i
    exact hlaw i
  have hmean : (∫ ω, X ⟨0, by omega⟩ ω ∂μ) = ∫ x, x ∂ν := by
    rw [← hlaw ⟨0, by omega⟩]
    exact (integral_map (hX ⟨0, by omega⟩)
      (show AEStronglyMeasurable (fun x : ℝ => x) _ from measurable_id.aestronglyMeasurable)).symm
  have hm : AEStronglyMeasurable (fun samples : Fin d → ℝ =>
      Real.exp (-Real.log 2 * sampleMaximum id (by omega) samples))
        (μ.map (fun ω i => X i ω)) :=
    (((measurable_sampleMaximum measurable_id (by omega)).const_mul (-Real.log 2)).exp).aestronglyMeasurable
  have hsame := integral_map hjoint hm
  rw [hmap] at hsame
  rw [← hsame, hmean]
  exact max_weight_real_law ν hd hbounded hdiam

end CircularLaw
