import CircularLaw.MeasureMaxWeight

/-!
# Tensorization from quadratic small-ball bounds

This develops the source form of LLTTY19, Lemma 2.7: the squared-radius
threshold has coefficient one, and an absolute constant appears in the
probability bound. The manuscript's use of one identical constant in both
places requires statement review before this result can be counted there.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CircularLaw

def tensorLayer {Ω : Type*} (u : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  {ω | u ω < (n : ℝ) + 1}.indicator (fun _ => (1 / 2 : ℝ) ^ n)

theorem tensorLayer_nonneg {Ω : Type*} (u : Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ tensorLayer u n ω := by
  classical
  by_cases h : u ω < (n : ℝ) + 1 <;> simp [tensorLayer, h]

theorem tensorLayer_le_geometric {Ω : Type*} (u : Ω → ℝ) (n : ℕ) (ω : Ω) :
    tensorLayer u n ω ≤ (1 / 2 : ℝ) ^ n := by
  classical
  by_cases h : u ω < (n : ℝ) + 1 <;> simp [tensorLayer, h]

theorem tensorLayer_summable {Ω : Type*} (u : Ω → ℝ) (ω : Ω) :
    Summable (fun n => tensorLayer u n ω) :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).of_nonneg_of_le (fun n => tensorLayer_nonneg u n ω)
      (fun n => tensorLayer_le_geometric u n ω)

theorem exp_neg_le_tensorLayers {Ω : Type*} (u : Ω → ℝ) (ω : Ω)
    (hu : 0 ≤ u ω) : Real.exp (-u ω) ≤ ∑' n, tensorLayer u n ω := by
  have hr : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    Real.exp (-u ω) ≤ Real.exp (-(⌊u ω⌋₊ : ℝ)) :=
      Real.exp_le_exp.mpr (neg_le_neg (Nat.floor_le hu))
    _ = Real.exp (-1) ^ ⌊u ω⌋₊ := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ (1 / 2 : ℝ) ^ ⌊u ω⌋₊ := pow_le_pow_left₀ (Real.exp_nonneg _) hr _
    _ = tensorLayer u ⌊u ω⌋₊ ω := by
      simp [tensorLayer, Nat.lt_floor_add_one]
    _ ≤ ∑' n, tensorLayer u n ω :=
      (tensorLayer_summable u ω).le_tsum _ (fun n _ => tensorLayer_nonneg u n ω)

theorem tsum_weighted_geometric_two :
    (∑' n : ℕ, ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) = 4 := by
  have hn := (hasSum_coe_mul_geometric_of_norm_lt_one
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).summable
  have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  simp_rw [add_mul, one_mul]
  rw [hn.tsum_add hg, tsum_coe_mul_geometric_of_norm_lt_one (by norm_num),
    tsum_geometric_two]
  norm_num

theorem tensorLayer_measurable {Ω : Type*} [MeasurableSpace Ω]
    {u : Ω → ℝ} (hu : Measurable u) (n : ℕ) : Measurable (tensorLayer u n) :=
  measurable_const.indicator (measurableSet_lt hu measurable_const)

theorem tensorLayer_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {u : Ω → ℝ} (hu : Measurable u) (n : ℕ) :
    Integrable (tensorLayer u n) μ :=
  (integrable_const _).indicator (measurableSet_lt hu measurable_const)

theorem integral_tensorLayer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {u : Ω → ℝ} (hu : Measurable u) (n : ℕ) :
    (∫ ω, tensorLayer u n ω ∂μ) =
      μ.real {ω | u ω < (n : ℝ) + 1} * (1 / 2 : ℝ) ^ n := by
  exact integral_indicator_const _ (measurableSet_lt hu measurable_const)

theorem tensorLayers_measurable {Ω : Type*} [MeasurableSpace Ω]
    {u : Ω → ℝ} (hu : Measurable u) :
    Measurable (fun ω => ∑' n, tensorLayer u n ω) := by
  apply measurable_of_tendsto_metrizable (f := fun N ω =>
    ∑ n ∈ Finset.range N, tensorLayer u n ω)
  · intro N
    exact Finset.measurable_sum _ (fun n _ => tensorLayer_measurable hu n)
  · exact tendsto_pi_nhds.mpr (fun ω => (tensorLayer_summable u ω).hasSum.tendsto_sum_nat)

theorem tensorLayers_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {u : Ω → ℝ} (hu : Measurable u) :
    Integrable (fun ω => ∑' n, tensorLayer u n ω) μ := by
  apply integrable_of_abs_bound μ (tensorLayers_measurable hu) (C := 2)
  intro ω
  rw [abs_of_nonneg (tsum_nonneg (fun n => tensorLayer_nonneg u n ω))]
  calc
    _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n := (tensorLayer_summable u ω).tsum_le_tsum
      (fun n => tensorLayer_le_geometric u n ω)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    _ = 2 := tsum_geometric_two

/-- A quadratic small-ball estimate gives a uniform Laplace bound.
The proof uses a summable geometric cover of the exponential, so every
exchange of a series and an integral includes an integrability proof. -/
theorem integral_exp_neg_le_of_sublevel_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {u : Ω → ℝ} (hu : Measurable u)
    (hu0 : ∀ ω, 0 ≤ u ω) {p : ℝ}
    (hsmall : ∀ n : ℕ, μ.real {ω | u ω < (n : ℝ) + 1} ≤ p * ((n : ℝ) + 1)) :
    (∫ ω, Real.exp (-u ω) ∂μ) ≤ 4 * p := by
  have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hnorm (n : ℕ) : (∫ ω, ‖tensorLayer u n ω‖ ∂μ) =
      ∫ ω, tensorLayer u n ω ∂μ := by
    congr 1
    funext ω
    exact Real.norm_of_nonneg (tensorLayer_nonneg u n ω)
  have hisum : Summable (fun n => ∫ ω, ‖tensorLayer u n ω‖ ∂μ) := by
    apply (hg.mul_left (μ.real Set.univ)).of_nonneg_of_le
      (fun n => integral_nonneg (fun ω => norm_nonneg _))
    intro n
    rw [hnorm, integral_tensorLayer μ hu]
    exact mul_le_mul_of_nonneg_right
      (measureReal_mono (Set.subset_univ _) (measure_ne_top μ Set.univ)) (by positivity)
  have hweighted : Summable (fun n : ℕ => ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by
    have hn := (hasSum_coe_mul_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).summable
    simpa only [add_mul, one_mul] using hn.add hg
  calc
    (∫ ω, Real.exp (-u ω) ∂μ) ≤ ∫ ω, (∑' n, tensorLayer u n ω) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun ω => (Real.exp_pos _).le)
        (tensorLayers_integrable μ hu) (ae_of_all _ fun ω => exp_neg_le_tensorLayers u ω (hu0 ω))
    _ = ∑' n, ∫ ω, tensorLayer u n ω ∂μ :=
      (integral_tsum_of_summable_integral_norm (tensorLayer_integrable μ hu) hisum).symm
    _ ≤ ∑' n : ℕ, p * (((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by
      apply (hisum.congr fun n => hnorm n).tsum_le_tsum _ (hweighted.mul_left p)
      intro n
      rw [integral_tensorLayer μ hu]
      nlinarith [hsmall n, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
    _ = 4 * p := by rw [tsum_mul_left, tsum_weighted_geometric_two]; ring

/-- The complex Lévy concentration function, with a supremum over all centers. -/
def levyConcentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℂ) (r : ℝ) : ℝ≥0∞ :=
  ⨆ z : ℂ, μ {ω | ‖X ω - z‖ ≤ r}

theorem small_ball_laplace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℂ} (hX : Measurable X)
    {t A τ : ℝ} (ht : 0 < t) (hA : 0 ≤ A) (hτ : 1 ≤ τ)
    (hsmall : ∀ σ : ℝ, 1 ≤ σ → levyConcentration μ X (σ * t) ≤
      ENNReal.ofReal (A * σ ^ 2)) (z : ℂ) :
    (∫ ω, Real.exp (-(‖X ω - z‖ ^ 2 / (τ ^ 2 * t ^ 2))) ∂μ) ≤
      4 * A * τ ^ 2 := by
  have hτ0 : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
  have hden : 0 < τ ^ 2 * t ^ 2 := mul_pos (sq_pos_of_pos hτ0) (sq_pos_of_pos ht)
  apply le_trans (integral_exp_neg_le_of_sublevel_bound μ
    (((hX.sub measurable_const).norm.pow_const 2).div_const _) (fun ω => by positivity)
      (p := A * τ ^ 2) ?_) (by ring_nf; rfl)
  intro n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hσ : 1 ≤ τ * Real.sqrt ((n : ℝ) + 1) := by nlinarith
  have hsq := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1)
  have hsub : {ω | ‖X ω - z‖ ^ 2 / (τ ^ 2 * t ^ 2) < (n : ℝ) + 1} ⊆
      {ω | ‖X ω - z‖ ≤ (τ * Real.sqrt ((n : ℝ) + 1)) * t} := by
    intro ω hω
    have hlt := (div_lt_iff₀ hden).mp hω
    have hnonneg : 0 ≤ (τ * Real.sqrt ((n : ℝ) + 1)) * t := by positivity
    have hsq' : ((τ * Real.sqrt ((n : ℝ) + 1)) * t) ^ 2 =
        ((n : ℝ) + 1) * (τ ^ 2 * t ^ 2) := by
      simp only [mul_pow, hsq]; ring
    change ‖X ω - z‖ ≤ _
    nlinarith [norm_nonneg (X ω - z)]
  calc
    _ ≤ μ.real {ω | ‖X ω - z‖ ≤ (τ * Real.sqrt ((n : ℝ) + 1)) * t} :=
      measureReal_mono hsub
    _ ≤ A * (τ * Real.sqrt ((n : ℝ) + 1)) ^ 2 := by
      apply ENNReal.toReal_le_of_le_ofReal (by positivity)
      exact (le_iSup (fun c : ℂ => μ {ω | ‖X ω - c‖ ≤
        (τ * Real.sqrt ((n : ℝ) + 1)) * t}) z).trans (hsmall _ hσ)
    _ = A * τ ^ 2 * ((n : ℝ) + 1) := by simp only [mul_pow, hsq]; ring

theorem tensorization_positive_radius {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ} (X : Fin K → Ω → ℂ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    {t A τ : ℝ} (ht : 0 < t) (hA : 0 ≤ A) (hτ : 1 ≤ τ)
    (hsmall : ∀ i (σ : ℝ), 1 ≤ σ → levyConcentration μ (X i) (σ * t) ≤
      ENNReal.ofReal (A * σ ^ 2)) (z : Fin K → ℂ) :
    μ.real {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * K} ≤
      (4 * Real.exp 1 * A * τ ^ 2) ^ K := by
  have hτ0 : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
  have hden : 0 < τ ^ 2 * t ^ 2 := mul_pos (sq_pos_of_pos hτ0) (sq_pos_of_pos ht)
  let F : Ω → ℝ := fun ω => Real.exp (-((∑ i, ‖X i ω - z i‖ ^ 2) / (τ ^ 2 * t ^ 2)))
  have hm : Measurable F := by dsimp [F]; fun_prop
  have hFi : Integrable F μ := by
    apply integrable_of_abs_bound μ hm (C := 1)
    intro ω
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    dsimp [F]
    have : 0 ≤ ∑ i, ‖X i ω - z i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact neg_nonpos.mpr (div_nonneg this hden.le)
  have hid : (∫ ω, F ω ∂μ) =
      ∏ i, ∫ ω, Real.exp (-(‖X i ω - z i‖ ^ 2 / (τ ^ 2 * t ^ 2))) ∂μ := by
    dsimp [F]
    simp_rw [Finset.sum_div, ← Finset.sum_neg_distrib, Real.exp_sum]
    exact hind.integral_fun_prod_comp
      (f := fun i w => Real.exp (-(‖w - z i‖ ^ 2 / (τ ^ 2 * t ^ 2))))
      (fun i => (hX i).aemeasurable) (fun i => by fun_prop)
  have hmgf : (∫ ω, F ω ∂μ) ≤ (4 * A * τ ^ 2) ^ K := by
    rw [hid]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod
        (s := Finset.univ) (fun _ _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
        (fun i _ => small_ball_laplace μ (hX i) ht hA hτ (hsmall i) (z i)))
  have hsub : {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * K} ⊆
      {ω | Real.exp (-(K : ℝ)) ≤ F ω} := by
    intro ω hω
    apply Real.exp_le_exp.mpr
    dsimp [F]
    exact neg_le_neg ((div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hω))
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => (Real.exp_pos _).le) hFi (Real.exp (-(K : ℝ)))
  have hbound : Real.exp (-(K : ℝ)) *
      μ.real {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * K} ≤
      (4 * A * τ ^ 2) ^ K := by
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_pos _).le).trans
      (hmark.trans hmgf)
  calc
    _ ≤ (4 * A * τ ^ 2) ^ K / Real.exp (-(K : ℝ)) := by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa only [mul_comm] using hbound
    _ = (4 * Real.exp 1 * A * τ ^ 2) ^ K := by
      rw [Real.exp_neg, div_inv_eq_mul]
      have he : Real.exp (K : ℝ) = Real.exp 1 ^ K := by
        simpa only [mul_one] using Real.exp_nat_mul 1 K
      rw [he, ← mul_pow]
      congr 1; ring

theorem tensorization_zero_radius {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ} (X : Fin K → Ω → ℂ)
    (hind : iIndepFun X μ) {A : ℝ} (hA : 0 ≤ A)
    (hsmall : ∀ i, levyConcentration μ (X i) 0 ≤ ENNReal.ofReal A)
    (z : Fin K → ℂ) :
    μ.real {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ 0} ≤ A ^ K := by
  have heq : {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ 0} =
      ⋂ i ∈ Finset.univ, (X i) ⁻¹' {w | ‖w - z i‖ ≤ 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
      Finset.mem_univ, true_implies]
    constructor
    · intro h i
      have hi : ‖X i ω - z i‖ ^ 2 ≤ ∑ j, ‖X j ω - z j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖X j ω - z j‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [norm_nonneg (X i ω - z i)]
    · intro h
      have hz : ∑ i, ‖X i ω - z i‖ ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hi := h i
        nlinarith [norm_nonneg (X i ω - z i)]
      exact hz.le
  rw [measureReal_def, heq,
    hind.measure_inter_preimage_eq_mul Finset.univ
      (fun i _ => measurableSet_le (by fun_prop) measurable_const),
    ENNReal.toReal_prod]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (Finset.prod_le_prod (s := Finset.univ) (fun _ _ => ENNReal.toReal_nonneg)
      (fun i _ => ENNReal.toReal_le_of_le_ofReal hA
        ((le_iSup (fun c : ℂ => μ {ω | ‖X i ω - c‖ ≤ 0}) (z i)).trans (hsmall i))))

/-- The source version of the tensorization estimate, including all
nonnegative radii, any number of variables, and arbitrary deterministic shifts. -/
theorem tensorization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ} (X : Fin K → Ω → ℂ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    {t A τ : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A) (hτ : 1 ≤ τ)
    (hsmall : ∀ i (σ : ℝ), 1 ≤ σ → levyConcentration μ (X i) (σ * t) ≤
      ENNReal.ofReal (A * σ ^ 2)) (z : Fin K → ℂ) :
    μ.real {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * K} ≤
      (4 * Real.exp 1 * A * τ ^ 2) ^ K := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · have ht' : t = 0 := ht0.symm
    subst t
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
    apply le_trans (tensorization_zero_radius μ X hind hA (fun i => by
      simpa using hsmall i 1 le_rfl) z)
    apply pow_le_pow_left₀ hA
    have he := Real.add_one_le_exp (1 : ℝ)
    nlinarith [sq_nonneg (τ - 1), mul_nonneg hA (by nlinarith : 0 ≤ τ ^ 2 - 1)]
  · exact tensorization_positive_radius μ X hX hind htpos hA hτ hsmall z

/-- The manuscript tensorization target after the approved squared-radius
correction, including arbitrary deterministic shifts. -/
def TensorizationSourceLemma : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (K : ℕ) (X : Fin K → Ω → ℂ),
      (∀ i, Measurable (X i)) → iIndepFun X μ →
      ∀ (t A : ℝ), 0 ≤ t → 0 ≤ A →
        (∀ i (σ : ℝ), 1 ≤ σ → levyConcentration μ (X i) (σ * t) ≤
          ENNReal.ofReal (A * σ ^ 2)) →
        ∀ (τ : ℝ), 1 ≤ τ → ∀ (z : Fin K → ℂ),
          μ.real {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * K} ≤
            (C * A * τ ^ 2) ^ K

theorem tensorization_source_lemma : TensorizationSourceLemma := by
  refine ⟨4 * Real.exp 1, by positivity, ?_⟩
  intro Ω mΩ μ hμ K X hX hind t A ht hA hsmall τ hτ z
  haveI := hμ
  exact tensorization μ X hX hind ht hA hτ hsmall z

end CircularLaw
