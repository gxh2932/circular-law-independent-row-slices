import CircularLaw.GaussianFreshRowSmallBall
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Resampling the actual omitted row under the full matrix law

Finite row resampling preserves the full row-slice law. Since the enlarged
retained span depends only on retained rows, an omitted row can be replaced
by an independent fresh slice without changing its Gaussian normal. Fubini
then applies the averaged supremum bound to the actual shifted omitted-row
small-ball probability.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped BigOperators Topology

namespace CircularLaw

theorem finiteMean_resample_coordinate {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] (i : ι) (g : (ι → α) → ℝ) :
    finiteMean g = finiteMean (fun rows => finiteMean (fun s => g (Function.update rows i s))) := by
  let e := Equiv.funSplitAt i α
  have hUpdate (p : α × ({j : ι // j ≠ i} → α)) (s : α) :
      Function.update (e.symm p) i s = e.symm (s, p.2) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  calc
    finiteMean g = finiteMean (fun p => g (e.symm p)) := (finiteMean_reindex e.symm g).symm
    _ = finiteMean (fun rest => finiteMean (fun s => g (e.symm (s, rest)))) := finiteMean_prod_fubini _
    _ = finiteMean (fun p : α × ({j : ι // j ≠ i} → α) =>
        finiteMean (fun s => g (e.symm (s, p.2)))) := (finiteMean_snd _).symm
    _ = finiteMean (fun p => finiteMean (fun s => g (Function.update (e.symm p) i s))) := by
      simp only [hUpdate]
    _ = _ := finiteMean_reindex e.symm
      (fun rows => finiteMean (fun s => g (Function.update rows i s)))

theorem finiteMean_integral_fubini {X α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (f : α → X → ℝ) (hInt : ∀ a, Integrable (f a) μ) :
    finiteMean (fun a => ∫ x, f a x ∂μ) = ∫ x, finiteMean (fun a => f a x) ∂μ := by
  simp only [finiteMean]
  rw [integral_div, integral_finset_sum _ (fun a _ => hInt a)]

theorem enlargedRetainedRowSpan_update_omitted {n d : ℕ} (I : Finset (Fin n))
    (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) (hi : i ∉ I) (s : RowSlice n d) :
    enlargedRetainedRowSpan I ζ (Function.update rows i s) = enlargedRetainedRowSpan I ζ rows := by
  apply enlargedRetainedRowSpan_depends_on_retained_rows
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hi hj
  exact Function.update_of_ne hji s rows

def enlargedRetainedGaussianRowForm {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin n) (z : Fin n → ℂ) : ℂ :=
  rowLinearForm (rows i) (fun j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j) -
    ζ * projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z i

theorem enlargedRetainedGaussian_fresh_row_form_continuous {n d : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) (s : RowSlice n d) :
    Continuous (fun z => rowLinearForm s
      (fun j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j) -
        ζ * projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z i) := by
  have hCoord (j : Fin n) : Continuous (fun z =>
      projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp (projectedComplexGaussian_continuous _)
  exact (continuous_finset_sum _ (fun j _ => continuous_const.mul (hCoord j))).sub
    (continuous_const.mul (hCoord i))

theorem enlargedRetainedGaussianRowForm_continuous {n d : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) :
    Continuous (enlargedRetainedGaussianRowForm I ζ rows i) :=
  enlargedRetainedGaussian_fresh_row_form_continuous I ζ rows i (rows i)

theorem finiteGaussian_product_event_real {X α : Type*} [MeasurableSpace X] [Fintype α]
    [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure X) [IsProbabilityMeasure μ] (A : Set (α × X)) (hA : MeasurableSet A) :
    ((finiteUniformMeasure α).prod μ).real A = finiteMean (fun a => μ.real {x | (a, x) ∈ A}) := by
  let f := A.indicator (fun _ : α × X => (1 : ℝ))
  have hInt : Integrable f ((finiteUniformMeasure α).prod μ) :=
    (integrable_const _).indicator hA
  have hSlices (a : α) : MeasurableSet {x | (a, x) ∈ A} :=
    hA.preimage (measurable_const.prodMk measurable_id)
  calc
    _ = ∫ p, f p ∂(finiteUniformMeasure α).prod μ := by
      simpa only [f, smul_eq_mul, mul_one] using
        (integral_indicator_const (μ := (finiteUniformMeasure α).prod μ) (1 : ℝ) hA).symm
    _ = ∫ a, ∫ x, f (a, x) ∂μ ∂finiteUniformMeasure α := integral_prod _ hInt
    _ = finiteMean (fun a => μ.real {x | (a, x) ∈ A}) := by
      rw [integral_finiteUniformMeasure]
      congr 1
      funext a
      simpa only [f, Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
        integral_indicator_const (μ := μ) (1 : ℝ) (hSlices a)

theorem actual_omitted_row_gaussian_probability_le_averaged_concentration {n d : ℕ}
    (hdn : d ≤ n) (I : Finset (Fin n)) (ζ : ℂ) (i : Fin n) (hi : i ∉ I) (r : ℝ) :
    ((rowSliceMatrixLaw n d).prod (standardComplexGaussianVectorLaw n)).real
      {p | ‖enlargedRetainedGaussianRowForm I ζ p.1 i p.2‖ ≤ r} ≤
        finiteMean (fun rows : RowSliceMatrix n d => ∫ z,
          rowSliceDiskConcentration (d := d)
            (fun j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j) r
          ∂standardComplexGaussianVectorLaw n) := by
  haveI := rowSlice_nonempty hdn
  let μ := standardComplexGaussianVectorLaw n
  let H := fun (rows : RowSliceMatrix n d) (s : RowSlice n d) (z : Fin n → ℂ) =>
    if ‖rowLinearForm s (fun j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j) -
        ζ * projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z i‖ ≤ r then (1 : ℝ) else 0
  have hHMeas (rows : RowSliceMatrix n d) (s : RowSlice n d) : Measurable (H rows s) :=
    measurable_const.ite ((isClosed_le
      (enlargedRetainedGaussian_fresh_row_form_continuous I ζ rows i s).norm continuous_const).measurableSet)
      measurable_const
  have hHInt (rows : RowSliceMatrix n d) (s : RowSlice n d) : Integrable (H rows s) μ :=
    Integrable.of_bound (hHMeas rows s).aestronglyMeasurable 1 (ae_of_all _ (fun z => by
      dsimp [H]
      split_ifs <;> norm_num))
  have hEventMeas : MeasurableSet {p : RowSliceMatrix n d × (Fin n → ℂ) |
      ‖enlargedRetainedGaussianRowForm I ζ p.1 i p.2‖ ≤ r} := by
    have hForm : Measurable (fun p : RowSliceMatrix n d × (Fin n → ℂ) =>
        enlargedRetainedGaussianRowForm I ζ p.1 i p.2) :=
      measurable_from_prod_countable_right (fun rows =>
        (enlargedRetainedGaussianRowForm_continuous I ζ rows i).measurable)
    exact measurableSet_le hForm.norm measurable_const
  have hProb (rows : RowSliceMatrix n d) : μ.real {z | ‖enlargedRetainedGaussianRowForm I ζ rows i z‖ ≤ r} =
      ∫ z, H rows (rows i) z ∂μ := by
    simpa only [H, enlargedRetainedGaussianRowForm, Set.indicator_apply, Set.mem_setOf_eq,
      smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ)
        ((isClosed_le (enlargedRetainedGaussianRowForm_continuous I ζ rows i).norm continuous_const).measurableSet)).symm
  rw [rowSliceMatrixLaw, finiteGaussian_product_event_real _ _ hEventMeas]
  change finiteMean (fun rows : RowSliceMatrix n d => μ.real
    {z | ‖enlargedRetainedGaussianRowForm I ζ rows i z‖ ≤ r}) ≤ _
  simp only [hProb]
  rw [finiteMean_resample_coordinate i]
  apply finiteMean_mono
  intro rows
  have hReplace (s : RowSlice n d) :
      H (Function.update rows i s) (Function.update rows i s i) = H rows s := by
    funext z
    simp only [H, Function.update_self, enlargedRetainedRowSpan_update_omitted I ζ rows i hi s]
  simp only [hReplace]
  rw [finiteMean_integral_fubini μ (H rows) (hHInt rows)]
  have hConcMeas := rowSliceDiskConcentration_measurable hdn
    (fun z j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j)
    (fun j => (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
      (projectedComplexGaussian_continuous _)) r
  have hConcInt : Integrable (fun z => rowSliceDiskConcentration (d := d)
      (fun j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j) r) μ :=
    Integrable.of_bound hConcMeas.aestronglyMeasurable 1 (ae_of_all _ (fun z => by
      simp only [rowSliceDiskConcentration, Real.norm_eq_abs]
      rw [abs_of_nonneg (finiteDiskConcentration_nonneg _ _)]
      exact finiteDiskConcentration_le_one _ _))
  have hFreshInt : Integrable (fun z => finiteMean (fun s => H rows s z)) μ := by
    unfold finiteMean
    exact (integrable_finset_sum _ (fun s _ => hHInt rows s)).div_const _
  apply integral_mono hFreshInt hConcInt
  intro z
  simp only [H, finiteMean_indicator, rowLinearForm_eq_support_sum]
  exact uniformProbability_le_finiteDiskConcentration _ r
    (ζ * projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z i)

theorem actual_omitted_row_gaussian_small_ball_uniform :
    ∃ Cstar R : ℝ, 0 < Cstar ∧ 0 < R ∧
      ∀ C : ℝ, Cstar ≤ C → ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
          ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
            ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d → ∀ i : Fin n, i ∉ I →
              ((rowSliceMatrixLaw n d).prod (standardComplexGaussianVectorLaw n)).real
                {p | ‖enlargedRetainedGaussianRowForm I ζ p.1 i p.2‖ ≤
                  Real.exp (-R * Real.rpow (d : ℝ) (1 / 96))} ≤ R / (d : ℝ) ^ 3 + R / n := by
  obtain ⟨Cstar, R, hCstar, hR, hMean⟩ := averaged_random_normal_small_ball_theorem
  refine ⟨Cstar, R, hCstar, hR, ?_⟩
  intro C hC σ Z₀ hσ0 hσ1
  obtain ⟨NA, hNA⟩ := hMean C hC σ Z₀ hσ0 hσ1
  obtain ⟨NP, hNP⟩ := eventually_atTop.mp
    (eventually_fresh_row_gaussian_parameters (hCstar.trans_le hC) hσ1.le)
  refine ⟨max NA NP, ?_⟩
  intro n hn d hBand L hL I hI ζ hShift i hi
  have hnA : NA ≤ n := (le_max_left _ _).trans hn
  have hnP : NP ≤ n := (le_max_right _ _).trans hn
  have hHalf := (hNP n hnP d hBand).2.2.1
  exact (actual_omitted_row_gaussian_probability_le_averaged_concentration (by omega : d ≤ n)
    I ζ i hi _).trans (hNA n hnA d hBand L hL I hI ζ hShift)

end CircularLaw
