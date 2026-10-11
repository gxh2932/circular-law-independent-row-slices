import CircularLaw.FiniteDiskConcentration
import CircularLaw.GaussianFreshRowParameters
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The averaged fresh-row concentration bound

The concentration function is the actual supremum of exact-slice event
probabilities. The Gaussian exceptional event gives its pointwise bound;
integration charges Gaussian failure once, and finite averaging charges
the structural failure once. The manuscript's source codimensions and
radius are retained throughout.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped BigOperators Topology

namespace CircularLaw

theorem finiteDiskConcentration_translate {α : Type*} [Fintype α]
    (y : α → ℂ) (r : ℝ) (c : ℂ) :
    finiteDiskConcentration (fun s => y s + c) r = finiteDiskConcentration y r := by
  apply le_antisymm
  · apply finiteDiskConcentration_le
    intro w
    have hEq : (fun s : α => ‖y s + c - w‖ ≤ r) = (fun s : α => ‖y s - (w - c)‖ ≤ r) := by
      funext s
      rw [show y s + c - w = y s - (w - c) by ring]
    rw [hEq]
    exact uniformProbability_le_finiteDiskConcentration y r (w - c)
  · apply finiteDiskConcentration_le
    intro w
    have hEq : (fun s : α => ‖y s - w‖ ≤ r) = (fun s : α => ‖y s + c - (w + c)‖ ≤ r) := by
      funext s
      rw [show y s + c - (w + c) = y s - w by ring]
    rw [hEq]
    exact uniformProbability_le_finiteDiskConcentration _ r (w + c)

theorem rowSliceDiskConcentration_of_gaussian_event {n d L : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hHalf : 2 * d ≤ n)
    (hFraction : structuralClusterFraction n L ≤ 1 / 4)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {Cg r : ℝ}
    (hRadius : r ≤ Real.exp (-Cg * structuralGrowth n L)) (z : Fin n → ℂ)
    (hEvent : GaussianAntiClusterEvent E L Cg z) :
    rowSliceDiskConcentration (d := d) (fun j => projectedComplexGaussian E z j) r ≤
      8 * ((L : ℝ) / n) + Real.exp (-sliceTailRate * d) := by
  obtain ⟨J, hJ, hCluster⟩ := hEvent
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCardN : J.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ J
  have hJHalf : (J.card : ℝ) ≤ (n : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_left hFraction (by positivity : (0 : ℝ) ≤ 2 * n)
    linarith
  have hK : (n : ℝ) / 2 ≤ ((Finset.univ \ J).card : ℝ) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hCardN]
    linarith
  have hDenom : (n : ℝ) / 2 ≤ (n - d + 1 : ℕ) := by
    have hdN : d ≤ n := by omega
    rw [Nat.cast_add, Nat.cast_sub hdN, Nat.cast_one]
    have hHalfR : 2 * (d : ℝ) ≤ n := by exact_mod_cast hHalf
    linarith
  have hWeight : 4 * (L : ℝ) / (n - d + 1 : ℕ) ≤ 8 * ((L : ℝ) / n) := by
    have h := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 4 * L)
      (by positivity : (0 : ℝ) < (n : ℝ) / 2) hDenom
    convert h using 1
    field_simp
    ring
  apply finiteDiskConcentration_le
  intro center
  have h := slice_small_ball_exponential hd (by omega : d ≤ n) (Finset.univ \ J) hK
    (fun j => projectedComplexGaussian E z j) r
    (fun w => (Finset.card_le_card (by
      intro j hj
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,
        (Finset.mem_filter.mp hj).2.trans hRadius⟩)).trans (hCluster w)) center
  exact h.trans (add_le_add_left hWeight _)

theorem integral_unit_bound_with_failure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (A : Set X) (hA : MeasurableSet A)
    {B : ℝ} (hB : 0 ≤ B) (hGood : ∀ x ∈ A, f x ≤ B) :
    ∫ x, f x ∂μ ≤ B + μ.real Aᶜ := by
  have hInt : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hf1 x))
  have hBadInt : Integrable (Aᶜ.indicator (fun _ : X => (1 : ℝ))) μ :=
    (integrable_const _).indicator hA.compl
  calc
    _ ≤ ∫ x, B + Aᶜ.indicator (fun _ : X => (1 : ℝ)) x ∂μ := by
      apply integral_mono hInt ((integrable_const B).add hBadInt)
      intro x
      change f x ≤ B + Aᶜ.indicator (fun _ : X => (1 : ℝ)) x
      by_cases hx : x ∈ A
      · simpa only [Set.indicator_apply, Set.mem_compl_iff, hx, not_true_eq_false, if_false, add_zero]
          using hGood x hx
      · simp only [Set.indicator_apply, Set.mem_compl_iff, hx, not_false_eq_true, if_true]
        linarith [hf1 x]
    _ = B + μ.real Aᶜ := by
      rw [integral_add (integrable_const B) hBadInt, integral_indicator_const (μ := μ) (1 : ℝ) hA.compl]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, one_mul]

theorem finiteMean_unit_bound_with_failure {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf1 : ∀ x, f x ≤ 1) (A : α → Prop) {B : ℝ} (hB : 0 ≤ B)
    (hGood : ∀ x, A x → f x ≤ B) : finiteMean f ≤ B + uniformProbability (fun x => ¬A x) := by
  have h := finiteMean_mono (f := f) (g := fun x => B + if ¬A x then 1 else 0) (by
    intro x
    by_cases hx : A x
    · simpa only [hx, not_true_eq_false, if_false, add_zero] using hGood x hx
    · simp only [hx, not_false_eq_true, if_true]
      linarith [hf1 x])
  simpa only [finiteMean_add, finiteMean_const, finiteMean_indicator] using h

theorem projectedGaussian_integral_slice_concentration {n d L : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hHalf : 2 * d ≤ n)
    (hFraction : structuralClusterFraction n L ≤ 1 / 4)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {Cg r : ℝ}
    (hRadius : r ≤ Real.exp (-Cg * structuralGrowth n L))
    (hSuccess : 1 - Cg * ((L : ℝ) / n) ≤ (standardComplexGaussianVectorLaw n).real
      {z | GaussianAntiClusterEvent E L Cg z}) :
    (∫ z, rowSliceDiskConcentration (d := d) (fun j => projectedComplexGaussian E z j) r
      ∂standardComplexGaussianVectorLaw n) ≤
        (8 + Cg) * ((L : ℝ) / n) + Real.exp (-sliceTailRate * d) := by
  have hMeas := rowSliceDiskConcentration_measurable (by omega : d ≤ n)
    (fun z j => projectedComplexGaussian E z j)
    (fun j => (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
      (projectedComplexGaussian_continuous E)) r
  have hGoodMeas := GaussianAntiClusterEvent_measurableSet E L Cg
  have hIntegral := integral_unit_bound_with_failure (standardComplexGaussianVectorLaw n) _ hMeas
    (fun _ => finiteDiskConcentration_nonneg _ _) (fun _ => finiteDiskConcentration_le_one _ _)
    {z | GaussianAntiClusterEvent E L Cg z} hGoodMeas (by positivity)
    (fun z hz => rowSliceDiskConcentration_of_gaussian_event hn hd hHalf hFraction E hRadius z hz)
  have hBad : (standardComplexGaussianVectorLaw n).real {z | GaussianAntiClusterEvent E L Cg z}ᶜ ≤
      Cg * ((L : ℝ) / n) := by
    rw [measureReal_compl hGoodMeas, probReal_univ]
    linarith
  linarith

def AveragedRandomNormalSmallBallTheorem : Prop :=
  ∃ Cstar R : ℝ, 0 < Cstar ∧ 0 < R ∧
    ∀ C : ℝ, Cstar ≤ C → ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
        ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
          ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
            finiteMean (fun rows : RowSliceMatrix n d =>
              ∫ z, rowSliceDiskConcentration (d := d)
                (fun j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j)
                (Real.exp (-R * Real.rpow (d : ℝ) (1 / 96)))
                ∂standardComplexGaussianVectorLaw n) ≤ R / (d : ℝ) ^ 3 + R / n

theorem averaged_random_normal_small_ball_theorem : AveragedRandomNormalSmallBallTheorem := by
  obtain ⟨a0, Cg, ha0, hCg, hGauss⟩ := fixed_subspace_gaussian_anti_clustering_theorem
  obtain ⟨Cstruct, hCstruct, hStruct⟩ := row_slice_structural_theorem_with_normal_rank
  let a : ℝ := min a0 1
  have ha : 0 < a := lt_min ha0 zero_lt_one
  have ha0Bound : a ≤ a0 := min_le_left _ _
  have haOne : a ≤ 1 := min_le_right _ _
  let Cstar : ℝ := max Cstruct 1
  let R : ℝ := 2 * Cg + 20
  have hR : 0 < R := by dsimp [R]; linarith
  refine ⟨Cstar, R, lt_of_lt_of_le hCstruct (le_max_left _ _), hR, ?_⟩
  intro C hC σ Z₀ hσ0 hσ1
  have hCStruct : Cstruct ≤ C := (le_max_left _ _).trans hC
  have hCOne : 1 ≤ C := (le_max_right _ _).trans hC
  have hCPos : 0 < C := lt_of_lt_of_le zero_lt_one hCOne
  obtain ⟨NS, hNS⟩ := hStruct a ha haOne C hCStruct σ Z₀ hσ0 hσ1
  obtain ⟨NG, hNG⟩ := hGauss C hCOne σ hσ0 hσ1 a ha ha0Bound
  obtain ⟨NP, hNP⟩ := eventually_atTop.mp (eventually_fresh_row_gaussian_parameters hCPos hσ1.le)
  refine ⟨max NS (max NG NP), ?_⟩
  intro n hn d hBand L hL I hI ζ hShift
  have hnS : NS ≤ n := (le_max_left _ _).trans hn
  have hnG : NG ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnP : NP ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  obtain ⟨hnPos, hdPos, hHalf, hCubic, hTail, hParams⟩ := hNP n hnP d hBand
  obtain ⟨_, _, hLower, hUpper, hFraction⟩ := hParams L hL
  haveI := rowSlice_nonempty (by omega : d ≤ n)
  have hRadius := gaussianSourceRadius_degree_comparison hdPos hCubic hL hCg.le
    (show 2 * Cg ≤ R by dsimp [R]; linarith)
  let f := fun rows : RowSliceMatrix n d => ∫ z, rowSliceDiskConcentration (d := d)
    (fun j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j)
    (Real.exp (-R * Real.rpow (d : ℝ) (1 / 96))) ∂standardComplexGaussianVectorLaw n
  have hf1 : ∀ rows, f rows ≤ 1 := by
    intro rows
    have hMeas := rowSliceDiskConcentration_measurable (by omega : d ≤ n)
      (fun z j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j)
      (fun j => (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
        (projectedComplexGaussian_continuous _))
      (Real.exp (-R * Real.rpow (d : ℝ) (1 / 96)))
    have hInt := Integrable.of_bound (μ := standardComplexGaussianVectorLaw n)
      hMeas.aestronglyMeasurable 1 (ae_of_all _ (fun z => by
        simp only [rowSliceDiskConcentration, Real.norm_eq_abs]
        rw [abs_of_nonneg (finiteDiskConcentration_nonneg _ _)]
        exact finiteDiskConcentration_le_one _ _))
    have h := integral_mono hInt (integrable_const (1 : ℝ)) (fun _ => finiteDiskConcentration_le_one _ _)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hGood : ∀ rows, SourceStructuralRowSpan L a I ζ rows →
      f rows ≤ (8 + Cg) * ((L : ℝ) / n) + Real.exp (-sliceTailRate * d) := by
    intro rows hRows
    have hDimension : Module.finrank ℂ (enlargedRetainedRowSpan I ζ rows) = n - L :=
      (enlargedRetainedRowSpan_finrank I ζ rows).trans hI
    have hSuccess := hNG n hnG d hBand L hLower hUpper (enlargedRetainedRowSpan I ζ rows)
      hDimension (enlargedRetainedRowSpan_structural a I ζ rows hRows)
    exact projectedGaussian_integral_slice_concentration hnPos hdPos hHalf hFraction _ hRadius hSuccess
  have hMean := finiteMean_unit_bound_with_failure f hf1 (SourceStructuralRowSpan L a I ζ)
    (by positivity : 0 ≤ (8 + Cg) * ((L : ℝ) / n) + Real.exp (-sliceTailRate * d)) hGood
  have hFail : uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceStructuralRowSpan L a I ζ rows) ≤
      5 / (n : ℝ) := by
    rw [uniformProbability_not]
    linarith [hNS n hnS d hBand L hL I hI ζ hShift]
  have hLRatio : (L : ℝ) / n ≤ 1 / (d : ℝ) ^ 3 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
    have h := div_le_div_of_nonneg_right hUpper hnR.le
    convert h using 1
    field_simp
  have hScaled := mul_le_mul_of_nonneg_left hLRatio (by linarith : 0 ≤ 8 + Cg)
  have hDConst : (8 + Cg) * (1 / (d : ℝ) ^ 3) + 1 / (d : ℝ) ^ 3 ≤ R / (d : ℝ) ^ 3 := by
    calc
      _ = (9 + Cg) / (d : ℝ) ^ 3 := by ring
      _ ≤ R / (d : ℝ) ^ 3 := div_le_div_of_nonneg_right
        (by dsimp [R]; linarith) (by positivity)
  have hNConst : 5 / (n : ℝ) ≤ R / n := div_le_div_of_nonneg_right
    (by dsimp [R]; linarith) (Nat.cast_nonneg n)
  exact hMean.trans (by linarith)

end CircularLaw
