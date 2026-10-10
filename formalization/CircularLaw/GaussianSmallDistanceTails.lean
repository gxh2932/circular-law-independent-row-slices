import CircularLaw.GaussianRectangularDistances

/-!
# Arbitrarily small leave-one-out Gaussian distances

The checked projected Gaussian small-ball estimate gives the simpler
uniform bound exp(1)*u whenever the conditioned span has positive
codimension. Fresh-row exposure and conjugation transfer this estimate
to every actual row distance, and a finite union controls them together.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem shifted_gaussian_span_distance_linear_tail {ι : Type*} [Fintype ι] {n : ℕ}
    (rows : ι → EuclideanSpace ℂ (Fin n)) (hRows : Fintype.card ι < n)
    (w : EuclideanSpace ℂ (Fin n)) {u : ℝ} (hu : 0 < u) :
    (standardComplexGaussianVectorLaw n).real
      {z | finiteSpanDistance (standardComplexGaussianVector n z + w) rows ^ 2 ≤ u} ≤
        Real.exp 1 * u := by
  by_cases hSmall : Real.exp 1 * u ≤ 1
  · let p := Module.finrank ℂ (Submodule.span ℂ (Set.range rows))ᗮ
    have hp : 0 < p :=
      (Nat.sub_pos_of_lt hRows).trans_le (finite_span_orthogonal_finrank_lower rows)
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hBase : Real.exp 1 * u / p ≤ Real.exp 1 * u :=
      div_le_self (by positivity) hpOne
    have hPow := pow_le_pow_of_le_one (by positivity : (0 : ℝ) ≤ Real.exp 1 * u / p)
      (hBase.trans hSmall) (Nat.succ_le_of_lt hp)
    have hPowLe : (Real.exp 1 * u / p) ^ p ≤ Real.exp 1 * u / p := by
      simpa only [pow_one] using hPow
    exact (shifted_gaussian_finite_span_distance_smallBall rows hRows w hu).trans
      (hPowLe.trans hBase)
  · have hProb : (standardComplexGaussianVectorLaw n).real
        {z | finiteSpanDistance (standardComplexGaussianVector n z + w) rows ^ 2 ≤ u} ≤ 1 := by
      simpa only [probReal_univ] using measureReal_mono (μ := standardComplexGaussianVectorLaw n)
        (Set.subset_univ {z | finiteSpanDistance (standardComplexGaussianVector n z + w) rows ^ 2 ≤ u})
    exact hProb.trans (le_of_not_ge hSmall)

theorem independent_gaussian_span_distance_linear_tail {ι X : Type*} [Fintype ι] {n : ℕ}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (rows : ι → X → EuclideanSpace ℂ (Fin n)) (w : X → EuclideanSpace ℂ (Fin n))
    (hRows : ∀ i, Continuous (rows i)) (hw : Continuous w) (hCard : Fintype.card ι < n)
    {u : ℝ} (hu : 0 < u) :
    (μ.prod (standardComplexGaussianVectorLaw n)).real
      {p | independentGaussianSpanDistance rows w p ^ 2 ≤ u} ≤ Real.exp 1 * u := by
  apply probability_product_event_le_sections μ (standardComplexGaussianVectorLaw n) _
    (measurableSet_le ((measurable_independent_gaussian_span_distance rows w hRows hw).pow_const 2)
      measurable_const) (by positivity)
  intro x
  exact shifted_gaussian_span_distance_linear_tail (fun i => rows i x) hCard (w x) hu

theorem gaussian_leave_one_out_distance_linear_tail {m n : ℕ}
    (w : Fin (m + 1) → EuclideanSpace ℂ (Fin n)) (hmn : m < n) (i : Fin (m + 1))
    {u : ℝ} (hu : 0 < u) :
    (gaussianRowsLaw (m + 1) n).real
      {x | gaussianLeaveOneOutDistance w x i ^ 2 ≤ u} ≤ Real.exp 1 * u := by
  let rows : Fin m → GaussianRowsSample m n → EuclideanSpace ℂ (Fin n) :=
    fun j x => standardComplexGaussianVector n (x j) + w (i.succAbove j)
  let shift : GaussianRowsSample m n → EuclideanSpace ℂ (Fin n) := fun _ => w i
  have hRows (j : Fin m) : Continuous (rows j) :=
    ((standardComplexGaussianVector_continuous n).comp (continuous_apply j)).add continuous_const
  have hShift : Continuous shift := continuous_const
  have hMeas := measurable_independent_gaussian_span_distance rows shift hRows hShift
  have hMap := map_measureReal_apply (μ := gaussianRowsLaw (m + 1) n)
    (s := {p | independentGaussianSpanDistance rows shift p ^ 2 ≤ u})
    (gaussian_fresh_row_exposure_measurePreserving (n := n) i).measurable
    (measurableSet_le (hMeas.pow_const 2) measurable_const)
  rw [(gaussian_fresh_row_exposure_measurePreserving (n := n) i).map_eq] at hMap
  apply hMap.symm.trans_le
  simpa only [Fintype.card_fin] using independent_gaussian_span_distance_linear_tail
    (gaussianRowsLaw m n) rows shift hRows hShift
    (by simpa only [Fintype.card_fin] using hmn) hu

theorem gaussian_all_row_distances_linear_tail {m n : ℕ}
    (w : Fin (m + 1) → EuclideanSpace ℂ (Fin n)) (hmn : m < n)
    {u : ℝ} (hu : 0 < u) :
    (gaussianRowsLaw (m + 1) n).real
      {x | ∃ i, gaussianLeaveOneOutDistance w x i ^ 2 ≤ u} ≤
        (m + 1 : ℕ) * (Real.exp 1 * u) := by
  let A := fun i : Fin (m + 1) => {x | gaussianLeaveOneOutDistance w x i ^ 2 ≤ u}
  have hEq : {x | ∃ i, gaussianLeaveOneOutDistance w x i ^ 2 ≤ u} =
      ⋃ i ∈ (Finset.univ : Finset (Fin (m + 1))), A i := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_univ, exists_true_left, A]
  rw [hEq]
  calc
    _ ≤ ∑ i : Fin (m + 1), (gaussianRowsLaw (m + 1) n).real (A i) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i : Fin (m + 1), Real.exp 1 * u :=
      Finset.sum_le_sum (fun i _ => gaussian_leave_one_out_distance_linear_tail w hmn i hu)
    _ = _ := by simp

theorem gaussian_conjugate_row_distances_linear_tail {m n : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin n) ℂ) (hmn : m < n) {u : ℝ} (hu : 0 < u) :
    (gaussianRowsLaw (m + 1) n).real
      {x | ∃ i, finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B x)) i ^ 2 ≤ u} ≤
        (m + 1 : ℕ) * (Real.exp 1 * u) := by
  let w : Fin (m + 1) → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (fun j => star (B i j))
  have hConj : Measurable (fun x : GaussianRowsSample (m + 1) n => fun i j => star (x i j)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j =>
      continuous_star.measurable.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))))
  have hSet : MeasurableSet {x | ∃ i, gaussianLeaveOneOutDistance w x i ^ 2 ≤ u} := by
    have hUnion : MeasurableSet (⋃ i : Fin (m + 1), {x | gaussianLeaveOneOutDistance w x i ^ 2 ≤ u}) :=
      MeasurableSet.iUnion (fun i => measurableSet_le
        ((measurable_gaussian_leave_one_out_distance w i).pow_const 2) measurable_const)
    simpa only [Set.iUnion_setOf] using hUnion
  have hMap := map_measureReal_apply (μ := gaussianRowsLaw (m + 1) n) hConj hSet
  rw [gaussian_rows_conjugate_law] at hMap
  simp only [gaussian_conjugate_row_distance_eq]
  exact hMap.symm.trans_le (gaussian_all_row_distances_linear_tail w hmn hu)

end CircularLaw
