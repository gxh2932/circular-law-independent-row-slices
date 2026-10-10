import CircularLaw.GaussianCopiesCombinationLaw
import CircularLaw.GaussianCorrelationSmallBall

/-!
# Coordinate tails for the actual projected Gaussian

Each coordinate has the exact scale given by the projection of its basis
vector. Projection contraction bounds that scale by one. The resulting
tail bound applies to each fixed unit combination and to all coordinates
of all the independent copies, without coordinate independence assumptions.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators InnerProductSpace

namespace CircularLaw

theorem projectedComplexGaussian_coordinate_law {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i : Fin n) :
    (standardComplexGaussianVectorLaw n).map (fun z => projectedComplexGaussian E z i) =
      standardComplexGaussianLaw.map
        (‖Eᗮ.starProjection (EuclideanSpace.single i 1)‖ • ContinuousLinearMap.id ℝ ℂ) := by
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
    projectedComplexGaussian_inner_law E (EuclideanSpace.single i 1)

theorem projectedComplexGaussian_coordinate_scale_le_one {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i : Fin n) :
    ‖Eᗮ.starProjection (EuclideanSpace.single i 1)‖ ≤ 1 := by
  simpa only [EuclideanSpace.norm_single, norm_one] using
    Submodule.norm_starProjection_apply_le (𝕜 := ℂ) Eᗮ (EuclideanSpace.single i 1)

theorem scaledStandardComplexGaussianLaw_radial_tail_le {σ r : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hr : 0 < r) :
    (standardComplexGaussianLaw.map (σ • ContinuousLinearMap.id ℝ ℂ)).real
      {z | r ≤ ‖z‖} ≤ Real.exp (-r ^ 2) := by
  by_cases hZero : σ = 0
  · have hs : MeasurableSet {z : ℂ | r ≤ ‖z‖} :=
      (isClosed_le continuous_const continuous_norm).measurableSet
    rw [hZero, map_measureReal_apply (by fun_prop) hs]
    have hEmpty : ((0 : ℝ) • ContinuousLinearMap.id ℝ ℂ) ⁻¹' {z : ℂ | r ≤ ‖z‖} = ∅ := by
      ext z
      simp [hr]
    rw [hEmpty, measureReal_empty]
    exact (Real.exp_pos _).le
  · have hPos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hZero)
    rw [scaledStandardComplexGaussianLaw_radial_tail hPos hr.le]
    apply Real.exp_le_exp.mpr
    have hRatio : r ≤ r / σ := (le_div_iff₀ hPos).mpr
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hσ1 hr.le)
    nlinarith only [hRatio, hr, div_nonneg hr.le hσ]

theorem projectedComplexGaussian_coordinate_tail {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i : Fin n) {r : ℝ} (hr : 0 < r) :
    (standardComplexGaussianVectorLaw n).real
      {z | r ≤ ‖projectedComplexGaussian E z i‖} ≤ Real.exp (-r ^ 2) := by
  have hs : MeasurableSet {z : ℂ | r ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hMeas : Measurable (fun z => projectedComplexGaussian E z i) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).comp
      (projectedComplexGaussian_continuous E)).measurable
  have h := scaledStandardComplexGaussianLaw_radial_tail_le
    (norm_nonneg _) (projectedComplexGaussian_coordinate_scale_le_one E i) hr
  rw [← projectedComplexGaussian_coordinate_law E i, map_measureReal_apply hMeas hs] at h
  exact h

theorem projectedComplexGaussianLaw_coordinate_tail {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i : Fin n) {r : ℝ} (hr : 0 < r) :
    (projectedComplexGaussianLaw E).real {y | r ≤ ‖y i‖} ≤ Real.exp (-r ^ 2) := by
  unfold projectedComplexGaussianLaw
  rw [map_measureReal_apply (projectedComplexGaussian_continuous E).measurable
    (measurableSet_le measurable_const
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).measurable.norm)]
  exact projectedComplexGaussian_coordinate_tail E i hr

theorem projectedGaussianCopiesCombination_unit_coordinate_tail {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin p))
    (hx : ‖x‖ = 1) (i : Fin n) {r : ℝ} (hr : 0 < r) :
    (standardGaussianCopiesLaw n p).real
      {z | r ≤ ‖gaussianCopiesCombination (projectedGaussianCopies E z) x i‖} ≤
      Real.exp (-r ^ 2) := by
  change (standardGaussianCopiesLaw n p).real
    {z | gaussianCopiesCombination (projectedGaussianCopies E z) x ∈
      {y : EuclideanSpace ℂ (Fin n) | r ≤ ‖y i‖}} ≤ _
  rw [projectedGaussianCopiesCombination_unit_event_real E x hx
    {y | r ≤ ‖y i‖}
    (measurableSet_le measurable_const
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).measurable.norm)]
  exact projectedComplexGaussianLaw_coordinate_tail E i hr

theorem projectedGaussianCopies_coordinate_tail {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (k : Fin p) (i : Fin n)
    {r : ℝ} (hr : 0 < r) :
    (standardGaussianCopiesLaw n p).real
      {z | r ≤ ‖projectedGaussianCopies E z k i‖} ≤ Real.exp (-r ^ 2) := by
  have hs : MeasurableSet {y : EuclideanSpace ℂ (Fin n) | r ≤ ‖y i‖} :=
    measurableSet_le measurable_const
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).measurable.norm
  have h := map_measureReal_apply (μ := standardGaussianCopiesLaw n p)
    (projectedGaussianCopies_continuous E k).measurable hs
  rw [projectedGaussianCopies_law E k] at h
  exact h.symm.trans_le (projectedComplexGaussianLaw_coordinate_tail E i hr)

theorem projectedGaussianCopies_any_coordinate_tail {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {r : ℝ} (hr : 0 < r) :
    (standardGaussianCopiesLaw n p).real
      {z | ∃ k : Fin p, ∃ i : Fin n, r ≤ ‖projectedGaussianCopies E z k i‖} ≤
      (p : ℝ) * n * Real.exp (-r ^ 2) := by
  have hUnion : {z | ∃ k : Fin p, ∃ i : Fin n, r ≤ ‖projectedGaussianCopies E z k i‖} =
      ⋃ j : Fin p × Fin n, {z | r ≤ ‖projectedGaussianCopies E z j.1 j.2‖} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Prod.exists]
  rw [hUnion]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _j : Fin p × Fin n, Real.exp (-r ^ 2) :=
      Finset.sum_le_sum (fun j _ => projectedGaussianCopies_coordinate_tail E j.1 j.2 hr)
    _ = _ := by simp [Nat.cast_mul, mul_assoc]

theorem projectedGaussianCopiesCombination_finite_unit_coordinate_tail {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (S : Finset (EuclideanSpace ℂ (Fin p))) (hS : ∀ x ∈ S, ‖x‖ = 1)
    {r : ℝ} (hr : 0 < r) :
    (standardGaussianCopiesLaw n p).real
      {z | ∃ x ∈ S, ∃ i : Fin n,
        r ≤ ‖gaussianCopiesCombination (projectedGaussianCopies E z) x i‖} ≤
      (S.card : ℝ) * n * Real.exp (-r ^ 2) := by
  have hUnion : {z | ∃ x ∈ S, ∃ i : Fin n,
      r ≤ ‖gaussianCopiesCombination (projectedGaussianCopies E z) x i‖} =
      ⋃ x ∈ S, ⋃ i : Fin n,
        {z | r ≤ ‖gaussianCopiesCombination (projectedGaussianCopies E z) x i‖} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hUnion]
  apply (measureReal_biUnion_finset_le S _).trans
  calc
    _ ≤ ∑ _x ∈ S, (n : ℝ) * Real.exp (-r ^ 2) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (measureReal_iUnion_fintype_le _).trans
      calc
        _ ≤ ∑ _i : Fin n, Real.exp (-r ^ 2) := Finset.sum_le_sum
          (fun i _ => projectedGaussianCopiesCombination_unit_coordinate_tail E x (hS x hx) i hr)
        _ = _ := by simp
    _ = _ := by simp [mul_assoc]

theorem gaussianCopiesCombination_coordinate_norm_bound {n p : ℕ}
    (Y : Fin p → EuclideanSpace ℂ (Fin n)) (x : EuclideanSpace ℂ (Fin p)) (i : Fin n) :
    ‖gaussianCopiesCombination Y x i‖ ≤ ‖x‖ * Real.sqrt (∑ k, ‖Y k i‖ ^ 2) := by
  let a : EuclideanSpace ℂ (Fin p) := WithLp.toLp 2 (fun k => star (x k))
  let b : EuclideanSpace ℂ (Fin p) := WithLp.toLp 2 (fun k => Y k i)
  have hNorm : ‖a‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg a) (norm_nonneg x)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp [a]
  have hInner : ⟪a, b⟫_ℂ = gaussianCopiesCombination Y x i := by
    rw [gaussianCopiesCombination_coordinate]
    simp [PiLp.inner_apply, a, b, mul_comm]
  calc
    _ = ‖⟪a, b⟫_ℂ‖ := congrArg norm hInner.symm
    _ ≤ ‖a‖ * ‖b‖ := norm_inner_le_norm a b
    _ = _ := by rw [hNorm, EuclideanSpace.norm_eq b]

theorem gaussianCopiesCombination_uniform_coordinate_bound {n p : ℕ}
    (Y : Fin p → EuclideanSpace ℂ (Fin n)) (x : EuclideanSpace ℂ (Fin p))
    (hx : ‖x‖ ≤ 1) (i : Fin n) {r : ℝ} (hr : 0 ≤ r) (hY : ∀ k, ‖Y k i‖ ≤ r) :
    ‖gaussianCopiesCombination Y x i‖ ≤ Real.sqrt p * r := by
  have hSum : (∑ k : Fin p, ‖Y k i‖ ^ 2) ≤ (p : ℝ) * r ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin p, r ^ 2 := Finset.sum_le_sum
        (fun k _ => (sq_le_sq₀ (norm_nonneg _) hr).mpr (hY k))
      _ = _ := by simp
  calc
    _ ≤ ‖x‖ * Real.sqrt (∑ k, ‖Y k i‖ ^ 2) :=
      gaussianCopiesCombination_coordinate_norm_bound Y x i
    _ ≤ Real.sqrt (∑ k, ‖Y k i‖ ^ 2) :=
      by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt ((p : ℝ) * r ^ 2) := Real.sqrt_le_sqrt hSum
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg p), Real.sqrt_sq hr]

theorem projectedGaussianCopies_all_coordinates_success {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {r : ℝ} (hr : 0 < r) :
    MeasurableSet {z | ∀ k : Fin p, ∀ i : Fin n, ‖projectedGaussianCopies E z k i‖ < r} ∧
      1 - (p : ℝ) * n * Real.exp (-r ^ 2) ≤ (standardGaussianCopiesLaw n p).real
        {z | ∀ k : Fin p, ∀ i : Fin n, ‖projectedGaussianCopies E z k i‖ < r} := by
  have hMeas (k : Fin p) (i : Fin n) : Measurable (fun z => ‖projectedGaussianCopies E z k i‖) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).comp
      (projectedGaussianCopies_continuous E k)).measurable.norm
  have hBadMeas : MeasurableSet
      {z | ∃ k : Fin p, ∃ i : Fin n, r ≤ ‖projectedGaussianCopies E z k i‖} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun k => MeasurableSet.iUnion
      (fun i => measurableSet_le measurable_const (hMeas k i)))
  have hCompl : {z | ∃ k : Fin p, ∃ i : Fin n, r ≤ ‖projectedGaussianCopies E z k i‖}ᶜ =
      {z | ∀ k : Fin p, ∀ i : Fin n, ‖projectedGaussianCopies E z k i‖ < r} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_le]
  refine ⟨by rw [← hCompl]; exact hBadMeas.compl, ?_⟩
  rw [← hCompl, probReal_compl_eq_one_sub hBadMeas]
  exact sub_le_sub_left (projectedGaussianCopies_any_coordinate_tail E hr) 1

theorem projectedGaussianCopies_uniform_coordinate_bound_on_success {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (z : Fin p → (Fin n → ℂ))
    {r : ℝ} (hr : 0 ≤ r)
    (hGood : ∀ k : Fin p, ∀ i : Fin n, ‖projectedGaussianCopies E z k i‖ < r) :
    ∀ x : EuclideanSpace ℂ (Fin p), ‖x‖ ≤ 1 → ∀ i : Fin n,
      ‖gaussianCopiesCombination (projectedGaussianCopies E z) x i‖ ≤ Real.sqrt p * r := by
  intro x hx i
  exact gaussianCopiesCombination_uniform_coordinate_bound _ x hx i hr (fun k => (hGood k i).le)

theorem projectedGaussianCopies_uniform_coordinate_success {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {r : ℝ} (hr : 0 < r) :
    ∃ A : Set (Fin p → (Fin n → ℂ)), MeasurableSet A ∧
      1 - (p : ℝ) * n * Real.exp (-r ^ 2) ≤ (standardGaussianCopiesLaw n p).real A ∧
      ∀ z ∈ A, ∀ x : EuclideanSpace ℂ (Fin p), ‖x‖ ≤ 1 → ∀ i : Fin n,
        ‖gaussianCopiesCombination (projectedGaussianCopies E z) x i‖ ≤ Real.sqrt p * r := by
  obtain ⟨hMeas, hProb⟩ := projectedGaussianCopies_all_coordinates_success E hr
  refine ⟨{z | ∀ k : Fin p, ∀ i : Fin n, ‖projectedGaussianCopies E z k i‖ < r},
    hMeas, hProb, ?_⟩
  intro z hz
  exact projectedGaussianCopies_uniform_coordinate_bound_on_success E z hr.le hz

theorem projectedGaussianCopies_uniform_coordinate_log_success {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {ε : ℝ}
    (hε : 0 < ε) (hεpn : ε < (p : ℝ) * n) :
    ∃ A : Set (Fin p → (Fin n → ℂ)), MeasurableSet A ∧
      1 - ε ≤ (standardGaussianCopiesLaw n p).real A ∧
      ∀ z ∈ A, ∀ x : EuclideanSpace ℂ (Fin p), ‖x‖ ≤ 1 → ∀ i : Fin n,
        ‖gaussianCopiesCombination (projectedGaussianCopies E z) x i‖ ≤
          Real.sqrt p * Real.sqrt (Real.log ((p : ℝ) * n / ε)) := by
  have hPN : 0 < (p : ℝ) * n := hε.trans hεpn
  have hRatio : 1 < (p : ℝ) * n / ε := (one_lt_div hε).mpr hεpn
  have hLog : 0 < Real.log ((p : ℝ) * n / ε) := Real.log_pos hRatio
  have hFailure : (p : ℝ) * n *
      Real.exp (-(Real.sqrt (Real.log ((p : ℝ) * n / ε))) ^ 2) = ε := by
    rw [Real.sq_sqrt hLog.le, Real.exp_neg, Real.exp_log (zero_lt_one.trans hRatio)]
    field_simp
    exact div_self hPN.ne'
  obtain ⟨A, hMeas, hProb, hBound⟩ := projectedGaussianCopies_uniform_coordinate_success E
    (Real.sqrt_pos.mpr hLog)
  rw [hFailure] at hProb
  exact ⟨A, hMeas, hProb, hBound⟩

end CircularLaw
