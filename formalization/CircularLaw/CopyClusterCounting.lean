import CircularLaw.ProjectedGaussianCopies
import CircularLaw.GaussianCorrelationSmallBall

/-!
# Closeness to representatives across all Gaussian copies

A coordinate is far if any copy is far from its assigned representative.
The union bound, integration of the finite coordinate count and Markov
give failure at most `2*p*beta` for half the retained coordinates to be
far. The estimate needs only the actual marginal correlation bounds.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def copyFarCoordinates {n p : ℕ} (K : Finset (Fin n)) (r : Fin n → Fin n)
    (Y : Fin p → Fin n → ℂ) (α : ℝ) : Finset (Fin n) :=
  K.filter (fun j => ∃ k : Fin p, α ≤ ‖Y k j - Y k (r j)‖)

theorem copyFarCoordinates_count_eq_sum {n p : ℕ} (K : Finset (Fin n)) (r : Fin n → Fin n)
    (Y : Fin p → Fin n → ℂ) (α : ℝ) :
    ((copyFarCoordinates K r Y α).card : ℝ) =
      ∑ j ∈ K, if ∃ k : Fin p, α ≤ ‖Y k j - Y k (r j)‖ then (1 : ℝ) else 0 := by
  simp only [copyFarCoordinates, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem copyFarCoordinates_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (K : Finset (Fin n)) (r : Fin n → Fin n) (Y : Ω → Fin p → Fin n → ℂ) (α β : ℝ)
    (hY : ∀ k j, Measurable (fun ω => Y ω k j))
    (hTail : ∀ k, ∀ j ∈ K, μ.real {ω | α ≤ ‖Y ω k j - Y ω k (r j)‖} ≤ β) :
    Measurable (fun ω => ((copyFarCoordinates K r (Y ω) α).card : ℝ)) ∧
      Integrable (fun ω => ((copyFarCoordinates K r (Y ω) α).card : ℝ)) μ ∧
      (∫ ω, ((copyFarCoordinates K r (Y ω) α).card : ℝ) ∂μ) ≤
        (p : ℝ) * β * K.card := by
  let A := fun j => {ω | ∃ k : Fin p, α ≤ ‖Y ω k j - Y ω k (r j)‖}
  have hUnion (j : Fin n) : A j = ⋃ k : Fin p, {ω | α ≤ ‖Y ω k j - Y ω k (r j)‖} := by
    ext ω
    simp only [A, Set.mem_setOf_eq, Set.mem_iUnion]
  have hMeas (j : Fin n) : MeasurableSet (A j) := by
    rw [hUnion]
    exact MeasurableSet.iUnion (fun k =>
      measurableSet_le measurable_const ((hY k j).sub (hY k (r j))).norm)
  have hBad (j : Fin n) (hj : j ∈ K) : μ.real (A j) ≤ (p : ℝ) * β := by
    rw [hUnion]
    apply (measureReal_iUnion_fintype_le _).trans
    calc
      _ ≤ ∑ _k : Fin p, β := Finset.sum_le_sum (fun k _ => hTail k j hj)
      _ = _ := by simp [mul_comm]
  let F := fun j => (A j).indicator (fun _ => (1 : ℝ))
  have hFInt (j : Fin n) : Integrable (F j) μ :=
    (integrable_const _).indicator (hMeas j)
  have hFMeas (j : Fin n) : Measurable (F j) := measurable_const.indicator (hMeas j)
  have hEq : (fun ω => ((copyFarCoordinates K r (Y ω) α).card : ℝ)) =
      fun ω => ∑ j ∈ K, F j ω := by
    funext ω
    rw [copyFarCoordinates_count_eq_sum]
    simp only [F, A, Set.indicator_apply, Set.mem_setOf_eq]
  rw [hEq]
  refine ⟨Finset.measurable_sum K (fun j _ => hFMeas j),
    integrable_finset_sum K (fun j _ => hFInt j), ?_⟩
  rw [integral_finset_sum K (fun j _ => hFInt j)]
  calc
    _ = ∑ j ∈ K, μ.real (A j) := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [F, smul_eq_mul, mul_one] using
        integral_indicator_const (μ := μ) (1 : ℝ) (hMeas j)
    _ ≤ ∑ _j ∈ K, (p : ℝ) * β := Finset.sum_le_sum hBad
    _ = _ := by simp [mul_comm]

theorem copyFarCoordinates_half_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (K : Finset (Fin n)) (hK : K.Nonempty) (r : Fin n → Fin n)
    (Y : Ω → Fin p → Fin n → ℂ) (α β : ℝ)
    (hY : ∀ k j, Measurable (fun ω => Y ω k j))
    (hTail : ∀ k, ∀ j ∈ K, μ.real {ω | α ≤ ‖Y ω k j - Y ω k (r j)‖} ≤ β) :
    μ.real {ω | (K.card : ℝ) / 2 ≤ ((copyFarCoordinates K r (Y ω) α).card : ℝ)} ≤
      2 * (p : ℝ) * β := by
  obtain ⟨_, hInt, hMean⟩ := copyFarCoordinates_integral_bound μ K r Y α β hY hTail
  have hThreshold : 0 < (K.card : ℝ) / 2 := by
    have hPos : (0 : ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
    positivity
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => Nat.cast_nonneg (copyFarCoordinates K r (Y ω) α).card))
    hInt ((K.card : ℝ) / 2)
  apply (mul_le_mul_iff_of_pos_left hThreshold).mp
  calc
    _ ≤ (p : ℝ) * β * K.card := hMarkov.trans hMean
    _ = _ := by ring

theorem projectedGaussianCopies_correlated_half_probability {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n))
    (hK : K.Nonempty) (r : Fin n → Fin n) (α β : ℝ)
    (hCorr : ∀ j ∈ K, projectedGaussianStronglyCorrelated E α β j (r j)) :
    (standardGaussianCopiesLaw n p).real
      {z | (K.card : ℝ) / 2 ≤
        ((copyFarCoordinates K r (fun k j => projectedGaussianCopies E z k j) α).card : ℝ)} ≤
      2 * (p : ℝ) * β := by
  apply copyFarCoordinates_half_probability (standardGaussianCopiesLaw n p) K hK r _ α β
  · intro k j
    exact ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
      (projectedGaussianCopies_continuous E k)).measurable
  · intro k j hj
    rw [projectedGaussianCopies_pair_tail]
    exact hCorr j hj

theorem copyFarCoordinates_half_success {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (K : Finset (Fin n)) (hK : K.Nonempty) (r : Fin n → Fin n)
    (Y : Ω → Fin p → Fin n → ℂ) (α β : ℝ)
    (hY : ∀ k j, Measurable (fun ω => Y ω k j))
    (hTail : ∀ k, ∀ j ∈ K, μ.real {ω | α ≤ ‖Y ω k j - Y ω k (r j)‖} ≤ β) :
    MeasurableSet {ω | ((copyFarCoordinates K r (Y ω) α).card : ℝ) < (K.card : ℝ) / 2} ∧
      1 - 2 * (p : ℝ) * β ≤
        μ.real {ω | ((copyFarCoordinates K r (Y ω) α).card : ℝ) < (K.card : ℝ) / 2} := by
  have hMeas := (copyFarCoordinates_integral_bound μ K r Y α β hY hTail).1
  have hBadMeas : MeasurableSet
      {ω | (K.card : ℝ) / 2 ≤ ((copyFarCoordinates K r (Y ω) α).card : ℝ)} :=
    measurableSet_le measurable_const hMeas
  have hGoodMeas : MeasurableSet
      {ω | ((copyFarCoordinates K r (Y ω) α).card : ℝ) < (K.card : ℝ) / 2} :=
    measurableSet_lt hMeas measurable_const
  have hCompl : {ω | (K.card : ℝ) / 2 ≤ ((copyFarCoordinates K r (Y ω) α).card : ℝ)}ᶜ =
      {ω | ((copyFarCoordinates K r (Y ω) α).card : ℝ) < (K.card : ℝ) / 2} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  refine ⟨hGoodMeas, ?_⟩
  rw [← hCompl, probReal_compl_eq_one_sub hBadMeas]
  exact sub_le_sub_left (copyFarCoordinates_half_probability μ K hK r Y α β hY hTail) 1

end CircularLaw
