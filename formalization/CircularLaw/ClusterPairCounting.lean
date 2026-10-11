import CircularLaw.GaussianCorrelationSmallBall

/-!
# Counting non-correlated close pairs in a large coordinate disk

If each index has at most `b` correlated neighbours in the retained set,
a disk containing at least `2*b` indices contributes at least `2*b^2`
ordered close non-correlated pairs. Averaging this count gives the cluster
probability bound without independence between coordinates.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def noncorrelatedClosePairCount {n : ℕ} (K : Finset (Fin n)) (R : Fin n → Fin n → Prop)
    (y : Fin n → ℂ) (r : ℝ) : ℕ :=
  ∑ i ∈ K, (K.filter (fun j => ¬ R i j ∧ ‖y i - y j‖ ≤ 2 * r)).card

theorem coordinate_disk_close_pairs {n : ℕ} (y : Fin n → ℂ) {r : ℝ} (w : ℂ)
    {i j : Fin n} (hi : ‖y i - w‖ ≤ r) (hj : ‖y j - w‖ ≤ r) :
    ‖y i - y j‖ ≤ 2 * r := by
  calc
    ‖y i - y j‖ = dist (y i) (y j) := (dist_eq_norm _ _).symm
    _ ≤ dist (y i) w + dist w (y j) := dist_triangle _ _ _
    _ = ‖y i - w‖ + ‖y j - w‖ := by rw [dist_eq_norm, dist_comm w (y j), dist_eq_norm]
    _ ≤ 2 * r := by linarith

theorem large_disk_noncorrelatedClosePairCount {n b : ℕ}
    (K : Finset (Fin n)) (R : Fin n → Fin n → Prop) (y : Fin n → ℂ) (r : ℝ)
    (hR : ∀ i ∈ K, (K.filter (R i)).card ≤ b) (w : ℂ)
    (hDisk : 2 * b ≤ (K.filter (fun j => ‖y j - w‖ ≤ r)).card) :
    2 * b ^ 2 ≤ noncorrelatedClosePairCount K R y r := by
  let S := K.filter (fun j => ‖y j - w‖ ≤ r)
  have hSK : S ⊆ K := Finset.filter_subset _ _
  have hRow (i : Fin n) (hi : i ∈ S) :
      b ≤ (K.filter (fun j => ¬ R i j ∧ ‖y i - y j‖ ≤ 2 * r)).card := by
    have hCorr : (S.filter (R i)).card ≤ b :=
      (Finset.card_le_card (Finset.filter_subset_filter _ hSK)).trans (hR i (hSK hi))
    have hPartition := Finset.card_filter_add_card_filter_not (s := S) (p := R i)
    have hCount : b ≤ (S.filter (fun j => ¬ R i j)).card := by
      change 2 * b ≤ S.card at hDisk
      omega
    apply hCount.trans (Finset.card_le_card ?_)
    intro j hj
    obtain ⟨hjS, hjR⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hSK hjS, hjR,
      coordinate_disk_close_pairs y w (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hjS).2⟩
  calc
    2 * b ^ 2 = b * (2 * b) := by ring
    _ ≤ b * S.card := Nat.mul_le_mul_left _ hDisk
    _ = ∑ _i ∈ S, b := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ S, (K.filter (fun j => ¬ R i j ∧ ‖y i - y j‖ ≤ 2 * r)).card :=
      Finset.sum_le_sum hRow
    _ ≤ noncorrelatedClosePairCount K R y r :=
      Finset.sum_le_sum_of_subset_of_nonneg hSK (fun _ _ _ => Nat.zero_le _)

theorem noncorrelatedClosePairCount_eq_sum {n : ℕ}
    (K : Finset (Fin n)) (R : Fin n → Fin n → Prop) (y : Fin n → ℂ) (r : ℝ) :
    (noncorrelatedClosePairCount K R y r : ℝ) =
      ∑ i ∈ K, ∑ j ∈ K, if ¬ R i j ∧ ‖y i - y j‖ ≤ 2 * r then (1 : ℝ) else 0 := by
  simp only [noncorrelatedClosePairCount, Nat.cast_sum, Finset.card_filter, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem noncorrelatedClosePairCount_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (K : Finset (Fin n)) (R : Fin n → Fin n → Prop) (Y : Ω → Fin n → ℂ) (r : ℝ)
    (hY : ∀ i, Measurable (fun ω => Y ω i)) {s : ℝ}
    (hSmall : ∀ i ∈ K, ∀ j ∈ K, ¬ R i j → μ.real {ω | ‖Y ω i - Y ω j‖ ≤ 2 * r} ≤ s ^ 2) :
    Integrable (fun ω => (noncorrelatedClosePairCount K R (Y ω) r : ℝ)) μ ∧
      (∫ ω, (noncorrelatedClosePairCount K R (Y ω) r : ℝ) ∂μ) ≤
        (K.card : ℝ) ^ 2 * s ^ 2 := by
  let F := fun i j (ω : Ω) =>
    {ω | ¬ R i j ∧ ‖Y ω i - Y ω j‖ ≤ 2 * r}.indicator (fun _ => (1 : ℝ)) ω
  have hEvent (i j : Fin n) : MeasurableSet {ω | ¬ R i j ∧ ‖Y ω i - Y ω j‖ ≤ 2 * r} := by
    by_cases h : R i j
    · simp [h]
    · simpa only [h, not_false_eq_true, true_and] using
        measurableSet_le ((hY i).sub (hY j)).norm measurable_const
  have hInt (i j : Fin n) : Integrable (F i j) μ :=
    (integrable_const _).indicator (hEvent i j)
  have hEq : (fun ω => (noncorrelatedClosePairCount K R (Y ω) r : ℝ)) =
      fun ω => ∑ i ∈ K, ∑ j ∈ K, F i j ω := by
    funext ω
    rw [noncorrelatedClosePairCount_eq_sum]
    simp only [F, Set.indicator_apply, Set.mem_setOf_eq]
  rw [hEq]
  constructor
  · exact integrable_finset_sum K (fun i _ => integrable_finset_sum K (fun j _ => hInt i j))
  · rw [integral_finset_sum _ (fun i _ => integrable_finset_sum K (fun j _ => hInt i j))]
    calc
      _ = ∑ i ∈ K, ∑ j ∈ K, μ.real {ω | ¬ R i j ∧ ‖Y ω i - Y ω j‖ ≤ 2 * r} := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finset_sum _ (fun j _ => hInt i j)]
        apply Finset.sum_congr rfl
        intro j _
        simpa only [F, smul_eq_mul, mul_one] using
          integral_indicator_const (μ := μ) (1 : ℝ) (hEvent i j)
      _ ≤ ∑ _i ∈ K, ∑ _j ∈ K, s ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases h : R i j
        · simp only [h, not_true_eq_false, false_and, Set.setOf_false, measureReal_empty]
          positivity
        · simpa only [h, not_false_eq_true, true_and] using hSmall i hi j hj h
      _ = (K.card : ℝ) ^ 2 * s ^ 2 := by simp [pow_two, mul_assoc]

theorem bounded_correlation_large_disk_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n b : ℕ} (hb : 0 < b)
    (K : Finset (Fin n)) (R : Fin n → Fin n → Prop) (Y : Ω → Fin n → ℂ) (r : ℝ)
    (hY : ∀ i, Measurable (fun ω => Y ω i))
    (hR : ∀ i ∈ K, (K.filter (R i)).card ≤ b) {s : ℝ}
    (hSmall : ∀ i ∈ K, ∀ j ∈ K, ¬ R i j → μ.real {ω | ‖Y ω i - Y ω j‖ ≤ 2 * r} ≤ s ^ 2) :
    μ.real {ω | ∃ w : ℂ, 2 * b ≤ (K.filter (fun j => ‖Y ω j - w‖ ≤ r)).card} ≤
      ((s * K.card) ^ 2) / (2 * (b : ℝ) ^ 2) := by
  obtain ⟨hInt, hMean⟩ := noncorrelatedClosePairCount_integral_bound μ K R Y r hY hSmall
  have hThreshold : 0 < 2 * (b : ℝ) ^ 2 := by positivity
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => Nat.cast_nonneg (noncorrelatedClosePairCount K R (Y ω) r)))
    hInt (2 * (b : ℝ) ^ 2)
  have hContain : {ω | ∃ w : ℂ, 2 * b ≤ (K.filter (fun j => ‖Y ω j - w‖ ≤ r)).card} ⊆
      {ω | 2 * (b : ℝ) ^ 2 ≤ (noncorrelatedClosePairCount K R (Y ω) r : ℝ)} := by
    rintro ω ⟨w, hw⟩
    exact_mod_cast large_disk_noncorrelatedClosePairCount K R (Y ω) r hR w hw
  apply (measureReal_mono hContain).trans
  apply (le_div_iff₀ hThreshold).mpr
  have h := hMarkov.trans hMean
  nlinarith only [h]

end CircularLaw
