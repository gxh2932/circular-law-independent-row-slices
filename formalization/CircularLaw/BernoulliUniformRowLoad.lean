import CircularLaw.BernoulliRowLoadProbability
import CircularLaw.RowLoadRates

/-!
# Uniform Bernoulli row-load events at both LLY ranks

All coordinate subsets are controlled before the vector is chosen.
The ambient parameter stays d/n for every deterministic retained row set.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators

namespace CircularLaw

theorem finite_measure_finset_exists_le {Ω α : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Finset α) (E : α → Ω → Prop) :
    μ.real {ω | ∃ a ∈ S, E a ω} ≤ ∑ a ∈ S, μ.real {ω | E a ω} := by
  have hEvent : {ω | ∃ a ∈ S, E a ω} = ⋃ a ∈ S, {ω | E a ω} := by
    ext ω
    simp
  rw [hEvent]
  exact measureReal_biUnion_finset_le S (fun a => {ω | E a ω})

def BernoulliSourceRowLoad {n : ℕ} (d : ℕ) (I : Finset (Fin n)) (k : ℕ)
    (sample : BernoulliSquareSample n) : Prop :=
  (∀ J : Finset (Fin n), J.card ≤ almostConstantRank n d →
    (bernoulliRetainedEventCount I (fun row => (1 : ℝ) ≤ bernoulliRowLoad row J) sample : ℝ) ≤
      (I.card : ℝ) / 8) ∧
  (∀ J : Finset (Fin n), J.card ≤ k →
    (bernoulliRetainedEventCount I (fun row => 16 * (k : ℝ) * d / n ≤ bernoulliRowLoad row J)
      sample : ℝ) ≤ (I.card : ℝ) / 8)

def BernoulliLLYRowLoad {n : ℕ} (d : ℕ) (I : Finset (Fin n)) (k₂ k₃ : ℕ)
    (sample : BernoulliSquareSample n) : Prop :=
  BernoulliSourceRowLoad d I k₂ sample ∧ BernoulliSourceRowLoad d I k₃ sample

theorem bernoulli_uniform_row_load_failure_counting {n d k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hk : 0 < k) (I : Finset (Fin n)) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliSourceRowLoad d I k sample} ≤
      (((smallCoordinateSets n (almostConstantRank n d)).card : ℝ) +
        (smallCoordinateSets n k).card) * Real.exp (-rowLoadRate * I.card) := by
  rw [sparseBernoulliMatrixLaw_eq hn hdn]
  let μ := bernoulliSquareMatrixLaw n (rowBernoulliParameter n d) (rowBernoulliParameter_le_one hn hdn)
  let E0 := fun sample : BernoulliSquareSample n =>
    ∃ J ∈ smallCoordinateSets n (almostConstantRank n d), (I.card : ℝ) / 8 <
      bernoulliRetainedEventCount I (fun row => (1 : ℝ) ≤ bernoulliRowLoad row J) sample
  let Ek := fun sample : BernoulliSquareSample n =>
    ∃ J ∈ smallCoordinateSets n k, (I.card : ℝ) / 8 <
      bernoulliRetainedEventCount I (fun row => 16 * (k : ℝ) * d / n ≤ bernoulliRowLoad row J) sample
  have hEvent (sample : BernoulliSquareSample n) :
      ¬BernoulliSourceRowLoad d I k sample → E0 sample ∨ Ek sample := by
    intro hBad
    rcases _root_.not_and_or.mp hBad with h0 | hk
    · push_neg at h0
      obtain ⟨J, hJ, hCount⟩ := h0
      exact Or.inl ⟨J, (mem_smallCoordinateSets J).mpr hJ, hCount⟩
    · push_neg at hk
      obtain ⟨J, hJ, hCount⟩ := hk
      exact Or.inr ⟨J, (mem_smallCoordinateSets J).mpr hJ, hCount⟩
  have h0 : μ.real {sample | E0 sample} ≤
      ((smallCoordinateSets n (almostConstantRank n d)).card : ℝ) *
        Real.exp (-rowLoadRate * I.card) := by
    apply (finite_measure_finset_exists_le μ (smallCoordinateSets n (almostConstantRank n d))
      (fun J sample => (I.card : ℝ) / 8 <
        bernoulliRetainedEventCount I (fun row => (1 : ℝ) ≤ bernoulliRowLoad row J) sample)).trans
    apply (Finset.sum_le_sum (fun J hJ =>
      bernoulli_retained_many_events_failure _ _ I _
        (bernoulli_small_set_row_load_probability hn hdn J ((mem_smallCoordinateSets J).mp hJ)))).trans_eq
    simp
  have hK : μ.real {sample | Ek sample} ≤ ((smallCoordinateSets n k).card : ℝ) *
      Real.exp (-rowLoadRate * I.card) := by
    apply (finite_measure_finset_exists_le μ (smallCoordinateSets n k)
      (fun J sample => (I.card : ℝ) / 8 <
        bernoulliRetainedEventCount I (fun row => 16 * (k : ℝ) * d / n ≤ bernoulliRowLoad row J)
          sample)).trans
    apply (Finset.sum_le_sum (fun J hJ =>
      bernoulli_retained_many_events_failure _ _ I _
        (bernoulli_large_set_row_load_probability hn hd hdn hk J ((mem_smallCoordinateSets J).mp hJ)))).trans_eq
    simp
  apply (measureReal_mono (μ := μ) (fun sample hSample => hEvent sample hSample)
    (h₂ := by finiteness)).trans
  apply (measureReal_union_le {sample | E0 sample} {sample | Ek sample}).trans
  simpa only [add_mul] using add_le_add h0 hK

theorem bernoulli_uniform_row_load_failure_entropy {n d k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hk : 0 < k)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) (hRank : (k : ℝ) ≤ a * n)
    (I : Finset (Fin n)) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliSourceRowLoad d I k sample} ≤
      Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ))) - rowLoadRate * I.card) +
        Real.exp ((n : ℝ) * smallSetEntropy a - rowLoadRate * I.card) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht : (0 : ℝ) < 1 / (16 * (d : ℝ)) := by positivity
  have htOne : 1 / (16 * (d : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mpr
    linarith
  have hSize0 : (almostConstantRank n d : ℝ) ≤ (1 / (16 * (d : ℝ))) * n := by
    convert almostConstantRank_upper (n := n) hd using 1
    ring
  have hEntropy0 := smallCoordinateSets_card_density ht htOne hSize0
  have hEntropy := smallCoordinateSets_card_density ha haOne hRank
  apply (bernoulli_uniform_row_load_failure_counting hn hd hdn hk I).trans
  calc
    _ ≤ (Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ)))) +
        Real.exp ((n : ℝ) * smallSetEntropy a)) * Real.exp (-rowLoadRate * I.card) :=
      mul_le_mul_of_nonneg_right (add_le_add hEntropy0 hEntropy) (Real.exp_pos _).le
    _ = _ := by simp only [add_mul, ← Real.exp_add, sub_eq_add_neg, neg_mul]

theorem bernoulli_lly_row_load_failure_entropy {n d k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n) (I : Finset (Fin n)) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliLLYRowLoad d I k₂ k₃ sample} ≤
      2 * (Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ))) - rowLoadRate * I.card) +
        Real.exp ((n : ℝ) * smallSetEntropy a - rowLoadRate * I.card)) := by
  have hSubset : {sample : BernoulliSquareSample n | ¬BernoulliLLYRowLoad d I k₂ k₃ sample} ⊆
      {sample | ¬BernoulliSourceRowLoad d I k₂ sample} ∪
        {sample | ¬BernoulliSourceRowLoad d I k₃ sample} := by
    intro sample hSample
    exact _root_.not_and_or.mp hSample
  apply (measureReal_mono hSubset (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  simpa only [two_mul] using add_le_add
    (bernoulli_uniform_row_load_failure_entropy hn hd hdn hk₂ ha haOne hRank₂ I)
    (bernoulli_uniform_row_load_failure_entropy hn hd hdn hk₃ ha haOne hRank₃ I)

theorem bernoulli_lly_row_load_failure_absorbed {n d k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n) (I : Finset (Fin n))
    (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliLLYRowLoad d I k₂ k₃ sample} ≤
      Real.exp (-(rowLoadRate / 4) * n) := by
  have hRowScaled := mul_le_mul_of_nonneg_left hRows rowLoadRate_pos.le
  have hSmall0 := mul_le_mul_of_nonneg_left hEntropy0 (Nat.cast_nonneg (α := ℝ) n)
  have hSmall := mul_le_mul_of_nonneg_left hEntropy (Nat.cast_nonneg (α := ℝ) n)
  have hNRate : (0 : ℝ) ≤ rowLoadRate * n := mul_nonneg rowLoadRate_pos.le (Nat.cast_nonneg n)
  have hExp0 : Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ))) - rowLoadRate * I.card) ≤
      Real.exp (-(rowLoadRate / 2) * n) := Real.exp_le_exp.mpr (by nlinarith)
  have hExp : Real.exp ((n : ℝ) * smallSetEntropy a - rowLoadRate * I.card) ≤
      Real.exp (-(rowLoadRate / 2) * n) := Real.exp_le_exp.mpr (by nlinarith)
  apply (bernoulli_lly_row_load_failure_entropy hn hd hdn hk₂ hk₃ ha haOne hRank₂ hRank₃ I).trans
  calc
    _ ≤ 2 * (Real.exp (-(rowLoadRate / 2) * n) + Real.exp (-(rowLoadRate / 2) * n)) := by
      gcongr
    _ = 4 * Real.exp (-(rowLoadRate / 2) * n) := by ring
    _ = Real.exp (Real.log 4) * Real.exp (-(rowLoadRate / 2) * n) := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ = Real.exp (Real.log 4 - (rowLoadRate / 2) * n) := by
      rw [← Real.exp_add, sub_eq_add_neg, neg_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_bernoulli_lly_row_load_failure_uniform {C a : ℝ} (hC : 0 < C)
    (ha : 0 < a) (haOne : a ≤ 1) (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → d ≤ n →
      ∀ k₂ k₃ : ℕ, 0 < k₂ → 0 < k₃ → (k₂ : ℝ) ≤ a * n → (k₃ : ℝ) ≤ a * n →
        ∀ I : Finset (Fin n), (99 / 100 : ℝ) * n ≤ I.card →
          (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliLLYRowLoad d I k₂ k₃ sample} ≤
            Real.exp (-(rowLoadRate / 4) * n) := by
  have hDegree : ∀ᶠ d : ℕ in atTop, 0 < d ∧
      smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4 := by
    filter_upwards [eventually_gt_atTop 0, eventually_row_load_degree_entropy] with d hd hEntropy0
    exact ⟨hd, hEntropy0⟩
  have hDimension : ∀ᶠ n : ℕ in atTop, 4 * Real.log 4 / rowLoadRate ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [eventually_gt_atTop 0, eventually_degree_property_uniform hC hDegree, hDimension]
    with n hn hDegree hDimension
  intro d hLower hdn k₂ k₃ hk₂ hk₃ hRank₂ hRank₃ I hRows
  obtain ⟨hd, hEntropy0⟩ := hDegree d hLower
  apply bernoulli_lly_row_load_failure_absorbed hn hd hdn hk₂ hk₃ ha haOne hRank₂ hRank₃
    I hRows hEntropy0 hEntropy
  have h := (div_le_iff₀ rowLoadRate_pos).mp hDimension
  nlinarith only [h]

end CircularLaw
