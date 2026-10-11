import CircularLaw.BernoulliSubsetLowerTail
import CircularLaw.BernoulliPrincipalMinorLaw
import CircularLaw.AlmostConstantRanks

/-!
# Actual Bernoulli row loads and retained-row event counts

Markov's inequality bounds each large-load row event by one sixteenth.
The exact law on the retained rows gives the product-event upper tail.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def bernoulliRowLoad {n : ℕ} (row : Fin n → Bool) (J : Finset (Fin n)) : ℕ :=
  (bernoulliSupport row ∩ J).card

theorem bernoulli_row_load_eq_subset_count {n : ℕ}
    (row : Fin n → Bool) (J : Finset (Fin n)) :
    (bernoulliRowLoad row J : ℝ) = bernoulliSubsetCount J row := by
  have hInter : bernoulliSupport row ∩ J = J.filter (fun j => row j = true) := by
    ext j
    simp [bernoulliSupport, and_comm]
  rw [bernoulliRowLoad, hInter, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, bernoulliSubsetCount]
  apply Finset.sum_congr rfl
  intro j _
  cases row j <;> simp

theorem bernoulli_row_load_integral {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (J : Finset (Fin n)) :
    (∫ row, (bernoulliRowLoad row J : ℝ) ∂bernoulliCubeLaw (Fin n)
      (rowBernoulliParameter n d) (rowBernoulliParameter_le_one hn hdn)) =
        (d : ℝ) * J.card / n := by
  simp_rw [bernoulli_row_load_eq_subset_count]
  rw [bernoulli_subset_count_integral, rowBernoulliParameter_coe]
  ring

theorem bernoulli_small_set_row_load_probability {n d : ℕ}
    (hn : 0 < n) (hdn : d ≤ n)
    (J : Finset (Fin n)) (hJ : J.card ≤ almostConstantRank n d) :
    (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one hn hdn)).real
        {row | (1 : ℝ) ≤ bernoulliRowLoad row J} ≤ 1 / 16 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMark := finite_measure_event_markov
    (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d) (rowBernoulliParameter_le_one hn hdn))
    (fun row => (1 : ℝ) ≤ bernoulliRowLoad row J) (fun row => (bernoulliRowLoad row J : ℝ))
    (by norm_num : (0 : ℝ) < 1) (fun row => Nat.cast_nonneg _) (fun _ h => h)
  rw [bernoulli_row_load_integral hn hdn J, div_one] at hMark
  apply hMark.trans
  apply (div_le_iff₀ hnR).mpr
  have hFloor := Nat.div_mul_le_self n (16 * d)
  have hSmall : 16 * d * J.card ≤ n := by
    change (n / (16 * d)) * (16 * d) ≤ n at hFloor
    change J.card ≤ n / (16 * d) at hJ
    nlinarith
  have hReal : (16 : ℝ) * d * J.card ≤ n := by exact_mod_cast hSmall
  nlinarith

theorem bernoulli_large_set_row_load_probability {n d k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hk : 0 < k)
    (J : Finset (Fin n)) (hJ : J.card ≤ k) :
    (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one hn hdn)).real
        {row | 16 * (k : ℝ) * d / n ≤ bernoulliRowLoad row J} ≤ 1 / 16 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hThreshold : (0 : ℝ) < 16 * (k : ℝ) * d / n := by positivity
  have hMark := finite_measure_event_markov
    (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d) (rowBernoulliParameter_le_one hn hdn))
    (fun row => 16 * (k : ℝ) * d / n ≤ bernoulliRowLoad row J)
    (fun row => (bernoulliRowLoad row J : ℝ)) hThreshold
    (fun row => Nat.cast_nonneg _) (fun _ h => h)
  rw [bernoulli_row_load_integral hn hdn J] at hMark
  apply hMark.trans
  apply (div_le_iff₀ hThreshold).mpr
  have hJReal : (J.card : ℝ) ≤ k := by exact_mod_cast hJ
  calc
    (d : ℝ) * J.card / n ≤ (d : ℝ) * k / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJReal hdR.le) hnR.le
    _ = (1 / 16 : ℝ) * (16 * (k : ℝ) * d / n) := by ring

def bernoulliRetainedEventCount {n : ℕ} (I : Finset (Fin n)) (E : (Fin n → Bool) → Prop)
    (sample : BernoulliSquareSample n) : ℕ :=
  (I.filter (fun i => E (fun j => sample (i, j)))).card

theorem bernoulli_retained_event_count_eq_coordinates {n : ℕ} (I : Finset (Fin n))
    (E : (Fin n → Bool) → Prop) (sample : BernoulliSquareSample n) :
    bernoulliRetainedEventCount I E sample =
      coordinateEventCount (fun _ : I => E) (fun i j => sample (i.val, j)) := by
  unfold bernoulliRetainedEventCount coordinateEventCount
  symm
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨i.property, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hEq
    exact Subtype.ext hEq
  · intro i hi
    exact ⟨⟨i, (Finset.mem_filter.mp hi).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, rfl⟩

theorem bernoulli_retained_many_events_failure {n : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (I : Finset (Fin n)) (E : (Fin n → Bool) → Prop)
    (hSmall : (bernoulliCubeLaw (Fin n) p hp).real {row | E row} ≤ 1 / 16) :
    (bernoulliSquareMatrixLaw n p hp).real {sample |
      (I.card : ℝ) / 8 < bernoulliRetainedEventCount I E sample} ≤
        Real.exp (-rowLoadRate * I.card) := by
  let e : I × Fin n ↪ Fin n × Fin n :=
    ⟨fun a => (a.1.val, a.2), by
      intro a b h
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst h
      · exact congrArg (fun x : Fin n × Fin n => x.2) h⟩
  have hRestrict := finite_law_event_real
    (measurable_of_countable (fun x : BernoulliSquareSample n => fun a => x (e a)))
    (bernoulli_cube_law_restrict p hp e)
    (fun x : I × Fin n → Bool =>
      (I.card : ℝ) / 8 < coordinateEventCount (fun _ : I => E) (Function.curry x))
  have hCurry := finite_law_event_real
    (bernoulli_row_product_measure_preserving (ρ := I) (ι := Fin n) p hp).measurable
    (bernoulli_row_product_map (ρ := I) (ι := Fin n) p hp)
    (fun rows : I → Fin n → Bool => (I.card : ℝ) / 8 < coordinateEventCount (fun _ : I => E) rows)
  have hProb := finite_product_many_events_sixteenth
    (fun _ : I => bernoulliCubeLaw (Fin n) p hp) (fun _ : I => E) (fun _ => hSmall)
  simp only [Fintype.card_coe] at hProb
  simpa only [bernoulliSquareMatrixLaw, bernoulli_retained_event_count_eq_coordinates,
    Function.curry, e, Function.Embedding.coeFn_mk] using
    hRestrict.trans hCurry |>.le.trans hProb

end CircularLaw
