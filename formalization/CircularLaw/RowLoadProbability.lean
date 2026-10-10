import CircularLaw.IndependentUpperTail
import CircularLaw.AlmostConstantRanks

/-!
# Exact row loads and retained-row upper tails

The expectation uses only the actual coordinate marginals of a fixed
size support. Markov bounds each large-load row event by `1/16`;
independence across the retained rows supplies the exponential tail.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rowLoad {n d : ℕ} (S : RowSlice n d) (J : Finset (Fin n)) : ℕ := (S.val ∩ J).card

theorem rowLoad_cast_sum {n d : ℕ} (S : RowSlice n d) (J : Finset (Fin n)) :
    (rowLoad S J : ℝ) = ∑ j ∈ J, if j ∈ S.val then (1 : ℝ) else 0 := by
  have hInter : S.val ∩ J = J.filter (fun j => j ∈ S.val) := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, and_comm]
  unfold rowLoad
  rw [hInter]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem rowLoad_expectation {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (J : Finset (Fin n)) :
    finiteMean (fun S : RowSlice n d => (rowLoad S J : ℝ)) = (d : ℝ) * J.card / n := by
  simp_rw [rowLoad_cast_sum]
  rw [finiteMean_finset_sum]
  simp only [finiteMean_indicator, row_coordinate_probability hd hdn, Finset.sum_const, nsmul_eq_mul]
  ring

theorem small_set_row_load_probability {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (J : Finset (Fin n)) (hJ : J.card ≤ almostConstantRank n d) :
    uniformProbability (fun S : RowSlice n d => (1 : ℝ) ≤ rowLoad S J) ≤ 1 / 16 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le hd hdn
  have hMark := finite_uniform_markov (fun S : RowSlice n d => (1 : ℝ) ≤ rowLoad S J)
    (fun S => (rowLoad S J : ℝ)) (by norm_num : (0 : ℝ) < 1)
    (fun S => Nat.cast_nonneg (rowLoad S J)) (fun _ h => h)
  rw [rowLoad_expectation hd hdn J, div_one] at hMark
  apply hMark.trans
  apply (div_le_iff₀ hnR).mpr
  have hFloor := Nat.div_mul_le_self n (16 * d)
  have hSmall : 16 * d * J.card ≤ n := by
    change (n / (16 * d)) * (16 * d) ≤ n at hFloor
    change J.card ≤ n / (16 * d) at hJ
    nlinarith
  have hReal : (16 : ℝ) * d * J.card ≤ n := by exact_mod_cast hSmall
  nlinarith

theorem large_set_row_load_probability {n d k : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hk : 0 < k) (J : Finset (Fin n)) (hJ : J.card ≤ k) :
    uniformProbability (fun S : RowSlice n d => 16 * (k : ℝ) * d / n ≤ rowLoad S J) ≤ 1 / 16 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le hd hdn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hThreshold : (0 : ℝ) < 16 * (k : ℝ) * d / n := by positivity
  have hMark := finite_uniform_markov
    (fun S : RowSlice n d => 16 * (k : ℝ) * d / n ≤ rowLoad S J)
    (fun S => (rowLoad S J : ℝ)) hThreshold
    (fun S => Nat.cast_nonneg (rowLoad S J)) (fun _ h => h)
  rw [rowLoad_expectation hd hdn J] at hMark
  apply hMark.trans
  apply (div_le_iff₀ hThreshold).mpr
  have hJReal : (J.card : ℝ) ≤ k := by exact_mod_cast hJ
  calc
    (d : ℝ) * J.card / n ≤ (d : ℝ) * k / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJReal hdR.le) hnR.le
    _ = (1 / 16 : ℝ) * (16 * (k : ℝ) * d / n) := by ring

def retainedEventCount {n d : ℕ} (I : Finset (Fin n)) (E : RowSlice n d → Prop)
    (rows : RowSliceMatrix n d) : ℕ :=
  coordinateEventCount (fun _ : I => E) (fun i => rows i.val)

theorem retainedEventCount_eq_filter {n d : ℕ} (I : Finset (Fin n)) (E : RowSlice n d → Prop)
    (rows : RowSliceMatrix n d) :
    retainedEventCount I E rows = (I.filter (fun i => E (rows i))).card := by
  unfold retainedEventCount coordinateEventCount
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨i.property, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hEq
    exact Subtype.ext hEq
  · intro i hi
    refine ⟨⟨i, (Finset.mem_filter.mp hi).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩

theorem retained_many_events_failure {n d : ℕ} (hdn : d ≤ n) (I : Finset (Fin n))
    (E : RowSlice n d → Prop) (hSmall : uniformProbability E ≤ 1 / 16) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      (I.card : ℝ) / 8 < retainedEventCount I E rows) ≤ Real.exp (-rowLoadRate * I.card) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  change uniformProbability (fun rows : RowSliceMatrix n d =>
    (I.card : ℝ) / 8 < coordinateEventCount (fun _ : I => E) (fun i => rows i.val)) ≤ _
  rw [uniformProbability_pi_restrict (α := fun _ : Fin n => RowSlice n d) I
    (fun retained => (I.card : ℝ) / 8 < coordinateEventCount (fun _ : I => E) retained)]
  simpa only [Fintype.card_coe] using
    independent_many_events_sixteenth (fun _ : I => E) (fun _ => hSmall)

end CircularLaw
