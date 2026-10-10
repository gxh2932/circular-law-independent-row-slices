import CircularLaw.RowLoadProbability
import CircularLaw.SmallSetEntropy

/-!
# The actual uniform row-load event

The two conditions are the source row counts for all sets of size at
most `n0` and `n3`. Their failure is bounded over the actual families
of coordinate sets, under the full matrix law.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem uniformProbability_or_le {α : Type*} [Fintype α] (E F : α → Prop) :
    uniformProbability (fun x => E x ∨ F x) ≤ uniformProbability E + uniformProbability F := by
  have hPoint (x : α) : (if E x ∨ F x then (1 : ℝ) else 0) ≤
      (if E x then (1 : ℝ) else 0) + (if F x then (1 : ℝ) else 0) := by
    by_cases hE : E x <;> by_cases hF : F x <;> simp only [hE, hF, or_true, true_or,
      false_or, if_true, if_false] <;> norm_num
  have h := finiteMean_mono hPoint
  simpa only [finiteMean_indicator, finiteMean_add] using h

def SourceRowLoad {n d : ℕ} (I : Finset (Fin n)) (k : ℕ) (rows : RowSliceMatrix n d) : Prop :=
  (∀ J : Finset (Fin n), J.card ≤ almostConstantRank n d →
    (retainedEventCount I (fun S => (1 : ℝ) ≤ rowLoad S J) rows : ℝ) ≤ (I.card : ℝ) / 8) ∧
  (∀ J : Finset (Fin n), J.card ≤ k →
    (retainedEventCount I (fun S => 16 * (k : ℝ) * d / n ≤ rowLoad S J) rows : ℝ) ≤ (I.card : ℝ) / 8)

theorem uniform_row_load_failure_counting {n d k : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hk : 0 < k) (I : Finset (Fin n)) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceRowLoad I k rows) ≤
      (((smallCoordinateSets n (almostConstantRank n d)).card : ℝ) +
        (smallCoordinateSets n k).card) * Real.exp (-rowLoadRate * I.card) := by
  let E0 := fun rows : RowSliceMatrix n d => ∃ J ∈ smallCoordinateSets n (almostConstantRank n d),
    (I.card : ℝ) / 8 < retainedEventCount I (fun S => (1 : ℝ) ≤ rowLoad S J) rows
  let E3 := fun rows : RowSliceMatrix n d => ∃ J ∈ smallCoordinateSets n k,
    (I.card : ℝ) / 8 < retainedEventCount I (fun S => 16 * (k : ℝ) * d / n ≤ rowLoad S J) rows
  have hEvent : ∀ rows : RowSliceMatrix n d, ¬SourceRowLoad I k rows → E0 rows ∨ E3 rows := by
    intro rows hBad
    rcases _root_.not_and_or.mp hBad with hBad0 | hBad3
    · push_neg at hBad0
      obtain ⟨J, hJ, hCount⟩ := hBad0
      exact Or.inl ⟨J, (mem_smallCoordinateSets J).mpr hJ, hCount⟩
    · push_neg at hBad3
      obtain ⟨J, hJ, hCount⟩ := hBad3
      exact Or.inr ⟨J, (mem_smallCoordinateSets J).mpr hJ, hCount⟩
  have hBound0 : uniformProbability E0 ≤
      ((smallCoordinateSets n (almostConstantRank n d)).card : ℝ) * Real.exp (-rowLoadRate * I.card) := by
    apply (uniformProbability_finset_exists_le (smallCoordinateSets n (almostConstantRank n d))
      (fun J rows => (I.card : ℝ) / 8 < retainedEventCount I (fun S => (1 : ℝ) ≤ rowLoad S J) rows)).trans
    calc
      _ ≤ ∑ _J ∈ smallCoordinateSets n (almostConstantRank n d), Real.exp (-rowLoadRate * I.card) := by
        apply Finset.sum_le_sum
        intro J hJ
        exact retained_many_events_failure hdn I (fun S => (1 : ℝ) ≤ rowLoad S J)
          (small_set_row_load_probability hd hdn J ((mem_smallCoordinateSets J).mp hJ))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hBound3 : uniformProbability E3 ≤
      ((smallCoordinateSets n k).card : ℝ) * Real.exp (-rowLoadRate * I.card) := by
    apply (uniformProbability_finset_exists_le (smallCoordinateSets n k)
      (fun J rows => (I.card : ℝ) / 8 < retainedEventCount I
        (fun S => 16 * (k : ℝ) * d / n ≤ rowLoad S J) rows)).trans
    calc
      _ ≤ ∑ _J ∈ smallCoordinateSets n k, Real.exp (-rowLoadRate * I.card) := by
        apply Finset.sum_le_sum
        intro J hJ
        exact retained_many_events_failure hdn I (fun S => 16 * (k : ℝ) * d / n ≤ rowLoad S J)
          (large_set_row_load_probability hd hdn hk J ((mem_smallCoordinateSets J).mp hJ))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  apply (uniformProbability_mono hEvent).trans
  apply (uniformProbability_or_le E0 E3).trans
  have h := add_le_add hBound0 hBound3
  simpa only [add_mul] using h

theorem uniform_row_load_failure_entropy {n d : ℕ} {a₃ : ℝ} (hd : 0 < d) (hdn : d ≤ n)
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hk : 0 < thirdSteepScale n a₃) (I : Finset (Fin n)) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceRowLoad I (thirdSteepScale n a₃) rows) ≤
      Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ))) - rowLoadRate * I.card) +
      Real.exp ((n : ℝ) * smallSetEntropy a₃ - rowLoadRate * I.card) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht : (0 : ℝ) < 1 / (16 * (d : ℝ)) := by positivity
  have htOne : 1 / (16 * (d : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mpr
    linarith
  have hSize0 : (almostConstantRank n d : ℝ) ≤ (1 / (16 * (d : ℝ))) * n := by
    convert almostConstantRank_upper (n := n) hd using 1
    ring
  have hSize3 : (thirdSteepScale n a₃ : ℝ) ≤ a₃ * n :=
    Nat.floor_le (by positivity : (0 : ℝ) ≤ a₃ * n)
  have hEntropy0 := smallCoordinateSets_card_density ht htOne hSize0
  have hEntropy3 := smallCoordinateSets_card_density ha haOne hSize3
  apply (uniform_row_load_failure_counting hd hdn hk I).trans
  calc
    _ ≤ (Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ)))) +
        Real.exp ((n : ℝ) * smallSetEntropy a₃)) * Real.exp (-rowLoadRate * I.card) :=
      mul_le_mul_of_nonneg_right (add_le_add hEntropy0 hEntropy3) (Real.exp_pos _).le
    _ = _ := by simp only [add_mul, ← Real.exp_add, sub_eq_add_neg, neg_mul]

end CircularLaw
