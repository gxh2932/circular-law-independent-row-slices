import CircularLaw.BernoulliRowLoadProbability
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Actual Bernoulli row-degree upper tails

Every row has expected degree np. The simultaneous bound at 2np costs
only the dimension times a fixed exponential in that expected degree.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def bernoulliDegreeUpperRate : ℝ := 2 * Real.log 2 - 1

theorem bernoulli_degree_upper_rate_pos : 0 < bernoulliDegreeUpperRate := by
  unfold bernoulliDegreeUpperRate
  linarith [Real.log_two_gt_d9]

def BernoulliRowDegreeUpperBound {n : ℕ} (b : ℝ) (sample : BernoulliSquareSample n) : Prop :=
  ∀ i : Fin n, bernoulliSubsetCount Finset.univ (fun j => sample (i, j)) ≤ b

theorem bernoulli_row_degree_upper_failure {n : ℕ} (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliSquareMatrixLaw n p hp).real {sample |
      ¬BernoulliRowDegreeUpperBound (2 * ((n : ℝ) * p)) sample} ≤
      (n : ℝ) * Real.exp (-bernoulliDegreeUpperRate * ((n : ℝ) * p)) := by
  let E := fun i : Fin n => {sample : BernoulliSquareSample n |
    2 * ((n : ℝ) * p) ≤ bernoulliSubsetCount Finset.univ (fun j => sample (i, j))}
  have hEach (i : Fin n) :
      (bernoulliSquareMatrixLaw n p hp).real (E i) ≤
        Real.exp (-bernoulliDegreeUpperRate * ((n : ℝ) * p)) := by
    have hLaw := finite_law_event_real
      (bernoulli_row_coordinate_measure_preserving (ρ := Fin n) (ι := Fin n) p hp i).measurable
      (bernoulli_row_coordinate_measure_preserving (ρ := Fin n) (ι := Fin n) p hp i).map_eq
      (fun row => 2 * ((n : ℝ) * p) ≤ bernoulliSubsetCount Finset.univ row)
    change (bernoulliCubeLaw (Fin n × Fin n) p hp).real (E i) ≤ _
    rw [hLaw]
    have h := bernoulli_subset_count_upper_tail p hp (Finset.univ : Finset (Fin n))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le (2 * ((n : ℝ) * p))
    simp only [Finset.card_univ, Fintype.card_fin,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    apply h.trans_eq
    congr 1
    unfold bernoulliDegreeUpperRate
    ring
  have hSubset : {sample : BernoulliSquareSample n |
      ¬BernoulliRowDegreeUpperBound (2 * ((n : ℝ) * p)) sample} ⊆ ⋃ i, E i := by
    intro sample hSample
    obtain ⟨i, hi⟩ := not_forall.mp hSample
    exact Set.mem_iUnion.mpr ⟨i, (lt_of_not_ge hi).le⟩
  apply (measureReal_mono hSubset (h₂ := by finiteness)).trans
  apply (measureReal_iUnion_fintype_le E).trans
  apply (Finset.sum_le_sum (fun i _ => hEach i)).trans_eq
  simp

theorem sparse_bernoulli_row_degree_upper_failure {n d : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ¬BernoulliRowDegreeUpperBound (2 * (d : ℝ)) sample} ≤
      (n : ℝ) * Real.exp (-bernoulliDegreeUpperRate * d) := by
  rw [sparseBernoulliMatrixLaw_eq hn hdn]
  have hDegree : (n : ℝ) * rowBernoulliParameter n d = d := by
    rw [rowBernoulliParameter_coe]
    field_simp
  simpa only [hDegree] using bernoulli_row_degree_upper_failure (n := n)
    (rowBernoulliParameter n d) (rowBernoulliParameter_le_one hn hdn)

end CircularLaw
