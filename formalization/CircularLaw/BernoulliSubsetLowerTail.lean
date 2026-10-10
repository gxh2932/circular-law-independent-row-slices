import CircularLaw.BernoulliSubsetCountLaplace
import CircularLaw.FiniteProductEventUpperTail
import CircularLaw.RowSliceEdgeLowerTail
import CircularLaw.BernoulliRowProductLaw
import CircularLaw.FiniteLawTransport
import CircularLaw.BernoulliSquareMatrixLaw

/-!
# Bernoulli subset means, lower tails and actual row degrees

The row degrees keep the original independent-entry parameter. Their
simultaneous lower bound is a union bound over the actual matrix rows.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_subset_count_integral {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) :
    (∫ x, bernoulliSubsetCount S x ∂bernoulliCubeLaw ι p hp) = (S.card : ℝ) * p := by
  unfold bernoulliSubsetCount
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  have hEach (i : ι) :
      (∫ x, (cond (x i) 1 0 : ℝ) ∂bernoulliCubeLaw ι p hp) = (p : ℝ) := by
    rw [bernoulliCubeLaw_coordinate_integral p hp i (fun b => (cond b 1 0 : ℝ)),
      bernoulliCoordinateLaw_integral]
    simp
  simp only [hEach, Finset.sum_const, nsmul_eq_mul]

theorem bernoulli_subset_count_lower_laplace_tail {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    (bernoulliCubeLaw ι p hp).real {x | bernoulliSubsetCount S x ≤ u} ≤
      Real.exp ((S.card : ℝ) * p * (Real.exp (-t) - 1) + t * u) := by
  have hMark := finite_measure_event_markov (bernoulliCubeLaw ι p hp)
    (fun x => bernoulliSubsetCount S x ≤ u)
    (fun x => Real.exp (-t * bernoulliSubsetCount S x)) (Real.exp_pos (-t * u))
    (fun _ => (Real.exp_pos _).le)
    (fun _ hx => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr ht)))
  apply hMark.trans
  apply (div_le_div_of_nonneg_right (bernoulli_subset_count_exponential_integral_le p hp S (-t))
    (Real.exp_pos (-t * u)).le).trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

theorem bernoulli_subset_count_chernoff_lower_tail {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) {θ : ℝ} (hθ : 0 ≤ θ) :
    (bernoulliCubeLaw ι p hp).real
        {x | bernoulliSubsetCount S x ≤ (1 - θ) * ((S.card : ℝ) * p)} ≤
      Real.exp (-((S.card : ℝ) * p) * θ ^ 2 / 2) := by
  apply (bernoulli_subset_count_lower_laplace_tail p hp S hθ _).trans
  apply Real.exp_le_exp.mpr
  have hTaylor := mul_le_mul_of_nonneg_left (real_exp_neg_le_quadratic hθ)
    (mul_nonneg (Nat.cast_nonneg S.card) p.coe_nonneg)
  nlinarith only [hTaylor]

def BernoulliRowDegreeLowerBound {n : ℕ} (b : ℝ) (sample : BernoulliSquareSample n) : Prop :=
  ∀ i : Fin n, b ≤ bernoulliSubsetCount Finset.univ (fun j => sample (i, j))

theorem bernoulli_row_degree_lower_failure {n : ℕ} (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliSquareMatrixLaw n p hp).real {sample |
      ¬BernoulliRowDegreeLowerBound (9 * ((n : ℝ) * p) / 10) sample} ≤
      (n : ℝ) * Real.exp (-((n : ℝ) * p) / 200) := by
  let E := fun i : Fin n => {sample : BernoulliSquareSample n |
    bernoulliSubsetCount Finset.univ (fun j => sample (i, j)) ≤ 9 * ((n : ℝ) * p) / 10}
  have hEach (i : Fin n) :
      (bernoulliSquareMatrixLaw n p hp).real (E i) ≤ Real.exp (-((n : ℝ) * p) / 200) := by
    have hLaw := finite_law_event_real
      (bernoulli_row_coordinate_measure_preserving (ρ := Fin n) (ι := Fin n) p hp i).measurable
      (bernoulli_row_coordinate_measure_preserving (ρ := Fin n) (ι := Fin n) p hp i).map_eq
      (fun row => bernoulliSubsetCount Finset.univ row ≤ 9 * ((n : ℝ) * p) / 10)
    change (bernoulliCubeLaw (Fin n × Fin n) p hp).real (E i) ≤ _
    rw [hLaw]
    have h := bernoulli_subset_count_chernoff_lower_tail p hp (Finset.univ : Finset (Fin n))
      (by norm_num : (0 : ℝ) ≤ 1 / 10)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    have hThreshold : (1 - (1 / 10 : ℝ)) * ((n : ℝ) * p) = 9 * ((n : ℝ) * p) / 10 := by ring
    have hExponent : -((n : ℝ) * p) * (1 / 10 : ℝ) ^ 2 / 2 = -((n : ℝ) * p) / 200 := by ring
    simpa only [hThreshold, hExponent] using h
  have hSubset : {sample : BernoulliSquareSample n |
      ¬BernoulliRowDegreeLowerBound (9 * ((n : ℝ) * p) / 10) sample} ⊆ ⋃ i, E i := by
    intro sample hSample
    obtain ⟨i, hi⟩ := not_forall.mp hSample
    exact Set.mem_iUnion.mpr ⟨i, (lt_of_not_ge hi).le⟩
  apply (measureReal_mono hSubset (h₂ := by finiteness)).trans
  apply (measureReal_iUnion_fintype_le E).trans
  apply (Finset.sum_le_sum (fun i _ => hEach i)).trans_eq
  simp

theorem sparse_bernoulli_row_degree_lower_failure {n d : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ¬BernoulliRowDegreeLowerBound (9 * (d : ℝ) / 10) sample} ≤
      (n : ℝ) * Real.exp (-(d : ℝ) / 200) := by
  rw [sparseBernoulliMatrixLaw_eq hn hdn]
  have hDegree : (n : ℝ) * rowBernoulliParameter n d = d := by
    rw [rowBernoulliParameter_coe]
    field_simp
  simpa only [hDegree] using bernoulli_row_degree_lower_failure (n := n)
    (rowBernoulliParameter n d) (rowBernoulliParameter_le_one hn hdn)

end CircularLaw
