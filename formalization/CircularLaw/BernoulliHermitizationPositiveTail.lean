import CircularLaw.HermitizationPositiveTailRates
import CircularLaw.SingularBottomScaling
import CircularLaw.HermitizationPrefixComparison

/-!
# The actual raw Bernoulli positive logarithmic tail

The raw comparator's energy is d times the normalized energy. Its checked
tight second moment and the deterministic logarithmic energy estimate
give vanishing top positive logarithms at both rounded source cutoffs.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix BigOperators Topology

namespace CircularLaw

def squareTopPositiveLog {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) : ℝ :=
  (∑ j : Fin (min r n), max (Real.log (orderedSquareSingularValues A (Fin.castLE (Nat.min_le_right r n) j))) 0) / n

theorem square_top_positive_log_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) :
    0 ≤ squareTopPositiveLog A r :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => le_max_right _ _)) (Nat.cast_nonneg n)

theorem square_top_positive_log_eq_of_le {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hrn : r ≤ n) :
    squareTopPositiveLog A r =
      (∑ j : Fin r, max (Real.log (orderedSquareSingularValues A (Fin.castLE hrn j))) 0) / n := by
  have h : ∀ (m : ℕ) (hm : m ≤ n), m = r →
      (∑ j : Fin m, max (Real.log (orderedSquareSingularValues A (Fin.castLE hm j))) 0) / n =
        (∑ j : Fin r, max (Real.log (orderedSquareSingularValues A (Fin.castLE hrn j))) 0) / n := by
    intro m hm hmr
    subst m
    rfl
  exact h (min r n) (Nat.min_le_right r n) (Nat.min_eq_left hrn)

theorem square_top_positive_hermitization_energy_bound {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    {a C : ℝ} (ha : 0 < a) (haOne : a ≤ 1) (hC : 0 ≤ C)
    (hEnergy : squareMatrixEnergy A ≤ C * n * d) :
    squareTopPositiveLog A (hermitizationDeletionCount n d a) ≤
      (Real.log (1 + C) + (1 + a) * Real.log d) / Real.rpow (d : ℝ) a := by
  rw [square_top_positive_log_eq_of_le A (hermitizationDeletionCount_le_dimension (by omega) ha.le)]
  exact square_positive_log_hermitization_deletion_bound A hn hd hdn ha haOne hC hEnergy

theorem bernoulli_raw_shift_energy_eq {n d : ℕ} (hd : 0 < d) (z : ℂ)
    (x : BernoulliSquareSample n) :
    squareMatrixEnergy (bernoulliSquareMatrix x - (z * (Real.sqrt (d : ℝ) : ℂ)) • 1) =
      (d : ℝ) * squareMatrixEnergy (normalizedShiftedBernoulliMatrix d z x) := by
  rw [bernoulli_raw_shift_eq_sqrt_smul hd, squareMatrixEnergy_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg d)]

theorem bernoulli_raw_shift_energy_bound_of_second_moment {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (z : ℂ) (x : BernoulliSquareSample n)
    {C : ℝ} (hMoment : bernoulliSingularSecondMoment d z x ≤ C) :
    squareMatrixEnergy (bernoulliSquareMatrix x - (z * (Real.sqrt (d : ℝ) : ℂ)) • 1) ≤ C * n * d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [bernoulliSingularSecondMoment_eq] at hMoment
  have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hnR).mp hMoment) (Nat.cast_nonneg d)
  rw [bernoulli_raw_shift_energy_eq hd]
  nlinarith only [h]

theorem bernoulli_raw_top_positive_log_converges (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => squareTopPositiveLog
        (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1)
        (hermitizationDeletionCount n (d n) a)) 0 := by
  apply varying_probability_of_error_bound
  intro ε hε δ hδ
  obtain ⟨C, hC, hTight⟩ := bernoulli_second_moment_bounded_in_probability d z hDegree hSparse δ hδ
  have hSmall := (hermitization_positive_log_budget_tendsto_zero d hDegree ha C).eventually (gt_mem_nhds hε)
  filter_upwards [hTight, hSmall, eventually_valid_bernoulli_degrees hDegree hSparse] with n hT hS hd
  apply lt_of_le_of_lt _ hT
  apply measureReal_mono (h₂ := by finiteness)
  intro x hx
  by_contra hNot
  have hMoment : bernoulliSingularSecondMoment (d n) z x ≤ C :=
    (le_abs_self _).trans (le_of_not_gt hNot)
  have hn : 0 < n := lt_of_lt_of_le hd.1 hd.2
  have hEnergy := bernoulli_raw_shift_energy_bound_of_second_moment hn hd.1 z x hMoment
  have hBound := square_top_positive_hermitization_energy_bound _ hn hd.1 hd.2 ha haOne hC.le hEnergy
  simp only [Set.mem_setOf_eq, sub_zero,
    abs_of_nonneg (square_top_positive_log_nonneg _ _)] at hx
  exact (not_lt_of_ge (hBound.trans hS.le)) hx

end CircularLaw
