import CircularLaw.BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Counting all small coordinate sets

The weighted powerset identity bounds the actual family of subsets of
size at most `k`, including `k=0`. For density `t`, its entropy is at
most `n*t*(1-log(t))`. This tends to zero with `t` and gives a uniform
positive small-density threshold for each prescribed positive rate.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def smallCoordinateSets (n k : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter (fun J => J.card ≤ k)

theorem mem_smallCoordinateSets {n k : ℕ} (J : Finset (Fin n)) :
    J ∈ smallCoordinateSets n k ↔ J.card ≤ k := by
  simp only [smallCoordinateSets, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and]

theorem smallCoordinateSets_weighted_bound {n k : ℕ} {t : ℝ} (ht : 0 ≤ t) (htOne : t ≤ 1) :
    ((smallCoordinateSets n k).card : ℝ) * t ^ k ≤ (1 + t) ^ n := by
  calc
    _ = ∑ _J ∈ smallCoordinateSets n k, t ^ k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ J ∈ smallCoordinateSets n k, t ^ J.card := by
      apply Finset.sum_le_sum
      intro J hJ
      exact pow_le_pow_of_le_one ht htOne ((mem_smallCoordinateSets J).mp hJ)
    _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset, t ^ J.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro J _ _
      exact pow_nonneg ht J.card
    _ = _ := by
      have h := Finset.prod_one_add (f := fun _ : Fin n => t) Finset.univ
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h.symm

def smallSetEntropy (t : ℝ) : ℝ := t - t * Real.log t

theorem smallSetEntropy_nonneg {t : ℝ} (ht : 0 < t) (htOne : t ≤ 1) :
    0 ≤ smallSetEntropy t := by
  have hLog := Real.log_nonpos ht.le htOne
  unfold smallSetEntropy
  nlinarith

theorem smallCoordinateSets_card_density {n k : ℕ} {t : ℝ} (ht : 0 < t) (htOne : t ≤ 1)
    (hSize : (k : ℝ) ≤ t * n) :
    ((smallCoordinateSets n k).card : ℝ) ≤ Real.exp ((n : ℝ) * smallSetEntropy t) := by
  have hExp : (1 + t) ^ n ≤ Real.exp ((n : ℝ) * t) := by
    calc
      _ ≤ (Real.exp t) ^ n := pow_le_pow_left₀ (by positivity)
        (by have h := Real.add_one_le_exp t; linarith) n
      _ = _ := by rw [← Real.exp_nat_mul]
  have hTerm := (smallCoordinateSets_weighted_bound ht.le htOne (n := n) (k := k)).trans hExp
  have hDiv := (le_div_iff₀ (pow_pos ht k)).mpr hTerm
  have hLog : Real.log t ≤ 0 := Real.log_nonpos ht.le htOne
  have hScaled := mul_le_mul_of_nonpos_right hSize hLog
  calc
    _ ≤ Real.exp ((n : ℝ) * t) / t ^ k := hDiv
    _ = Real.exp ((n : ℝ) * t - (k : ℝ) * Real.log t) := by
      rw [show t ^ k = Real.exp ((k : ℝ) * Real.log t) by
        rw [Real.exp_nat_mul, Real.exp_log ht]]
      exact (Real.exp_sub _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold smallSetEntropy
      nlinarith

theorem smallSetEntropy_continuous : Continuous smallSetEntropy :=
  continuous_id.sub Real.continuous_mul_log

theorem smallSetEntropy_zero : smallSetEntropy 0 = 0 := by
  simp only [smallSetEntropy, zero_mul, sub_zero]

theorem small_set_entropy_threshold {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t ≤ a → smallSetEntropy t ≤ c := by
  have hNear : ∀ᶠ t : ℝ in 𝓝 0, smallSetEntropy t < c := by
    have hLimit := smallSetEntropy_continuous.continuousAt.tendsto (x := (0 : ℝ))
    rw [smallSetEntropy_zero] at hLimit
    exact hLimit.eventually (gt_mem_nhds hc)
  obtain ⟨δ, hδ, hBall⟩ := Metric.eventually_nhds_iff.mp hNear
  refine ⟨min (δ / 2) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro t ht hta
  have htδ : t < δ := by have h := hta.trans (min_le_left _ _); linarith
  apply (hBall ?_).le
  simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using htδ

end CircularLaw
