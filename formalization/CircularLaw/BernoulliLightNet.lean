import CircularLaw.BernoulliLightConcentration
import CircularLaw.RowSliceLightNet

/-!
# Simultaneous centered Bernoulli light estimates on two full unit nets

The literal pair cardinality is absorbed by the signed light tail.
Both nets cover the entire real unit ball.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def BernoulliLightNetBound {n : ℕ} (d : ℕ) (B : ℝ) (sample : BernoulliSquareSample n) : Prop :=
  ∀ x ∈ normLatticeNet n, ∀ y ∈ normLatticeNet n,
    |centeredBernoulliMatrixSum d (lightMatrixWeights (fun i j => x i * y j)
      (Real.sqrt (9 * (d : ℝ)) / n)) sample| ≤ B * Real.sqrt (9 * (d : ℝ))

theorem bernoulli_light_net_failure_exponential {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliLightNetBound d B sample} ≤
      4 * Real.exp ((14 - B / 32) * n) := by
  let μ := sparseBernoulliMatrixLaw n d
  let P := (normLatticeNet n).product (normLatticeNet n)
  let bad := fun (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (sample : BernoulliSquareSample n) => B * Real.sqrt (9 * (d : ℝ)) ≤
      |centeredBernoulliMatrixSum d (lightMatrixWeights (fun i j => p.1 i * p.2 j)
        (Real.sqrt (9 * (d : ℝ)) / n)) sample|
  have hCover : {sample : BernoulliSquareSample n | ¬BernoulliLightNetBound d B sample} ⊆
      {sample | ∃ p ∈ P, bad p sample} := by
    intro sample hFail
    unfold BernoulliLightNetBound at hFail
    push_neg at hFail
    obtain ⟨x, hx, y, hy, hBad⟩ := hFail
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, hBad.le⟩
  have hSingle : ∀ p ∈ P, μ.real {sample | bad p sample} ≤ 4 * Real.exp (-B * n / 32) := by
    intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    have hxNorm := normLatticeNet_norm_bound hn hx
    have hyNorm := normLatticeNet_norm_bound hn hy
    have hxMass : (∑ i, (p.1 i) ^ 2) ≤ 1 := by
      rw [← real_euclidean_norm_sq]
      nlinarith [norm_nonneg p.1]
    have hyMass : (∑ j, (p.2 j) ^ 2) ≤ 1 := by
      rw [← real_euclidean_norm_sq]
      nlinarith [norm_nonneg p.2]
    have hMass : (∑ i, ∑ j, (p.1 i * p.2 j) ^ 2) ≤ 1 := by
      rw [rankOneWeights_squared_sum]
      have hyNonneg : 0 ≤ ∑ j, (p.2 j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      simpa only [one_mul] using mul_le_mul hxMass hyMass hyNonneg (by norm_num : (0 : ℝ) ≤ 1)
    exact bernoulli_source_light_centered_probability hn hdn (by positivity : 0 < 9 * (d : ℝ))
      (by nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]) hB _ hMass
  have hCard : (P.card : ℝ) ≤ Real.exp (14 * (n : ℝ)) := by
    have hNet := norm_lattice_card_exponential (normLatticeNet n) (normLatticeNet_card_le n)
    calc
      _ = ((normLatticeNet n).card : ℝ) * (normLatticeNet n).card := by
        exact_mod_cast Finset.card_product (normLatticeNet n) (normLatticeNet n)
      _ ≤ Real.exp (7 * (n : ℝ)) * Real.exp (7 * (n : ℝ)) :=
        mul_le_mul hNet hNet (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (measureReal_mono (μ := μ) hCover (h₂ := by finiteness)).trans
  apply (finite_measure_finset_exists_le μ P bad).trans
  calc
    _ ≤ ∑ _p ∈ P, 4 * Real.exp (-B * n / 32) := Finset.sum_le_sum hSingle
    _ = (P.card : ℝ) * (4 * Real.exp (-B * n / 32)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (14 * (n : ℝ)) * (4 * Real.exp (-B * n / 32)) :=
      mul_le_mul_of_nonneg_right hCard (by positivity)
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem bernoulli_light_net_failure_polynomial {n d : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) {A : ℝ} (hA : 0 ≤ A) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliLightNetBound d (32 * (A + 20)) sample} ≤
      (n : ℝ) ^ (-(A + 1)) := by
  have hnPos : 0 < n := by omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hB : 1 ≤ 32 * (A + 20) := by linarith only [hA]
  have hFour : (4 : ℝ) ≤ Real.exp (2 * (n : ℝ)) := by
    have hTwo : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      norm_num at h
      exact h.le
    calc
      _ = (2 : ℝ) * 2 := by ring
      _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul hTwo hTwo (by norm_num) (Real.exp_nonneg _)
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hnOne])
  apply (bernoulli_light_net_failure_exponential hnPos hd hdn hB).trans
  calc
    _ = 4 * Real.exp (-(A + 6) * n) := by congr 2; ring
    _ ≤ Real.exp (2 * (n : ℝ)) * Real.exp (-(A + 6) * n) :=
      mul_le_mul_of_nonneg_right hFour (Real.exp_nonneg _)
    _ = Real.exp (-(A + 4) * n) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(A + 1) * Real.log (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hLog := mul_le_mul_of_nonneg_left (Real.log_le_self hnReal.le)
        (by linarith only [hA] : 0 ≤ A + 1)
      nlinarith only [hLog, hnReal.le]
    _ = _ := by rw [Real.rpow_def_of_pos hnReal]; congr 1; ring

end CircularLaw
