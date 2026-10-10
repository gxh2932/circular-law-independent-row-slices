import CircularLaw.NormMeanProjection
import CircularLaw.RowSliceHeavyBound
import CircularLaw.LightCoupleConcentration

/-!
# Light sums simultaneously over the actual two finite nets

The left net covers the real unit ball. The right net consists of
zero-sum unit vectors, so the raw light-sum tail applies. Their literal
product cardinality is absorbed into an exponential probability bound.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rowSliceLightThreshold (d : ℕ) (B : ℝ) : ℝ :=
  (d : ℝ) / Real.sqrt (9 * (d : ℝ)) + B * Real.sqrt (9 * (d : ℝ))

def RowSliceLightNetBound {m n d : ℕ} (B : ℝ) (rows : Fin m → RowSlice n d) : Prop :=
  ∀ x ∈ normLatticeNet m, ∀ y ∈ normZeroMeanNet n,
    |weightedSliceMatrixSum (lightMatrixWeights (fun i j => x i * y j)
      (Real.sqrt (9 * (d : ℝ)) / n)) rows| ≤ rowSliceLightThreshold d B

theorem norm_lattice_card_exponential {n : ℕ} (S : Finset (EuclideanSpace ℝ (Fin n)))
    (hCard : S.card ≤ 128 ^ n) : (S.card : ℝ) ≤ Real.exp (7 * (n : ℝ)) := by
  have hTwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at h
    exact h.le
  calc
    _ ≤ (128 : ℝ) ^ n := by exact_mod_cast hCard
    _ = ((2 : ℝ) ^ 7) ^ n := by norm_num
    _ ≤ ((Real.exp 1) ^ 7) ^ n :=
      pow_le_pow_left₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) hTwo 7) n
    _ = _ := by rw [← pow_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem rowSliceLightNetBound_failure_exponential {m n d : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {B : ℝ} (hB : 1 ≤ B) :
    uniformProbability (fun rows : Fin m → RowSlice n d => ¬RowSliceLightNetBound B rows) ≤
      4 * Real.exp ((14 - B / 32) * n) := by
  let P := (normLatticeNet m).product (normZeroMeanNet n)
  let bad := fun (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (rows : Fin m → RowSlice n d) => rowSliceLightThreshold d B ≤
      |weightedSliceMatrixSum (lightMatrixWeights (fun i j => p.1 i * p.2 j)
        (Real.sqrt (9 * (d : ℝ)) / n)) rows|
  have hCover : ∀ rows : Fin m → RowSlice n d, ¬RowSliceLightNetBound B rows →
      ∃ p ∈ P, bad p rows := by
    intro rows hFail
    unfold RowSliceLightNetBound at hFail
    push_neg at hFail
    obtain ⟨x, hx, y, hy, hBad⟩ := hFail
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, hBad.le⟩
  have hSingle : ∀ p ∈ P, uniformProbability (bad p) ≤ 4 * Real.exp (-B * n / 32) := by
    intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    have hxNorm := normLatticeNet_norm_bound hm hx
    have hyNorm := normZeroMeanNet_norm_bound hn hy
    have hxMass : (∑ i, (p.1 i) ^ 2) ≤ 1 := by
      rw [← real_euclidean_norm_sq]
      nlinarith [norm_nonneg p.1]
    have hyMass : (∑ j, (p.2 j) ^ 2) ≤ 1 := by
      rw [← real_euclidean_norm_sq]
      nlinarith [norm_nonneg p.2]
    have hMass : (∑ i, ∑ j, (p.1 i * p.2 j) ^ 2) ≤ 1 := by
      rw [rankOneWeights_squared_sum]
      have hyNonneg : 0 ≤ ∑ j, (p.2 j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hProduct := mul_le_mul hxMass hyMass hyNonneg (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using hProduct
    exact source_light_probability hn hdn (by positivity : 0 < 9 * (d : ℝ))
      (by nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d] : (d : ℝ) ≤ 9 * (d : ℝ)) hB _
      (rankOneWeights_sum_zero _ _ (normZeroMeanNet_sum_zero hn hy)) hMass
  have hCard : (P.card : ℝ) ≤ Real.exp (14 * (n : ℝ)) := by
    have hLeft := norm_lattice_card_exponential (normLatticeNet m) (normLatticeNet_card_le m)
    have hRight := norm_lattice_card_exponential (normZeroMeanNet n) (normZeroMeanNet_card_le n)
    have hmnReal : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hLeft' : ((normLatticeNet m).card : ℝ) ≤ Real.exp (7 * (n : ℝ)) :=
      hLeft.trans (Real.exp_le_exp.mpr (by linarith only [hmnReal]))
    calc
      _ = ((normLatticeNet m).card : ℝ) * (normZeroMeanNet n).card := by
        exact_mod_cast Finset.card_product (normLatticeNet m) (normZeroMeanNet n)
      _ ≤ Real.exp (7 * (n : ℝ)) * Real.exp (7 * (n : ℝ)) :=
        mul_le_mul hLeft' hRight (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (uniformProbability_mono hCover).trans
  apply (uniformProbability_finset_exists_le P bad).trans
  calc
    _ ≤ ∑ _p ∈ P, 4 * Real.exp (-B * n / 32) := Finset.sum_le_sum hSingle
    _ = (P.card : ℝ) * (4 * Real.exp (-B * n / 32)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (14 * (n : ℝ)) * (4 * Real.exp (-B * n / 32)) :=
      mul_le_mul_of_nonneg_right hCard (by positivity)
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem rowSliceLightNetBound_failure_polynomial {m n d : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {A : ℝ} (hA : 0 ≤ A) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      ¬RowSliceLightNetBound (32 * (A + 20)) rows) ≤ (n : ℝ) ^ (-(A + 1)) := by
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
      _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul hTwo hTwo (by norm_num) (Real.exp_pos _).le
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hnOne])
  apply (rowSliceLightNetBound_failure_exponential hm hnPos hmn hd hdn hB).trans
  calc
    _ = 4 * Real.exp (-(A + 6) * n) := by congr 2; ring
    _ ≤ Real.exp (2 * (n : ℝ)) * Real.exp (-(A + 6) * n) :=
      mul_le_mul_of_nonneg_right hFour (Real.exp_pos _).le
    _ = Real.exp (-(A + 4) * n) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(A + 1) * Real.log (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hLog := mul_le_mul_of_nonneg_left (Real.log_le_self hnReal.le)
        (by linarith only [hA] : 0 ≤ A + 1)
      nlinarith only [hLog, hnReal.le]
    _ = _ := by rw [Real.rpow_def_of_pos hnReal]; congr 1; ring

end CircularLaw
