import CircularLaw.GaussianCoordinateDeletion
import CircularLaw.OrderedNormAt
import CircularLaw.BinomialEntropy

/-!
# Small-ball bounds for actual Gaussian order statistics

Deleting the largest coordinates leaves a normal subspace of dimension
at least the original dimension minus the number deleted. The actual
projection small-ball law and a union over coordinate sets give an
order-statistic bound without coordinate independence assumptions.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped BigOperators InnerProductSpace

namespace CircularLaw

theorem gaussianDeletedCoordinates_smallBall_dimension_bound {n m k : ℕ}
    (hn : 0 < n) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hm : m ≤ Module.finrank ℂ Eᗮ) (K : Finset (Fin n)) (hCard : K.card = k)
    (hkm : k < m) {τ : ℝ} (hτ : 0 < τ)
    (hBase : Real.exp 1 * ((n : ℝ) * τ ^ 2) / (m - k : ℕ) ≤ 1) :
    (standardComplexGaussianVectorLaw n).real
      {z | ∀ i ∉ K, ‖projectedComplexGaussian E z i‖ ≤ τ} ≤
      (Real.exp 1 * ((n : ℝ) * τ ^ 2) / (m - k : ℕ)) ^ (m - k) := by
  have hDim := gaussianDeletedCoordinateSubspace_dimension E K
  have hDR : m - k ≤ Module.finrank ℂ (gaussianDeletedCoordinateSubspace E K) := by omega
  have hd : (0 : ℝ) < (m - k : ℕ) := by exact_mod_cast (by omega : 0 < m - k)
  have hDRreal : (m - k : ℕ) ≤
      (Module.finrank ℂ (gaussianDeletedCoordinateSubspace E K) : ℝ) := by exact_mod_cast hDR
  have hRatio : Real.exp 1 * ((n : ℝ) * τ ^ 2) /
      Module.finrank ℂ (gaussianDeletedCoordinateSubspace E K) ≤
      Real.exp 1 * ((n : ℝ) * τ ^ 2) / (m - k : ℕ) :=
    div_le_div_of_nonneg_left (by positivity) hd hDRreal
  apply (gaussianDeletedCoordinates_smallBall hn E K (by omega) hτ).trans
  exact (pow_le_pow_left₀ (by positivity) hRatio _).trans
    (pow_le_pow_of_le_one (by positivity) hBase hDR)

theorem projectedComplexGaussian_orderedNorm_smallBall {n m k : ℕ}
    (hn : 0 < n) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hm : m ≤ Module.finrank ℂ Eᗮ) (hk : 0 < k) (hkm : k < m)
    {τ : ℝ} (hτ : 0 < τ)
    (hBase : Real.exp 1 * ((n : ℝ) * τ ^ 2) / (m - k : ℕ) ≤ 1) :
    (standardComplexGaussianVectorLaw n).real
      {z | orderedNormAt (fun i => projectedComplexGaussian E z i) k ≤ τ} ≤
      (n.choose k : ℝ) *
        (Real.exp 1 * ((n : ℝ) * τ ^ 2) / (m - k : ℕ)) ^ (m - k) := by
  have hmn : m ≤ n := hm.trans (by simpa using Eᗮ.finrank_le)
  have hkn : k ≤ n := by omega
  let S := (Finset.univ : Finset (Fin n)).powersetCard k
  have hSubset : {z | orderedNormAt (fun i => projectedComplexGaussian E z i) k ≤ τ} ⊆
      ⋃ K ∈ S, {z | ∀ i ∉ K, ‖projectedComplexGaussian E z i‖ ≤ τ} := by
    intro z hz
    let K := orderedPrefix (fun i => projectedComplexGaussian E z i) k
    have hK : K ∈ S := Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, orderedPrefix_card _ hkn⟩
    refine Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr ⟨hK, ?_⟩⟩
    intro i hi
    exact (norm_le_orderedNormAt_notMem_prefix _ hk hkn i hi).trans hz
  apply (measureReal_mono hSubset (measure_ne_top _ _)).trans
  apply (measureReal_biUnion_finset_le S _).trans
  calc
    _ ≤ ∑ _K ∈ S,
        (Real.exp 1 * ((n : ℝ) * τ ^ 2) / (m - k : ℕ)) ^ (m - k) := by
      apply Finset.sum_le_sum
      intro K hK
      exact gaussianDeletedCoordinates_smallBall_dimension_bound hn E hm K
        (Finset.mem_powersetCard.mp hK).2 hkm hτ hBase
    _ = _ := by simp [S, Finset.card_powersetCard]

theorem projectedComplexGaussian_orderedNorm_smallBall_exponential {n m k : ℕ}
    (hn : 0 < n) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hm : m ≤ Module.finrank ℂ Eᗮ) (hk : 0 < k)
    (hDim : 5 * k ≤ m) (hAmbient : 256 * k ≤ n)
    {τ : ℝ} (hτ : 0 < τ) (hτUpper : τ ≤ 2 * (k : ℝ) / n) :
    (standardComplexGaussianVectorLaw n).real
      {z | orderedNormAt (fun i => projectedComplexGaussian E z i) k ≤ τ} ≤
      Real.exp (-(k : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkm : k < m := by omega
  have hd : (0 : ℝ) < (m - k : ℕ) := by exact_mod_cast (by omega : 0 < m - k)
  have hDR : 4 * (k : ℝ) ≤ (m - k : ℕ) := by
    exact_mod_cast (by omega : 4 * k ≤ m - k)
  have hAN : 256 * (k : ℝ) ≤ n := by exact_mod_cast hAmbient
  have hKN : (k : ℝ) / n ≤ 1 / 256 := (div_le_iff₀ hnR).mpr (by nlinarith)
  have hRatio : Real.exp 1 * ((n : ℝ) * τ ^ 2) / (m - k : ℕ) ≤
      Real.exp 1 * k / n := by
    apply (div_le_iff₀ hd).mpr
    have hSq := (sq_le_sq₀ hτ.le (by positivity)).mpr hτUpper
    calc
      _ ≤ Real.exp 1 * ((n : ℝ) * (2 * (k : ℝ) / n) ^ 2) := by gcongr
      _ = (Real.exp 1 * k / n) * (4 * k) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hDR (by positivity)
  have hRatioOne : Real.exp 1 * (k : ℝ) / n ≤ 1 := by
    calc
      _ = Real.exp 1 * ((k : ℝ) / n) := by ring
      _ ≤ 3 * (1 / 256) := mul_le_mul Real.exp_one_lt_three.le hKN
        (by positivity) (by norm_num)
      _ ≤ _ := by norm_num
  have hBase := hRatio.trans hRatioOne
  have hkn : k ≤ n := by omega
  apply (projectedComplexGaussian_orderedNorm_smallBall hn E hm hk hkm hτ hBase).trans
  calc
    _ ≤ (Real.exp 1 * n / k) ^ k * (Real.exp 1 * k / n) ^ (2 * k) := by
      apply mul_le_mul (choose_le_exp_ratio_power hn hk hkn)
        ((pow_le_pow_left₀ (by positivity) hRatio _).trans
          (pow_le_pow_of_le_one (by positivity) hRatioOne (by omega : 2 * k ≤ m - k)))
        (by positivity) (by positivity)
    _ = (Real.exp 1 ^ 3 * k / n) ^ k := by
      rw [pow_mul, ← mul_pow]
      congr 1
      field_simp
    _ ≤ (Real.exp (-1)) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      rw [Real.exp_neg, inv_eq_one_div]
      apply (le_div_iff₀ (Real.exp_pos 1)).mpr
      have h4 : Real.exp 1 ^ 4 * ((k : ℝ) / n) ≤ 1 := by
        calc
          _ ≤ (3 : ℝ) ^ 4 * (1 / 256) := mul_le_mul
            (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4)
            hKN (by positivity) (by positivity)
          _ ≤ _ := by norm_num
      convert h4 using 1
      ring
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem projectedComplexGaussian_nonflat_smallBall {n m : ℕ}
    (hn : 0 < n) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hm : m ≤ Module.finrank ℂ Eᗮ) (hLarge : 512 ≤ m) :
    (standardComplexGaussianVectorLaw n).real
      {z | orderedNormAt (fun i => projectedComplexGaussian E z i) (m / 512) ≤
        (m : ℝ) / (512 * n)} ≤ Real.exp (-(m : ℝ) / 512) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn : m ≤ n := hm.trans (by simpa using Eᗮ.finrank_le)
  have hk : 0 < m / 256 := by omega
  have hs : 0 < m / 512 := by omega
  have hkn : m / 256 ≤ n := by omega
  have hFloor : m ≤ 512 * (m / 256) := by omega
  have hFloorR : (m : ℝ) ≤ 512 * (m / 256 : ℕ) := by exact_mod_cast hFloor
  have hτ : (0 : ℝ) < (m : ℝ) / (256 * n) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    positivity
  have hτUpper : (m : ℝ) / (256 * n) ≤ 2 * (m / 256 : ℕ) / n := by
    rw [div_mul_eq_div_div]
    apply (div_le_div_iff_of_pos_right hnR).mpr
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
    nlinarith
  have hBound := projectedComplexGaussian_orderedNorm_smallBall_exponential hn E hm hk
    (by omega : 5 * (m / 256) ≤ m) (by omega : 256 * (m / 256) ≤ n) hτ hτUpper
  have hSubset : {z | orderedNormAt (fun i => projectedComplexGaussian E z i) (m / 512) ≤
      (m : ℝ) / (512 * n)} ⊆
      {z | orderedNormAt (fun i => projectedComplexGaussian E z i) (m / 256) ≤
        (m : ℝ) / (256 * n)} := by
    intro z hz
    apply (orderedNormAt_antitone _ hs (by omega : m / 512 ≤ m / 256) hkn).trans
    apply hz.trans
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  apply ((measureReal_mono hSubset).trans hBound).trans
  apply Real.exp_le_exp.mpr
  linarith

end CircularLaw
