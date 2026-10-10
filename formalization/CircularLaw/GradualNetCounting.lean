import CircularLaw.TwoAlphabetCounting
import CircularLaw.GradualClassAlphabets
import CircularLaw.OrderedPrefix
import CircularLaw.SteepNetFit

/-!
# The actual gradual approximation family has two finite alphabets

The exceptional set is the top `n2` coordinates of the source vector,
with its actual chosen ordering of ties. Original coordinates have
radius `n^6` on that set and radius `d^(3/2)` on its complement. Floor
rounding lands in the corresponding counted grid boxes.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem sourceGradualApprox_twoAlphabet_envelope {n d L k : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) :
    ∀ y ∈ canonicalApproxFamily k (sourceGradual n d L a₃),
      ∃ T : Finset (Fin n), T.card = secondSteepScale n d ∧
        (∀ i ∈ T, y i ∈ gradualClassBlockValues n d k 3) ∧
        ∀ i ∉ T, y i ∈ gradualClassBlockValues n d k 1 := by
  have hFinite := source_kernel_dimension_twice_degree hConditions
  have hRanks := secondSteepScale_valid hFinite.2.1 hConditions.dimension_root
  rintro y ⟨x, hx, rfl⟩
  refine ⟨orderedPrefix x (secondSteepScale n d), orderedPrefix_card x hRanks.2, ?_, ?_⟩
  · intro i _
    change canonicalApprox k (x i) ∈ gridBox k (gridBoxRadius k ((n : ℝ) ^ 6))
    apply canonicalApprox_mem_gridBox
    exact (norm_le_first_orderedNormAt hFinite.1 x i).trans
      (source_gradual_first_modulus hConditions hL hCubic x hx)
  · intro i hi
    change canonicalApprox k (x i) ∈ gridBox k (gridBoxRadius k (Real.rpow (d : ℝ) (3 / 2)))
    apply canonicalApprox_mem_gridBox
    have hRank : secondSteepScale n d ≤ ((normOrderPerm x).symm i).val := by
      have hNot : ¬((normOrderPerm x).symm i).val < secondSteepScale n d :=
        fun h => hi ((mem_orderedPrefix x _ i).mpr h)
      omega
    simpa only [Equiv.apply_symm_apply] using
      source_gradual_sorted_tail hRanks.1 hRanks.2 x hx (normOrderPerm x)
        (orderedNorm_antitone x) ((normOrderPerm x).symm i) hRank

theorem sourceGradualApprox_family_twoAlphabet_count {n d L k : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) :
    (canonicalApproxFamily k (sourceGradual n d L a₃)).Finite ∧
    Nat.card (canonicalApproxFamily k (sourceGradual n d L a₃)) ≤
      n.choose (secondSteepScale n d) *
        (gradualClassBlockValues n d k 3).card ^ secondSteepScale n d *
          (gradualClassBlockValues n d k 1).card ^ (n - secondSteepScale n d) := by
  simpa only [Fintype.card_fin] using twoAlphabet_family_count
    (gradualClassBlockValues n d k 3) (gradualClassBlockValues n d k 1)
    (secondSteepScale n d) (canonicalApproxFamily k (sourceGradual n d L a₃))
      (sourceGradualApprox_twoAlphabet_envelope hConditions hL hCubic)

def gradualNetCountingEntropy (n d k : ℕ) : ℝ :=
  (n : ℝ) * (Real.log 2 + Real.log 49 + 2 * Real.log k + 3 * Real.log d) +
    (secondSteepScale n d : ℝ) * (Real.log 49 + 2 * Real.log k + 12 * Real.log n)

theorem gradual_grid_alphabet_exp_bounds {n d k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) (r : ℕ) :
    ((gradualClassBlockValues n d k 3).card : ℝ) ^ r ≤
      Real.exp ((r : ℝ) * (Real.log 49 + 2 * Real.log k + 12 * Real.log n)) ∧
    ((gradualClassBlockValues n d k 1).card : ℝ) ^ r ≤
      Real.exp ((r : ℝ) * (Real.log 49 + 2 * Real.log k + 3 * Real.log d)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hAlphabets := gradualClassBlock_alphabets hn hd hk
  have hTop := pow_le_pow_left₀ (Nat.cast_nonneg _) hAlphabets.2.2.2 r
  have hTail := pow_le_pow_left₀ (Nat.cast_nonneg _) hAlphabets.2.1 r
  have hExpK : Real.exp (2 * Real.log k) = (k : ℝ) ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hkR] using Real.exp_nat_mul (Real.log k) 2
  have hExpN : Real.exp (12 * Real.log n) = (n : ℝ) ^ 12 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hnR] using Real.exp_nat_mul (Real.log n) 12
  have hExpD : Real.exp (3 * Real.log d) = (d : ℝ) ^ 3 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hdR] using Real.exp_nat_mul (Real.log d) 3
  constructor
  · apply hTop.trans_eq
    rw [Real.exp_nat_mul, Real.exp_add, Real.exp_add, hExpK, hExpN,
      Real.exp_log (by norm_num : (0 : ℝ) < 49)]
  · apply hTail.trans_eq
    rw [Real.exp_nat_mul, Real.exp_add, Real.exp_add, hExpK, hExpD,
      Real.exp_log (by norm_num : (0 : ℝ) < 49)]

theorem sourceGradualApprox_family_entropy_bound {n d L k : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (hk : 0 < k) :
    (canonicalApproxFamily k (sourceGradual n d L a₃)).Finite ∧
    (Nat.card (canonicalApproxFamily k (sourceGradual n d L a₃)) : ℝ) ≤
      Real.exp (gradualNetCountingEntropy n d k) := by
  have hFinite := source_kernel_dimension_twice_degree hConditions
  obtain ⟨hFamily, hCount⟩ := sourceGradualApprox_family_twoAlphabet_count hConditions hL hCubic
  have hReal : (Nat.card (canonicalApproxFamily k (sourceGradual n d L a₃)) : ℝ) ≤
      (n.choose (secondSteepScale n d) : ℝ) *
        ((gradualClassBlockValues n d k 3).card : ℝ) ^ secondSteepScale n d *
        ((gradualClassBlockValues n d k 1).card : ℝ) ^ (n - secondSteepScale n d) := by
    exact_mod_cast hCount
  have hChoose : (n.choose (secondSteepScale n d) : ℝ) ≤ Real.exp ((n : ℝ) * Real.log 2) := by
    have h := (by exact_mod_cast Nat.choose_le_two_pow n (secondSteepScale n d) :
      (n.choose (secondSteepScale n d) : ℝ) ≤ (2 : ℝ) ^ n)
    exact h.trans_eq (by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)])
  have hTop := (gradual_grid_alphabet_exp_bounds hFinite.1 hFinite.2.1 hk (secondSteepScale n d)).1
  have hTail := (gradual_grid_alphabet_exp_bounds hFinite.1 hFinite.2.1 hk (n - secondSteepScale n d)).2
  have hTailLog : 0 ≤ Real.log 49 + 2 * Real.log k + 3 * Real.log d := by
    have hLogK := Real.log_nonneg (by exact_mod_cast hk : (1 : ℝ) ≤ k)
    have hLogD := Real.log_nonneg (by exact_mod_cast hFinite.2.1 : (1 : ℝ) ≤ d)
    have hLog49 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 49)
    linarith
  have hTailCount : ((n - secondSteepScale n d : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n (secondSteepScale n d)
  have hTail' := hTail.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hTailCount hTailLog))
  refine ⟨hFamily, hReal.trans ?_⟩
  apply (mul_le_mul (mul_le_mul hChoose hTop (by positivity) (Real.exp_nonneg _))
    hTail' (by positivity) (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))).trans_eq
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold gradualNetCountingEntropy
  ring

end CircularLaw
