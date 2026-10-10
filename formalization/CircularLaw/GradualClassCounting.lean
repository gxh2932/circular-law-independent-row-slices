import CircularLaw.GradualClassAlphabets
import CircularLaw.BlockMultisetEntropy

/-!
# Entropy bound for the actual gradual approximation classes

The four-block encoding is instantiated with the literal source class,
rounded ranks, finite grid alphabets, and the source range of `k`.
Its real entropy bound retains the exact caps before asymptotic
absorption. The eventual statement discharges the finite rank and
degree conditions uniformly throughout the manuscript's lower band.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def gradualClassSizeCap (n d : ℕ) (a₃ : ℝ) (q : Fin 4) : ℝ :=
  if q = 0 then n else if q = 1 then a₃ * n
  else if q = 2 then (n : ℝ) / Real.rpow (d : ℝ) (2 / 3)
  else 2 * n / Real.rpow (d : ℝ) (3 / 2)

def gradualClassAlphabetCap (n d : ℕ) (q : Fin 4) : ℝ :=
  if q = 0 then 25 * n / (d : ℝ) ^ 3 else if q = 1 then 49 * n
  else if q = 2 then 49 * n * (d : ℝ) ^ 3 else 49 * (n : ℝ) ^ 13

def gradualClassBlockEntropy (n d : ℕ) (a₃ : ℝ) (q : Fin 4) : ℝ :=
  if q = 0 then gradualClassAlphabetCap n d q *
    (1 + Real.log (1 + gradualClassSizeCap n d a₃ q / gradualClassAlphabetCap n d q))
  else gradualClassSizeCap n d a₃ q *
    (1 + Real.log (1 + gradualClassAlphabetCap n d q / gradualClassSizeCap n d a₃ q))

def gradualClassCountingEntropy (n d : ℕ) (a₃ : ℝ) : ℝ :=
  ∑ q : Fin 4, gradualClassBlockEntropy n d a₃ q

theorem gradualClassSizeCap_pos {n d : ℕ} {a₃ : ℝ} (hn : 0 < n) (hd : 0 < d)
    (ha : 0 < a₃) (q : Fin 4) : 0 < gradualClassSizeCap n d a₃ q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  fin_cases q <;> simp [gradualClassSizeCap] <;> positivity

theorem gradualClassAlphabetCap_pos {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (q : Fin 4) : 0 < gradualClassAlphabetCap n d q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  fin_cases q <;> simp [gradualClassAlphabetCap] <;> positivity

theorem gradualClassBlock_sizes_cap {n d : ℕ} {a₃ : ℝ} (hd : 0 < d) (ha : 0 ≤ a₃)
    (hDimension : (d : ℝ) * Real.sqrt d ≤ n) (q : Fin 4) :
    (assignmentPartSize (gradualClassBlock n d a₃) q : ℝ) ≤
      gradualClassSizeCap n d a₃ q := by
  have hSizes := gradualClassBlock_sizes_le n d a₃
  fin_cases q
  · simpa only [gradualClassSizeCap, ↓reduceIte] using
      (by exact_mod_cast hSizes.1 : (assignmentPartSize (gradualClassBlock n d a₃) 0 : ℝ) ≤ n)
  · change _ ≤ a₃ * n
    apply (by exact_mod_cast hSizes.2.1 :
      (assignmentPartSize (gradualClassBlock n d a₃) 1 : ℝ) ≤ thirdSteepScale n a₃).trans
    exact Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n))
  · change _ ≤ (n : ℝ) / Real.rpow (d : ℝ) (2 / 3)
    apply (by exact_mod_cast hSizes.2.2.1 :
      (assignmentPartSize (gradualClassBlock n d a₃) 2 : ℝ) ≤ secondSteepScale n d).trans
    exact Nat.floor_le (div_nonneg (Nat.cast_nonneg n)
      (Real.rpow_nonneg (Nat.cast_nonneg d) (2 / 3)))
  · change _ ≤ 2 * n / Real.rpow (d : ℝ) (3 / 2)
    apply (by exact_mod_cast hSizes.2.2.2 :
      (assignmentPartSize (gradualClassBlock n d a₃) 3 : ℝ) ≤ firstSteepScale n d).trans
    simpa only [degree_three_halves_eq hd] using firstSteepScale_upper hd hDimension

theorem gradualClassBlock_alphabets_cap {n d k : ℕ} (hn : 0 < n)
    (hd : 0 < d) (hk : 0 < k) (hBudget : (k : ℝ) ^ 2 * (d : ℝ) ^ 3 ≤ n) (q : Fin 4) :
    ((gradualClassBlockValues n d k q).card : ℝ) ≤ gradualClassAlphabetCap n d q := by
  have hBounds := gradualClassBlock_alphabets_budget hn hd hk hBudget
  fin_cases q
  · simpa only [gradualClassAlphabetCap, ↓reduceIte] using hBounds.1
  · simpa only [gradualClassAlphabetCap, ↓reduceIte] using hBounds.2.1
  · simpa only [gradualClassAlphabetCap, ↓reduceIte] using hBounds.2.2.1
  · simpa only [gradualClassAlphabetCap, ↓reduceIte] using hBounds.2.2.2

theorem sourceGradualApproxClasses_entropy_bound {n d L k : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (ha : 0 < a₃)
    (hThird : 0 < thirdSteepScale n a₃) (hThirdN : thirdSteepScale n a₃ ≤ n)
    (hk : 0 < k) (hBudget : (k : ℝ) ^ 2 * (d : ℝ) ^ 3 ≤ n) :
    (Nat.card {m : Multiset ℂ // m ∈
      coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))} : ℝ) ≤
        Real.exp (gradualClassCountingEntropy n d a₃) := by
  have hn : 0 < n := by omega
  have hd : 0 < d := by have h := hConditions.degree_large; omega
  have hFactor (q : Fin 4) :
      (((gradualClassBlockValues n d k q).card +
        assignmentPartSize (gradualClassBlock n d a₃) q - 1).choose
          (assignmentPartSize (gradualClassBlock n d a₃) q) : ℝ) ≤
      Real.exp (gradualClassBlockEntropy n d a₃ q) := by
    have hN := gradualClassBlock_sizes_cap hd ha.le hConditions.dimension_root q
    have hA := gradualClassBlock_alphabets_cap hn hd hk hBudget q
    unfold gradualClassBlockEntropy
    split_ifs
    · exact starsBars_exp_bound_alphabet (gradualClassSizeCap_pos hn hd ha q)
        (gradualClassAlphabetCap_pos hn hd q) hN hA
    · exact starsBars_exp_bound_size (gradualClassSizeCap_pos hn hd ha q)
        (gradualClassAlphabetCap_pos hn hd q) hN hA
  have hCount : (Nat.card {m : Multiset ℂ // m ∈
      coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))} : ℝ) ≤
      ∏ q : Fin 4, (((gradualClassBlockValues n d k q).card +
        assignmentPartSize (gradualClassBlock n d a₃) q - 1).choose
          (assignmentPartSize (gradualClassBlock n d a₃) q) : ℝ) := by
    exact_mod_cast sourceGradualApproxClasses_card_le_blocks hConditions hL hCubic hThird hThirdN
  apply hCount.trans
  rw [gradualClassCountingEntropy, Real.exp_sum]
  exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun q _ => hFactor q)

theorem sourceGradualApproxFamily_finite {n d L k : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3)
    (hThird : 0 < thirdSteepScale n a₃) (hThirdN : thirdSteepScale n a₃ ≤ n) :
    (canonicalApproxFamily k (sourceGradual n d L a₃)).Finite :=
  finite_of_coordinateMultisetClasses_finite
    (sourceGradualApproxClasses_finite hConditions hL hCubic hThird hThirdN)

theorem eventually_sourceGradualApproxClasses_entropy_uniform {a₃ C : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hC : 0 < C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ k : ℕ, 0 < k →
        (k : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) →
        (canonicalApproxFamily k (sourceGradual n d L a₃)).Finite ∧
        (coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))).Finite ∧
        (Nat.card {m : Multiset ℂ // m ∈
          coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))} : ℝ) ≤
          Real.exp (gradualClassCountingEntropy n d a₃) := by
  filter_upwards [eventually_ge_atTop ⌈2 / a₃⌉₊,
    eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC eventually_steepStride_cubic] with n hn hConditions hCubic
  intro d hBand L hL k hk hRange
  have hSize : 2 ≤ a₃ * (n : ℝ) := by
    have hN : (⌈2 / a₃⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    have h := (Nat.le_ceil (2 / a₃)).trans hN
    have hMul := (div_le_iff₀ ha).mp h
    nlinarith
  have hThird := (thirdSteepScale_bounds ha hSize).1
  have hThirdN : thirdSteepScale n a₃ ≤ n := by
    have h := thirdSteepScale_half (n := n) ha.le haHalf
    omega
  have hCon := hConditions d hBand.1 hBand.2
  have hd : 0 < d := by have h := hCon.degree_large; omega
  exact ⟨sourceGradualApproxFamily_finite hCon hL (hCubic d hBand.1) hThird hThirdN,
    sourceGradualApproxClasses_finite hCon hL (hCubic d hBand.1) hThird hThirdN,
    sourceGradualApproxClasses_entropy_bound hCon hL (hCubic d hBand.1) ha hThird hThirdN hk
      (class_scale_budget_of_range hd hRange)⟩

end CircularLaw
