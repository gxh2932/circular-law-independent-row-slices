import CircularLaw.BlockMultisetCounting
import CircularLaw.CanonicalClassCardinality
import CircularLaw.GridBox
import CircularLaw.CoordinateRanges

/-!
# Actual rank-block encoding of gradual canonical approximation classes

The bulk tail has radius one, the next two blocks have radii `d^(3/2)`
and `d^3`, and the initial block has radius `n^6`. The last bound uses
the checked literal gradual class. In the manuscript's logarithmic
lower band this four-block encoding suffices for the class-count bound.
The precise exponential absorption is kept separate from the encoding.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def gradualClassBlock (n d : ℕ) (a₃ : ℝ) (j : Fin n) : Fin 4 :=
  if thirdSteepScale n a₃ ≤ j.val then 0
  else if secondSteepScale n d ≤ j.val then 1
  else if firstSteepScale n d ≤ j.val then 2
  else 3

def gradualClassBlockRadius (n d : ℕ) (q : Fin 4) : ℝ :=
  if q = 0 then 1 else if q = 1 then Real.rpow (d : ℝ) (3 / 2)
  else if q = 2 then (d : ℝ) ^ 3 else (n : ℝ) ^ 6

def gradualClassBlockValues (n d k : ℕ) (q : Fin 4) : Finset ℂ :=
  gridBox k (gridBoxRadius k (gradualClassBlockRadius n d q))

theorem norm_sorted_le_orderedNormAt {n : ℕ} (x : Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) (hσ : Antitone (fun i => ‖x (σ i)‖))
    {rank : ℕ} (hRank : 0 < rank) (hRankN : rank ≤ n)
    (j : Fin n) (hj : rank ≤ j.val) : ‖x (σ j)‖ ≤ orderedNormAt x rank := by
  rw [norm_sorted_eq_orderedNorm x σ hσ j, orderedNormAt_eq x hRank hRankN]
  apply orderedNorm_antitone x
  apply Fin.le_iff_val_le_val.mpr
  change rank - 1 ≤ j.val
  omega

theorem source_gradual_first_scale_modulus {n d L : ℕ} (hd : 0 < d) {a₃ : ℝ}
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    orderedNormAt x (firstSteepScale n d) ≤ (d : ℝ) ^ 3 := by
  apply le_of_not_gt
  intro hBad
  apply hx.1
  apply source_steep_union_of_large_gap hd a₃ x
  simpa only [hx.2.2, mul_one] using hBad

theorem source_gradual_block_modulus {n d L : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3)
    (hThird : 0 < thirdSteepScale n a₃) (hThirdN : thirdSteepScale n a₃ ≤ n)
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃)
    (σ : Equiv.Perm (Fin n)) (hσ : Antitone (fun i => ‖x (σ i)‖)) (j : Fin n) :
    ‖x (σ j)‖ ≤ gradualClassBlockRadius n d (gradualClassBlock n d a₃ j) := by
  have hd : 0 < d := by have h := hConditions.degree_large; omega
  have hn : 0 < n := by omega
  have hRanks := source_starting_rank_bounds hConditions.degree_large
    hConditions.dimension_fourth hConditions.dimension_root hL
    hConditions.stride_pos hConditions.stride_upper
  unfold gradualClassBlock
  split_ifs with h3 h2 h1
  · simpa only [gradualClassBlockRadius, ↓reduceIte] using
      (norm_sorted_le_orderedNormAt x σ hσ hThird hThirdN j h3).trans_eq hx.2.2
  · simpa only [gradualClassBlockRadius, ↓reduceIte, OfNat.ofNat_ne_zero] using
      source_gradual_sorted_tail (secondSteepScale_valid hd hConditions.dimension_root).1
        (secondSteepScale_valid hd hConditions.dimension_root).2 x hx σ hσ j h2
  · have hFirst := norm_sorted_le_orderedNormAt x σ hσ (firstSteepScale_pos hn hd)
      hRanks.2.2.1 j h1
    simpa only [gradualClassBlockRadius, ↓reduceIte, OfNat.ofNat_ne_zero] using
      hFirst.trans (source_gradual_first_scale_modulus hd x hx)
  · have hFirst := (norm_le_first_orderedNormAt hn x (σ j)).trans
      (source_gradual_first_modulus hConditions hL hCubic x hx)
    simpa only [gradualClassBlockRadius, ↓reduceIte, OfNat.ofNat_ne_zero] using hFirst

theorem sourceGradualApprox_block_envelope {n d L k : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3)
    (hThird : 0 < thirdSteepScale n a₃) (hThirdN : thirdSteepScale n a₃ ≤ n) :
    ∀ y ∈ canonicalApproxFamily k (sourceGradual n d L a₃),
      ∃ σ : Equiv.Perm (Fin n), ∀ j,
        y (σ j) ∈ gradualClassBlockValues n d k (gradualClassBlock n d a₃ j) := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨normOrderPerm x, fun j => ?_⟩
  apply canonicalApprox_mem_gridBox
  exact source_gradual_block_modulus hConditions hL hCubic hThird hThirdN x hx
    (normOrderPerm x) (orderedNorm_antitone x) j

theorem sourceGradualApproxClasses_finite {n d L k : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3)
    (hThird : 0 < thirdSteepScale n a₃) (hThirdN : thirdSteepScale n a₃ ≤ n) :
    (coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))).Finite :=
  coordinateMultisetClasses_finite_of_blocks (gradualClassBlock n d a₃)
    (gradualClassBlockValues n d k) _
    (sourceGradualApprox_block_envelope hConditions hL hCubic hThird hThirdN)

theorem sourceGradualApproxClasses_card_le_blocks {n d L k : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3)
    (hThird : 0 < thirdSteepScale n a₃) (hThirdN : thirdSteepScale n a₃ ≤ n) :
    Nat.card {m : Multiset ℂ // m ∈
      coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))} ≤
        ∏ q : Fin 4, ((gradualClassBlockValues n d k q).card +
          assignmentPartSize (gradualClassBlock n d a₃) q - 1).choose
            (assignmentPartSize (gradualClassBlock n d a₃) q) :=
  coordinateMultisetClasses_card_le_blocks (gradualClassBlock n d a₃)
    (gradualClassBlockValues n d k) _
    (sourceGradualApprox_block_envelope hConditions hL hCubic hThird hThirdN)

theorem fin_assignmentPartSize_le {n : ℕ} {ι : Type*} (part : Fin n → ι) (q : ι)
    (T : ℕ) (h : ∀ j : Fin n, part j = q → j.val < T) :
    assignmentPartSize part q ≤ T := by
  let f : {j : Fin n // part j = q} → Fin T := fun j => ⟨j.val.val, h j.val j.property⟩
  have hf : Function.Injective f := by
    intro j j' hEq
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun a : Fin T => a.val) hEq
  exact (Nat.card_le_card_of_injective f hf).trans_eq (by simp only [Nat.card_fin])

theorem gradualClassBlock_one_lt {n d : ℕ} {a₃ : ℝ} (j : Fin n)
    (h : gradualClassBlock n d a₃ j = 1) : j.val < thirdSteepScale n a₃ := by
  unfold gradualClassBlock at h
  split_ifs at h <;> simp_all

theorem gradualClassBlock_two_lt {n d : ℕ} {a₃ : ℝ} (j : Fin n)
    (h : gradualClassBlock n d a₃ j = 2) : j.val < secondSteepScale n d := by
  unfold gradualClassBlock at h
  split_ifs at h <;> simp_all

theorem gradualClassBlock_three_lt {n d : ℕ} {a₃ : ℝ} (j : Fin n)
    (h : gradualClassBlock n d a₃ j = 3) : j.val < firstSteepScale n d := by
  unfold gradualClassBlock at h
  split_ifs at h <;> simp_all

theorem gradualClassBlock_sizes_le (n d : ℕ) (a₃ : ℝ) :
    assignmentPartSize (gradualClassBlock n d a₃) 0 ≤ n ∧
    assignmentPartSize (gradualClassBlock n d a₃) 1 ≤ thirdSteepScale n a₃ ∧
    assignmentPartSize (gradualClassBlock n d a₃) 2 ≤ secondSteepScale n d ∧
    assignmentPartSize (gradualClassBlock n d a₃) 3 ≤ firstSteepScale n d :=
  ⟨fin_assignmentPartSize_le _ _ _ (fun j _ => j.isLt),
    fin_assignmentPartSize_le _ _ _ gradualClassBlock_one_lt,
    fin_assignmentPartSize_le _ _ _ gradualClassBlock_two_lt,
    fin_assignmentPartSize_le _ _ _ gradualClassBlock_three_lt⟩

end CircularLaw
