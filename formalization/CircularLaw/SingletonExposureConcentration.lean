import CircularLaw.SingletonExposure

/-!
# Concentration on the actual singleton-exposure fiber

The exposure statistic's fiber is transported to the checked support
fiber. Its concentration is at most one half and at most an absolute
constant divided by the square root of its actual witness count. Constant
vectors and deterministic diagonal shifts only move the center.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

theorem singleton_exposure_conditional_small_ball {n d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (J : ι → Finset (Fin n)) (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (reference : RowSlice n d) (hb : 1 ≤ (singletonWitnessMask J reference).card)
    (y : Fin n → ℂ) {r : ℝ} (hr : 0 < r)
    (hAtom : ∀ q z, uniformProbability (fun j : {j : Fin n // j ∈ J q} =>
      ‖y j.val - z‖ ≤ r) ≤ 1 / 2) (a z : ℂ) :
    uniformProbability (fun S : {S : RowSlice n d // singletonExposure J S = singletonExposure J reference} =>
      ‖rowLinearForm S.val y + a - z‖ ≤ r) ≤
        min (1 / 2) ((2 * (24 * Real.exp 1 / Real.pi)) /
          Real.sqrt ((singletonWitnessMask J reference).card : ℝ)) := by
  let fixed := singletonWitnessFixed J reference
  let blocks := fun q : SingletonWitnessIndices J reference => J q.val
  have hDisSub : Pairwise (fun q p : SingletonWitnessIndices J reference => Disjoint (blocks q) (blocks p)) :=
    fun _ _ hne => hDis (fun h => hne (Subtype.ext h))
  have hFixed : ∀ q, Disjoint fixed (blocks q) := singletonWitnessFixed_disjoint J reference
  have hDegree : fixed.card + Fintype.card (SingletonWitnessIndices J reference) = d :=
    singletonWitness_degree J hDis reference
  have hNonempty : ∀ q, (blocks q).Nonempty := by
    intro q
    let S : SingletonBlockFiber fixed blocks := ⟨reference.val, singletonWitness_reference_fiber J reference⟩
    exact ⟨(singletonBlockFiberChoice S q).val, (singletonBlockFiberChoice S q).property⟩
  let e := Equiv.subtypeEquivRight (singletonExposure_eq_iff_fiber J hDis reference)
  have hReindex := uniformProbability_reindex e.symm (fun S => ‖rowLinearForm S.val y + a - z‖ ≤ r)
  change uniformProbability (fun S : SingletonBlockSliceFiber (d := d) fixed blocks =>
    ‖rowLinearForm S.val y + a - z‖ ≤ r) = _ at hReindex
  rw [← hReindex]
  have h := singleton_block_conditional_small_ball fixed blocks hDisSub hFixed hDegree hNonempty
    (by simpa only [SingletonWitnessIndices, Fintype.card_coe] using hb)
    y hr (fun q => hAtom q.val) a z
  simpa only [SingletonWitnessIndices, Fintype.card_coe] using h

theorem equal_block_exposure_small_ball {n d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (L R : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (L q ∪ R q) (L p ∪ R p)))
    (hHalves : ∀ q, Disjoint (L q) (R q)) (hSize : ∀ q, (L q).card = (R q).card)
    (hLeft : ∀ q, (L q).Nonempty) (reference : RowSlice n d)
    (hb : 1 ≤ (singletonWitnessMask (fun q => L q ∪ R q) reference).card)
    (y : Fin n → ℂ) {r : ℝ} (hr : 0 < r)
    (hSep : ∀ q l, l ∈ L q → ∀ j, j ∈ R q → 2 * r < dist (y l) (y j)) (a z : ℂ) :
    uniformProbability (fun S : {S : RowSlice n d //
      singletonExposure (fun q => L q ∪ R q) S =
        singletonExposure (fun q => L q ∪ R q) reference} =>
      ‖rowLinearForm S.val y + a - z‖ ≤ r) ≤
        min (1 / 2) ((2 * (24 * Real.exp 1 / Real.pi)) /
          Real.sqrt ((singletonWitnessMask (fun q => L q ∪ R q) reference).card : ℝ)) :=
  singleton_exposure_conditional_small_ball (fun q => L q ∪ R q) hDis reference hb y hr
    (fun q z => equal_halves_small_ball (L q) (R q) (hHalves q) (hSize q) (hLeft q) y (hSep q) z) a z

theorem rowLinearForm_add_const {n d : ℕ} (S : RowSlice n d) (y : Fin n → ℂ) (c : ℂ) :
    rowLinearForm S (fun j => y j + c) = rowLinearForm S y + (d : ℂ) * c := by
  simp only [rowLinearForm, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, row_sum]

theorem shifted_row_action_eq_center {n d : ℕ} (S : RowSlice n d) (y : Fin n → ℂ)
    (c ζ : ℂ) (i : Fin n) :
    rowLinearForm S (fun j => y j + c) - ζ * (y i + c) =
      rowLinearForm S y + ((d : ℂ) * c - ζ * (y i + c)) := by
  rw [rowLinearForm_add_const]
  abel

end CircularLaw
