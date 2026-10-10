import CircularLaw.EqualBlockEuclidean

/-!
# Equal-block Euclidean estimates on the selected-block witness event

One block with `B` witnessed rows gives the exponential estimate. For many
blocks, `B` witnesses per block and the deterministic incidence bounds give
`3*B/4` selected rows, each with at least `B*q/(4*n)` singleton blocks.
The resulting logarithmic norm estimate keeps precisely that witness
event in the probability.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def blockWitnessRows {n d : ℕ} {ι : Type*} [Fintype ι]
    (J : Finset (Fin n)) (rows : ι → RowSlice n d) : Finset ι :=
  Finset.univ.filter (fun i => ((rows i).val ∩ J).card = 1)

theorem block_witness_rows_subset_positive {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (J : κ → Finset (Fin n)) (rows : ι → RowSlice n d) (q : κ) :
    blockWitnessRows (J q) rows ⊆ largeWitnessRows (matrixSingletonCounts J rows) 1 := by
  intro i hi
  have hCount : ((rows i).val ∩ J q).card = 1 := (Finset.mem_filter.mp hi).2
  have hMem := (mem_singletonWitnessMask J (rows i) q).mpr hCount
  have hPositive := Finset.card_pos.mpr ⟨q, hMem⟩
  apply (mem_largeWitnessRows (matrixSingletonCounts J rows) 1 i).mpr
  exact_mod_cast hPositive

theorem equal_blocks_one_witness_euclidean_half {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hdn : d ≤ n) (L R : κ → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (L q ∪ R q) (L p ∪ R p)))
    (hHalves : ∀ q, Disjoint (L q) (R q)) (hSize : ∀ q, (L q).card = (R q).card)
    (hLeft : ∀ q, (L q).Nonempty) (y : Fin n → ℂ) {r B : ℝ}
    (hr : 0 < r) (hB : 0 ≤ B)
    (hSep : ∀ q l, l ∈ L q → ∀ j, j ∈ R q → 2 * r < dist (y l) (y j))
    (c ζ : ℂ) (index : ι → Fin n) (q : κ) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      shiftedRowsL2Norm rows y c ζ index ≤ r * Real.sqrt (B / 8) ∧
        B ≤ (blockWitnessRows (L q ∪ R q) rows).card) ≤
      Real.exp (-witnessHalfRate * B) := by
  apply (uniformProbability_mono ?_).trans
    (equal_blocks_selected_euclidean_half hdn L R hDis hHalves hSize hLeft y hr
      (by norm_num : (1 : ℝ) ≤ 1) hB hSep c ζ index)
  intro rows hEvent
  refine ⟨hEvent.1, hEvent.2.trans ?_⟩
  exact_mod_cast Finset.card_le_card (block_witness_rows_subset_positive (fun q => L q ∪ R q) rows q)

theorem equal_blocks_many_witnesses_euclidean_log {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hdn : d ≤ n) (hn : 0 < n) (hq : 0 < Fintype.card κ)
    (hDimension : Fintype.card ι ≤ n) (L R : κ → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (L q ∪ R q) (L p ∪ R p)))
    (hHalves : ∀ q, Disjoint (L q) (R q)) (hSize : ∀ q, (L q).card = (R q).card)
    (hLeft : ∀ q, (L q).Nonempty) (y : Fin n → ℂ) {r B p : ℝ}
    (hr : 0 < r) (hB : 0 ≤ B) (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    (ha : 1 ≤ B / (4 * (n : ℝ)) * Fintype.card κ)
    (hSep : ∀ q l, l ∈ L q → ∀ j, j ∈ R q → 2 * r < dist (y l) (y j))
    (hEsseen : (2 * (24 * Real.exp 1 / Real.pi)) /
      Real.sqrt (B / (4 * (n : ℝ)) * Fintype.card κ) ≤ p)
    (c ζ : ℂ) (index : ι → Fin n) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      shiftedRowsL2Norm rows y c ζ index ≤ r * Real.sqrt (3 * B / 32) ∧
        ∀ q, B ≤ (blockWitnessRows (L q ∪ R q) rows).card) ≤
      Real.exp (-witnessLogRate * ((3 / 4 : ℝ) * B) * Real.log (1 / p)) := by
  let J := fun q => L q ∪ R q
  have hRadius : (3 / 4 : ℝ) * B / 8 = 3 * B / 32 := by ring
  have hBound := equal_blocks_selected_euclidean_log hdn L R hDis hHalves hSize hLeft y hr
    ha (by positivity : 0 ≤ (3 / 4 : ℝ) * B) hp hpHalf hSep hEsseen c ζ index
  rw [hRadius] at hBound
  apply (uniformProbability_mono ?_).trans hBound
  intro rows hEvent
  refine ⟨hEvent.1, ?_⟩
  have hMax (i : ι) : (matrixSingletonCounts J rows i : ℝ) ≤ Fintype.card κ := by
    have h := Finset.card_le_card (Finset.filter_subset
      (s := (Finset.univ : Finset κ)) (p := fun q => ((rows i).val ∩ J q).card = 1))
    simp only [Finset.card_univ] at h
    exact_mod_cast h
  have hSum := sum_witness_count_lower J rows hEvent.2
  exact large_witness_rows_card_lower (matrixSingletonCounts J rows)
    (by exact_mod_cast hn) (by exact_mod_cast hq) hB (by exact_mod_cast hDimension) hMax hSum

end CircularLaw
