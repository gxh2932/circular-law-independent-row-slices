import CircularLaw.ExposedEventIntegration

/-!
# Unconditional equal-block bounds with selected witness rows

The selected set is computed from the actual row singleton counts and is
constant on the exposure fiber. A lower bound on its size is kept inside
the event. Integrating the checked conditional norm estimate gives the
fixed-vector estimate without an extra structural failure probability.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def matrixSingletonCounts {n d : ℕ} {ι κ : Type*}
    [Fintype κ] [DecidableEq κ] (J : κ → Finset (Fin n)) (rows : ι → RowSlice n d) : ι → ℕ :=
  fun i => (singletonWitnessMask J (rows i)).card

theorem matrixSingletonCounts_eq_of_exposure {n d : ℕ} {ι κ : Type*}
    [Fintype κ] [DecidableEq κ] (J : κ → Finset (Fin n))
    {rows reference : ι → RowSlice n d}
    (h : singletonMatrixExposure J rows = singletonMatrixExposure J reference) :
    matrixSingletonCounts J rows = matrixSingletonCounts J reference := by
  funext i
  exact congrArg Finset.card (congrArg Prod.fst (congrFun h i))

theorem equal_block_selected_norm_half {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hdn : d ≤ n) (J : κ → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (y : Fin n → ℂ) {r a B : ℝ} (hr : 0 < r) (ha : 1 ≤ a)
    (hAtom : ∀ q z, uniformProbability (fun j : {j : Fin n // j ∈ J q} =>
      ‖y j.val - z‖ ≤ r) ≤ 1 / 2) (c ζ : ℂ) (index : ι → Fin n) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      (∑ i, ‖shiftedRowAction (rows i) y c ζ (index i)‖ ^ 2) ≤ r ^ 2 * B / 8 ∧
        B ≤ (largeWitnessRows (matrixSingletonCounts J rows) a).card) ≤
      Real.exp (-witnessHalfRate * B) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  apply uniformProbability_inter_exposed (singletonMatrixExposure J)
    (fun rows => (∑ i, ‖shiftedRowAction (rows i) y c ζ (index i)‖ ^ 2) ≤ r ^ 2 * B / 8)
    (fun rows => B ≤ (largeWitnessRows (matrixSingletonCounts J rows) a).card)
    (Real.exp_nonneg _)
  · intro rows reference h
    rw [matrixSingletonCounts_eq_of_exposure J h]
  · intro reference hGood
    let I := largeWitnessRows (matrixSingletonCounts J reference) a
    have hb : ∀ i ∈ I, 1 ≤ (singletonWitnessMask J (reference i)).card := by
      intro i hi
      have h := ha.trans ((mem_largeWitnessRows (matrixSingletonCounts J reference) a i).mp hi)
      exact_mod_cast h
    apply (uniformProbability_mono ?_).trans
      ((equal_block_exposure_norm_half J hDis reference I hb y hr hAtom c ζ index).trans ?_)
    · intro rows hNorm
      have hSubset : (∑ i : I, ‖shiftedRowAction (rows.val i.val) y c ζ (index i.val)‖ ^ 2) ≤
          ∑ i, ‖shiftedRowAction (rows.val i) y c ζ (index i)‖ ^ 2 := by
        rw [Finset.sum_coe_sort I (fun i => ‖shiftedRowAction (rows.val i) y c ζ (index i)‖ ^ 2)]
        exact Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
      apply hSubset.trans (hNorm.trans _)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hGood (sq_nonneg r))
        (by norm_num)
    · apply Real.exp_le_exp.mpr
      nlinarith [witnessHalfRate_pos]

theorem equal_block_selected_norm_log {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hdn : d ≤ n) (J : κ → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (y : Fin n → ℂ) {r a B p : ℝ} (hr : 0 < r) (ha : 1 ≤ a)
    (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    (hAtom : ∀ q z, uniformProbability (fun j : {j : Fin n // j ∈ J q} =>
      ‖y j.val - z‖ ≤ r) ≤ 1 / 2)
    (hEsseen : (2 * (24 * Real.exp 1 / Real.pi)) / Real.sqrt a ≤ p)
    (c ζ : ℂ) (index : ι → Fin n) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      (∑ i, ‖shiftedRowAction (rows i) y c ζ (index i)‖ ^ 2) ≤ r ^ 2 * B / 8 ∧
        B ≤ (largeWitnessRows (matrixSingletonCounts J rows) a).card) ≤
      Real.exp (-witnessLogRate * B * Real.log (1 / p)) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  apply uniformProbability_inter_exposed (singletonMatrixExposure J)
    (fun rows => (∑ i, ‖shiftedRowAction (rows i) y c ζ (index i)‖ ^ 2) ≤ r ^ 2 * B / 8)
    (fun rows => B ≤ (largeWitnessRows (matrixSingletonCounts J rows) a).card)
    (Real.exp_nonneg _)
  · intro rows reference h
    rw [matrixSingletonCounts_eq_of_exposure J h]
  · intro reference hGood
    let I := largeWitnessRows (matrixSingletonCounts J reference) a
    have hWitness : ∀ i ∈ I, a ≤ ((singletonWitnessMask J (reference i)).card : ℝ) := by
      intro i hi
      exact (mem_largeWitnessRows (matrixSingletonCounts J reference) a i).mp hi
    have hb : ∀ i ∈ I, 1 ≤ (singletonWitnessMask J (reference i)).card := by
      intro i hi
      exact_mod_cast ha.trans (hWitness i hi)
    have hRows : ∀ i ∈ I, (2 * (24 * Real.exp 1 / Real.pi)) /
        Real.sqrt ((singletonWitnessMask J (reference i)).card : ℝ) ≤ p := by
      intro i hi
      exact (div_le_div_of_nonneg_left (by positivity)
        (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt (hWitness i hi))).trans hEsseen
    apply (uniformProbability_mono ?_).trans
      ((equal_block_exposure_norm_log J hDis reference I hb y hr hp hpHalf hAtom hRows c ζ index).trans ?_)
    · intro rows hNorm
      have hSubset : (∑ i : I, ‖shiftedRowAction (rows.val i.val) y c ζ (index i.val)‖ ^ 2) ≤
          ∑ i, ‖shiftedRowAction (rows.val i) y c ζ (index i)‖ ^ 2 := by
        rw [Finset.sum_coe_sort I (fun i => ‖shiftedRowAction (rows.val i) y c ζ (index i)‖ ^ 2)]
        exact Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
      apply hSubset.trans (hNorm.trans _)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hGood (sq_nonneg r))
        (by norm_num)
    · apply Real.exp_le_exp.mpr
      have hLog : 0 ≤ Real.log (1 / p) := by
        apply Real.log_nonneg
        exact (le_div_iff₀ hp).mpr (by linarith)
      have hRate : 0 ≤ witnessLogRate * Real.log (1 / p) :=
        mul_nonneg witnessLogRate_pos.le hLog
      nlinarith

end CircularLaw
