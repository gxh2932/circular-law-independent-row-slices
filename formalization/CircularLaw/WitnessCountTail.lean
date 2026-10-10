import CircularLaw.RowWitnessBounds
import CircularLaw.IndependentLowerTail

/-!
# Exponential row-witness count tails

Only the rows are independent. The row probabilities themselves come from
the fixed-cardinality support model and its checked coordinate laws.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def uniqueWitnessRows {n d : ℕ} {ι : Type*} [Fintype ι]
    (L J : Finset (Fin n)) (rows : ι → RowSlice n d) : Finset ι :=
  Finset.univ.filter (fun i => uniqueRowWitness L J (rows i))

theorem unique_witness_rows_failure {n d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (L J : Finset (Fin n)) (hLJ : L ⊆ J)
    (hRows : (9 / 10 : ℝ) * n ≤ Fintype.card ι)
    (hLoss : ((d : ℝ) - 1) * ((J.card : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 10) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      ((uniqueWitnessRows L J rows).card : ℝ) < (d : ℝ) * L.card / 2) ≤
        Real.exp (-uniqueWitnessRate * d * L.card) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  let E := fun _i : ι => uniqueRowWitness (d := d) L J
  have hProb := unique_row_witness_probability_nine_tenths hn hd hdn L J hLJ hLoss
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hMean : (4 / 5 : ℝ) * ((d : ℝ) * L.card) ≤ ∑ i, uniformProbability (E i) := by
    calc
      _ ≤ (81 / 100 : ℝ) * d * L.card := by
        have hNonneg : (0 : ℝ) ≤ (d : ℝ) * L.card := by positivity
        nlinarith
      _ = ((9 / 10 : ℝ) * n) * ((9 / 10 : ℝ) * d * L.card / n) := by field_simp; ring
      _ ≤ (Fintype.card ι : ℝ) * ((9 / 10 : ℝ) * d * L.card / n) :=
        mul_le_mul_of_nonneg_right hRows (by positivity)
      _ ≤ (Fintype.card ι : ℝ) * uniformProbability (uniqueRowWitness (d := d) L J) :=
        mul_le_mul_of_nonneg_left hProb (Nat.cast_nonneg _)
      _ = _ := by simp only [E, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h := independent_lower_tail_four_fifths E ((d : ℝ) * L.card) hMean
  convert h using 1
  congr 1
  ring

theorem small_equal_pair_witness_failure {n d s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (L R : Finset (Fin n)) (hDis : Disjoint L R) (hL : L.card = s) (hR : R.card = s)
    (hRows : (n : ℝ) / 2 ≤ Fintype.card ι) (hSmall : 100 * d * s ≤ n) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      ((blockWitnessRows (L ∪ R) rows).card : ℝ) < (d : ℝ) * s / 4) ≤
        Real.exp (-(binomialHalfRate / 2) * d * s) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  let E := fun _i : ι => fun S : RowSlice n d => (S.val ∩ (L ∪ R)).card = 1
  have hProb := equal_pair_block_witness_probability hn hd hdn L R hDis hL hR hSmall
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hMean : (d : ℝ) * s / 2 ≤ ∑ i, uniformProbability (E i) := by
    calc
      _ = ((n : ℝ) / 2) * ((d : ℝ) * s / n) := by field_simp
      _ ≤ (Fintype.card ι : ℝ) * ((d : ℝ) * s / n) :=
        mul_le_mul_of_nonneg_right hRows (by positivity)
      _ ≤ (Fintype.card ι : ℝ) * uniformProbability
          (fun S : RowSlice n d => (S.val ∩ (L ∪ R)).card = 1) :=
        mul_le_mul_of_nonneg_left hProb (Nat.cast_nonneg _)
      _ = _ := by simp only [E, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hHalf := independent_lower_tail_half E
  have hCompare : uniformProbability (fun rows : ι → RowSlice n d =>
      ((blockWitnessRows (L ∪ R) rows).card : ℝ) < (d : ℝ) * s / 4) ≤
        uniformProbability (fun rows : ι → RowSlice n d =>
          (coordinateEventCount E rows : ℝ) < (∑ i, uniformProbability (E i)) / 2) := by
    apply uniformProbability_mono
    intro rows hRowsEvent
    have hCount : coordinateEventCount E rows = (blockWitnessRows (L ∪ R) rows).card := by
      unfold coordinateEventCount blockWitnessRows
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, E]
    rw [hCount]
    linarith
  apply (hCompare.trans hHalf).trans
  apply Real.exp_le_exp.mpr
  have hRate := binomialHalfRate_pos
  nlinarith

end CircularLaw
