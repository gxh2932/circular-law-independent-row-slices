import CircularLaw.WeightedSliceLaplace
import CircularLaw.FiniteConditioning

/-!
# Actual out-neighbour sets and their void probabilities

The selected rows remain independent exact slices. Complementing a slice
and the checked containment probability bound control simultaneous empty
columns; no independence of different columns is assumed.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rowSliceOutNeighbours {m n d : ℕ} (S : Finset (Fin m))
    (rows : Fin m → RowSlice n d) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∃ i ∈ S, j ∈ (rows i).val)

theorem mem_rowSliceOutNeighbours {m n d : ℕ} (S : Finset (Fin m))
    (rows : Fin m → RowSlice n d) (j : Fin n) :
    j ∈ rowSliceOutNeighbours S rows ↔ ∃ i ∈ S, j ∈ (rows i).val := by
  simp only [rowSliceOutNeighbours, Finset.mem_filter, Finset.mem_univ, true_and]

theorem row_slice_avoidance_probability_le {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (T : Finset (Fin n)) :
    uniformProbability (fun s : RowSlice n d => Disjoint T s.val) ≤
      (1 - (d : ℝ) / n) ^ T.card := by
  let e := rowSliceComplementEquiv hd
  have hEvent : (fun s : RowSlice n d => Disjoint T s.val) =
      (fun s => T ⊆ (e s).val) := by
    funext s
    apply propext
    constructor
    · intro h j hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, Finset.disjoint_left.mp h hj⟩
    · intro h
      exact Finset.disjoint_left.mpr (fun j hj => (Finset.mem_sdiff.mp (h hj)).2)
  rw [hEvent, uniformProbability_reindex e (fun s => T ⊆ s.val)]
  have h := slice_containment_probability_le hn (Nat.sub_le n d) T
  have hRatio : ((n - d : ℕ) : ℝ) / n = 1 - (d : ℝ) / n := by
    rw [Nat.cast_sub hd]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  simpa only [hRatio] using h

theorem row_slice_out_neighbour_void_probability {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      T ⊆ Finset.univ \ rowSliceOutNeighbours S rows) ≤
        ((1 - (d : ℝ) / n) ^ S.card) ^ T.card := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hd
  let E := fun i : Fin m => fun s : RowSlice n d => i ∈ S → Disjoint T s.val
  have hEvent : (fun rows : Fin m → RowSlice n d =>
      T ⊆ Finset.univ \ rowSliceOutNeighbours S rows) = (fun rows => ∀ i, E i (rows i)) := by
    funext rows
    apply propext
    constructor
    · intro h i hi
      apply Finset.disjoint_left.mpr
      intro j hj hjRow
      exact (Finset.mem_sdiff.mp (h hj)).2 ((mem_rowSliceOutNeighbours S rows j).mpr ⟨i, hi, hjRow⟩)
    · intro h j hj
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, ?_⟩
      intro hjOut
      obtain ⟨i, hi, hjRow⟩ := (mem_rowSliceOutNeighbours S rows j).mp hjOut
      exact Finset.disjoint_left.mp (h i hi) hj hjRow
  rw [hEvent, uniformProbability_pi]
  have hPoint (i : Fin m) : uniformProbability (E i) ≤
      if i ∈ S then (1 - (d : ℝ) / n) ^ T.card else 1 := by
    by_cases hi : i ∈ S
    · simpa only [E, hi, true_implies, if_pos] using row_slice_avoidance_probability_le hn hd T
    · simp [E, hi, uniformProbability_true]
  calc
    _ ≤ ∏ i : Fin m, (if i ∈ S then (1 - (d : ℝ) / n) ^ T.card else 1) :=
      Finset.prod_le_prod (fun i _ => uniformProbability_nonneg _) (fun i _ => hPoint i)
    _ = ((1 - (d : ℝ) / n) ^ T.card) ^ S.card := by rw [Fintype.prod_ite_mem, Finset.prod_const]
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

def rowSliceOutNeighbourMean {m n : ℕ} (d : ℕ) (S : Finset (Fin m)) : ℝ :=
  (n : ℝ) * (1 - (1 - (d : ℝ) / n) ^ S.card)

theorem rowSliceOutNeighbourMean_nonneg {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) : 0 ≤ rowSliceOutNeighbourMean (n := n) d S := by
  have hp : 0 ≤ 1 - (d : ℝ) / n := by
    apply sub_nonneg.mpr
    exact (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr (by exact_mod_cast hd)
  have hpOne : 1 - (d : ℝ) / n ≤ 1 := by
    have h : (0 : ℝ) ≤ (d : ℝ) / n := by positivity
    linarith
  unfold rowSliceOutNeighbourMean
  exact mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (pow_le_one₀ hp hpOne))

end CircularLaw
