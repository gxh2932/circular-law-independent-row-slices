import CircularLaw.LightCoupleBounds

/-!
# Actual rectangular edge counts and exponential moments

The edge count is the sum of support intersections over the selected
rows and columns. Its mean is exactly `(d/n)*|S|*|T|`. The checked
weighted slice moments give the Poisson exponential-moment bound under
the actual independent uniform row law, for either sign of the tilt.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rowSliceEdgeWeights {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) :
    Fin m → Fin n → ℝ := fun i j => if i ∈ S ∧ j ∈ T then 1 else 0

def rowSliceEdgeCount {m n d : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n))
    (rows : Fin m → RowSlice n d) : ℝ := weightedSliceMatrixSum (rowSliceEdgeWeights S T) rows

def rowSliceEdgeMean {m n : ℕ} (d : ℕ) (S : Finset (Fin m)) (T : Finset (Fin n)) : ℝ :=
  ((d : ℝ) / n) * ((S.card : ℝ) * (T.card : ℝ))

theorem rowSliceEdgeWeights_nonneg {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n))
    (i : Fin m) (j : Fin n) : 0 ≤ rowSliceEdgeWeights S T i j := by
  unfold rowSliceEdgeWeights
  split_ifs <;> norm_num

theorem rowSliceEdgeWeights_sum {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) :
    (∑ i, ∑ j, rowSliceEdgeWeights S T i j) = (S.card : ℝ) * (T.card : ℝ) := by
  have hRow (i : Fin m) : (∑ j, rowSliceEdgeWeights S T i j) =
      if i ∈ S then (T.card : ℝ) else 0 := by
    by_cases hi : i ∈ S <;> simp [rowSliceEdgeWeights, hi]
  simp_rw [hRow]
  simp

theorem rowSliceEdgeWeights_sum_apply {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n))
    (f : ℝ → ℝ) (hZero : f 0 = 0) :
    (∑ i, ∑ j, f (rowSliceEdgeWeights S T i j)) = (S.card : ℝ) * (T.card : ℝ) * f 1 := by
  have hPoint (i : Fin m) (j : Fin n) : f (rowSliceEdgeWeights S T i j) = rowSliceEdgeWeights S T i j * f 1 := by
    unfold rowSliceEdgeWeights
    split_ifs <;> simp only [one_mul, zero_mul, hZero]
  simp_rw [hPoint, ← Finset.sum_mul]
  rw [rowSliceEdgeWeights_sum]

theorem rowSliceEdgeCount_eq_intersection_sum {m n d : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n))
    (rows : Fin m → RowSlice n d) :
    rowSliceEdgeCount S T rows = ∑ i ∈ S, ((rows i).val ∩ T).card := by
  have hRow (i : Fin m) : weightedSliceSum Finset.univ (rowSliceEdgeWeights S T i) (rows i) =
      if i ∈ S then (((rows i).val ∩ T).card : ℝ) else 0 := by
    by_cases hi : i ∈ S
    · simp only [weightedSliceSum, rowSliceEdgeWeights, hi, true_and, if_true]
      have hIf (j : Fin n) : (if j ∈ (rows i).val then (if j ∈ T then (1 : ℝ) else 0) else 0) =
          if j ∈ (rows i).val ∩ T then 1 else 0 := by
        by_cases hS : j ∈ (rows i).val <;> by_cases hT : j ∈ T <;> simp [hS, hT]
      simp_rw [hIf]
      simp
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    · simp [weightedSliceSum, rowSliceEdgeWeights, hi]
  unfold rowSliceEdgeCount weightedSliceMatrixSum
  simp_rw [hRow]
  simp

theorem rowSliceEdgeCount_nonneg {m n d : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n))
    (rows : Fin m → RowSlice n d) : 0 ≤ rowSliceEdgeCount S T rows := by
  rw [rowSliceEdgeCount_eq_intersection_sum]
  positivity

theorem rowSliceEdgeMean_pos {m n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {S : Finset (Fin m)} {T : Finset (Fin n)} (hS : S.Nonempty) (hT : T.Nonempty) :
    0 < rowSliceEdgeMean d S T := by
  unfold rowSliceEdgeMean
  exact mul_pos (div_pos (by exact_mod_cast hd) (by exact_mod_cast hn))
    (mul_pos (by exact_mod_cast hS.card_pos) (by exact_mod_cast hT.card_pos))

theorem finiteMean_pi_apply {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (i : ι) (f : α → ℝ) :
    finiteMean (fun rows : ι → α => f (rows i)) = finiteMean f := by
  have h := finiteMean_pi_prod (fun j (a : α) => if j = i then f a else 1)
  have hMean (j : ι) : finiteMean (fun a : α => if j = i then f a else 1) =
      if j = i then finiteMean f else 1 := by
    by_cases hj : j = i <;> simp only [hj, if_true, if_false, finiteMean_const]
  simp_rw [Finset.prod_ite_eq', Finset.mem_univ, if_true, hMean] at h
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, if_true] using h

theorem finiteMean_rowSliceEdgeCount {m n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) :
    finiteMean (rowSliceEdgeCount S T : (Fin m → RowSlice n d) → ℝ) = rowSliceEdgeMean d S T := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  have hRow (i : Fin m) :
      finiteMean (fun rows : Fin m → RowSlice n d => weightedSliceSum Finset.univ (rowSliceEdgeWeights S T i) (rows i)) =
        ((d : ℝ) / n) * ∑ j : Fin n, rowSliceEdgeWeights S T i j := by
    have hEval := finiteMean_pi_apply (ι := Fin m) (α := RowSlice n d) i
      (weightedSliceSum (d := d) Finset.univ (rowSliceEdgeWeights S T i))
    have hSingle := finiteMean_weightedSliceSum hd hdn Finset.univ (rowSliceEdgeWeights S T i)
    exact hEval.trans hSingle
  have hSum := finiteMean_finset_sum (α := Fin m → RowSlice n d)
    (Finset.univ : Finset (Fin m))
    (fun i rows => weightedSliceSum Finset.univ (rowSliceEdgeWeights S T i) (rows i))
  change finiteMean (fun rows : Fin m → RowSlice n d =>
    ∑ i : Fin m, weightedSliceSum Finset.univ (rowSliceEdgeWeights S T i) (rows i)) = _
  rw [hSum]
  simp_rw [hRow]
  rw [← Finset.mul_sum, rowSliceEdgeWeights_sum]
  rfl

theorem rowSliceEdge_centered {m n d : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n))
    (rows : Fin m → RowSlice n d) :
    centeredWeightedSliceMatrixSum (rowSliceEdgeWeights S T) rows =
      rowSliceEdgeCount S T rows - rowSliceEdgeMean d S T := by
  rw [centeredWeightedSliceMatrixSum_eq, rowSliceEdgeWeights_sum]
  rfl

theorem rowSliceEdge_centered_laplace {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) (tilt : ℝ) :
    finiteMean (fun rows : Fin m → RowSlice n d =>
      Real.exp (tilt * (rowSliceEdgeCount S T rows - rowSliceEdgeMean d S T))) ≤
        Real.exp (rowSliceEdgeMean d S T * (Real.exp tilt - 1 - tilt)) := by
  have h := finiteMean_matrix_weighted_laplace_exp hn hd (rowSliceEdgeWeights S T)
    (rowSliceEdgeWeights_nonneg S T) tilt
  have hSum := rowSliceEdgeWeights_sum_apply S T (fun z => Real.exp (tilt * z) - 1 - tilt * z)
    (by norm_num)
  simp_rw [rowSliceEdge_centered] at h
  rw [hSum] at h
  apply h.trans_eq
  congr 1
  unfold rowSliceEdgeMean
  simp only [mul_one, mul_assoc]

theorem rowSliceEdge_laplace {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) (tilt : ℝ) :
    finiteMean (fun rows : Fin m → RowSlice n d => Real.exp (tilt * rowSliceEdgeCount S T rows)) ≤
      Real.exp (rowSliceEdgeMean d S T * (Real.exp tilt - 1)) := by
  have hPoint (rows : Fin m → RowSlice n d) : Real.exp (tilt * rowSliceEdgeCount S T rows) =
      Real.exp (tilt * rowSliceEdgeMean d S T) *
        Real.exp (tilt * (rowSliceEdgeCount S T rows - rowSliceEdgeMean d S T)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hPoint]
  rw [finiteMean_const_mul]
  apply (mul_le_mul_of_nonneg_left (rowSliceEdge_centered_laplace hn hd S T tilt)
    (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end CircularLaw
