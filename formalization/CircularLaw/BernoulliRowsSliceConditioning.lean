import CircularLaw.BernoulliSliceTransfer
import CircularLaw.BernoulliRowProductLaw

/-!
# Conditioning only selected independent rows to fixed-size slices

The exact event identity charges the support-size mass once per selected
row. Thus the Bernoulli transfer loss depends on the selected row count.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace CircularLaw

def bernoulliRowsSliceFiberEquiv (ι : Type*) [Fintype ι] (n d : ℕ) :
    (ι → RowSlice n d) ≃ {x : ι → Fin n → Bool // ∀ i, bernoulliSupportSize (x i) = d} where
  toFun rows := ⟨fun i => rowSliceBoolRow (rows i), fun i => by
    rw [bernoulliSupportSize, bernoulliSupport_rowSliceBoolRow]
    exact (rows i).property⟩
  invFun x := fun i => ⟨bernoulliSupport (x.val i), x.property i⟩
  left_inv rows := by
    funext i
    exact Subtype.ext (bernoulliSupport_rowSliceBoolRow (rows i))
  right_inv x := by
    apply Subtype.ext
    funext i j
    simp only [rowSliceBoolRow, bernoulliSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    cases x.val i j <;> simp

theorem bernoulli_rows_slice_atom {ι : Type*} [Fintype ι] {n d : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (x : ι → Fin n → Bool)
    (hSize : ∀ i, bernoulliSupportSize (x i) = d) :
    (Measure.pi (fun _ : ι => bernoulliCubeLaw (Fin n) p hp)).real {x} =
      bernoulliSliceAtomWeight n d p ^ Fintype.card ι := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, bernoulliCubeLaw_singleton_real, hSize]
  simp only [bernoulliSliceAtomWeight, Finset.prod_const, Finset.card_univ]

theorem bernoulli_rows_slice_event_probability {ι : Type*} [Fintype ι] {n d : ℕ}
    (hdn : d ≤ n) (p : ℝ≥0) (hp : p ≤ 1) (E : (ι → Fin n → Bool) → Prop) :
    (Measure.pi (fun _ : ι => bernoulliCubeLaw (Fin n) p hp)).real
      {x | (∀ i, bernoulliSupportSize (x i) = d) ∧ E x} =
      bernoulliSliceMass n d p ^ Fintype.card ι *
        uniformProbability (fun rows : ι → RowSlice n d => E (fun i => rowSliceBoolRow (rows i))) := by
  rw [finiteMeasure_event_real]
  have hSum : (∑ x : ι → Fin n → Bool,
      if (∀ i, bernoulliSupportSize (x i) = d) ∧ E x then
        (Measure.pi (fun _ : ι => bernoulliCubeLaw (Fin n) p hp)).real {x} else 0) =
      bernoulliSliceAtomWeight n d p ^ Fintype.card ι *
        ∑ rows : ι → RowSlice n d, if E (fun i => rowSliceBoolRow (rows i)) then 1 else 0 := by
    calc
      _ = ∑ x : ι → Fin n → Bool, if ∀ i, bernoulliSupportSize (x i) = d then
          bernoulliSliceAtomWeight n d p ^ Fintype.card ι * (if E x then 1 else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hSize : ∀ i, bernoulliSupportSize (x i) = d
        · by_cases hE : E x <;> simp [hSize, hE, bernoulli_rows_slice_atom p hp x hSize]
        · simp [hSize]
      _ = _ := by
        rw [← Finset.sum_filter]
        rw [Finset.sum_subtype (p := fun x : ι → Fin n → Bool => ∀ i, bernoulliSupportSize (x i) = d)
          (Finset.univ.filter (fun x : ι → Fin n → Bool => ∀ i, bernoulliSupportSize (x i) = d))
          (fun x => by simp) (fun x => bernoulliSliceAtomWeight n d p ^ Fintype.card ι * (if E x then 1 else 0))]
        rw [← (bernoulliRowsSliceFiberEquiv ι n d).sum_comp]
        rw [Finset.mul_sum]
        rfl
  calc
    _ = ∑ x : ι → Fin n → Bool,
        if (∀ i, bernoulliSupportSize (x i) = d) ∧ E x then
          (Measure.pi (fun _ : ι => bernoulliCubeLaw (Fin n) p hp)).real {x} else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : (∀ i, bernoulliSupportSize (x i) = d) ∧ E x <;> simp [h]
    _ = bernoulliSliceAtomWeight n d p ^ Fintype.card ι *
        ∑ rows : ι → RowSlice n d, if E (fun i => rowSliceBoolRow (rows i)) then 1 else 0 := hSum
    _ = _ := by
      have hCount : (Fintype.card {rows : ι → RowSlice n d // E (fun i => rowSliceBoolRow (rows i))} : ℝ) =
          ∑ rows : ι → RowSlice n d, if E (fun i => rowSliceBoolRow (rows i)) then (1 : ℝ) else 0 := by
        rw [Fintype.card_subtype, ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hChoose : (n.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdn).ne'
      rw [uniformProbability, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_fun, card_rowSlice, hCount, bernoulliSliceMass, mul_pow, Nat.cast_pow]
      field_simp

theorem bernoulli_rows_slice_event_transfer {ι : Type*} [Fintype ι] {n d : ℕ}
    (hdn : d ≤ n) (p : ℝ≥0) (hp : p ≤ 1) (hMass : 0 < bernoulliSliceMass n d p)
    (E : (ι → Fin n → Bool) → Prop) :
    uniformProbability (fun rows : ι → RowSlice n d => E (fun i => rowSliceBoolRow (rows i))) ≤
      (Measure.pi (fun _ : ι => bernoulliCubeLaw (Fin n) p hp)).real {x | E x} /
        bernoulliSliceMass n d p ^ Fintype.card ι := by
  apply (le_div_iff₀ (pow_pos hMass _)).mpr
  rw [mul_comm, ← bernoulli_rows_slice_event_probability hdn]
  exact measureReal_mono (fun _ h => h.2)

theorem bernoulli_rows_slice_event_transfer_sqrt {ι : Type*} [Fintype ι] {n d : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) (E : (ι → Fin n → Bool) → Prop) :
    uniformProbability (fun rows : ι → RowSlice n d => E (fun i => rowSliceBoolRow (rows i))) ≤
      (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ Fintype.card ι *
        (Measure.pi (fun _ : ι => bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
          (rowBernoulliParameter_le_one (by omega) hdn))).real {x | E x} := by
  let K := 4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ)
  let p := rowBernoulliParameter n d
  let hp := rowBernoulliParameter_le_one (show 0 < n by omega) hdn
  have hK : 0 < K := by dsimp [K]; positivity
  have hMass := bernoulliSliceMass_pos hd hdn
  have hOne : 1 ≤ K * bernoulliSliceMass n d p := by
    have h := (div_le_iff₀ hK).mp (bernoulliSliceMass_lower hd hdn)
    nlinarith only [h]
  have hPower : 1 ≤ K ^ Fintype.card ι * bernoulliSliceMass n d p ^ Fintype.card ι := by
    rw [← mul_pow]
    exact one_le_pow₀ hOne
  apply (bernoulli_rows_slice_event_transfer hdn p hp hMass E).trans
  apply (div_le_iff₀ (pow_pos hMass _)).mpr
  have hScaled := mul_le_mul_of_nonneg_left hPower
    (measureReal_nonneg (μ := Measure.pi (fun _ : ι => bernoulliCubeLaw (Fin n) p hp))
      (s := {x | E x}))
  change _ ≤ K ^ Fintype.card ι * _ * _
  nlinarith only [hScaled]

end CircularLaw
