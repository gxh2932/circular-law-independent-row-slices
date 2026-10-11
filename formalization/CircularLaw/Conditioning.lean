import CircularLaw.MeasureModel

/-!
# Conditioning ordered samples to exact slices

Section 3 passes from independent sampling with replacement to independent
uniform slices. This file proves the finite fiber counts underlying that
passage, including the exact distinctness probability and conditioning cost.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

theorem uniformProbability_mono {α : Type*} [Fintype α] {E F : α → Prop}
    (h : ∀ x, E x → F x) : uniformProbability E ≤ uniformProbability F := by
  have hc : Nat.card {x // E x} ≤ Nat.card {x // F x} :=
    Nat.card_le_card_of_injective
      (fun x : {x // E x} => (⟨x.val, h x.val x.property⟩ : {x // F x}))
      (fun x y hxy => Subtype.ext (congrArg (fun z : {x // F x} => z.val) hxy))
  unfold uniformProbability
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

theorem uniformProbability_pos_of_card_pos {α : Type*} [Fintype α]
    (D : α → Prop) (hD : 0 < Nat.card {x // D x}) : 0 < uniformProbability D := by
  have hle : Nat.card {x // D x} ≤ Nat.card α :=
    Nat.card_le_card_of_injective Subtype.val Subtype.coe_injective
  unfold uniformProbability
  exact div_pos (by exact_mod_cast hD) (by exact_mod_cast lt_of_lt_of_le hD hle)

/-- Conditioning a finite uniform law gives the uniform law on the surviving
subtype. The conditioning event must have positive cardinality. -/
theorem uniformProbability_conditioning {α : Type*} [Fintype α]
    (D E : α → Prop) [DecidablePred D] (hD : 0 < Nat.card {x // D x}) :
    uniformProbability (fun x : {x // D x} => E x.val) =
      uniformProbability (fun x => D x ∧ E x) / uniformProbability D := by
  classical
  have hcard : Nat.card {x : {x // D x} // E x.val} =
      Nat.card {x // D x ∧ E x} :=
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter D E)
  have hle : Nat.card {x // D x} ≤ Nat.card α :=
    Nat.card_le_card_of_injective Subtype.val Subtype.coe_injective
  have hk : (Nat.card {x // D x} : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hα : (Nat.card α : ℝ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le hD hle).ne'
  simp only [uniformProbability, hcard]
  field_simp

theorem uniformProbability_conditioning_le {α : Type*} [Fintype α]
    (D E : α → Prop) [DecidablePred D] (hD : 0 < Nat.card {x // D x}) :
    uniformProbability (fun x : {x // D x} => E x.val) ≤
      uniformProbability E / uniformProbability D := by
  rw [uniformProbability_conditioning D E hD]
  exact div_le_div_of_nonneg_right (uniformProbability_mono (fun _ h => h.2))
    (uniformProbability_nonneg D)

theorem card_event_of_constant_fibers {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (m : ℕ) (hf : ∀ y, Nat.card {x // f x = y} = m)
    (event : β → Prop) :
    Nat.card {x // event (f x)} = m * Nat.card {y // event y} := by
  classical
  rw [← Nat.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype f (fun _ => Iff.rfl))]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hc (y : {y : β // event y}) : Fintype.card {x : α // f x = y.val} = m := by
    simpa only [Nat.card_eq_fintype_card] using hf y.val
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Nat.cast_id, mul_comm]

theorem uniformProbability_constant_fibers {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (m : ℕ) (hm : 0 < m) (hf : ∀ y, Nat.card {x // f x = y} = m)
    (event : β → Prop) :
    uniformProbability (fun x => event (f x)) = uniformProbability event := by
  have htotal : Nat.card α = m * Nat.card β := by
    have h := card_event_of_constant_fibers f m hf (fun _ => True)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype_true] using h
  rw [uniformProbability, uniformProbability, card_event_of_constant_fibers f m hf event,
    htotal, Nat.cast_mul, Nat.cast_mul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [mul_div_mul_left _ _ hm']

theorem uniformProbability_transfer_conditioning {α β : Type*} [Fintype α] [Fintype β]
    (D : α → Prop) (hD : 0 < Nat.card {x // D x})
    (f : {x // D x} → β) (m : ℕ) (hm : 0 < m)
    (hf : ∀ y, Nat.card {x // f x = y} = m)
    (E : β → Prop) (F : α → Prop) (hcompat : ∀ x, E (f x) ↔ F x.val) :
    uniformProbability E ≤ uniformProbability F / uniformProbability D := by
  classical
  rw [← uniformProbability_constant_fibers f m hm hf E]
  have he : (fun x : {x // D x} => E (f x)) = (fun x => F x.val) :=
    funext (fun x => propext (hcompat x))
  rw [he]
  exact uniformProbability_conditioning_le D F hD

def sliceOfEmbedding {n d : ℕ} (e : Fin d ↪ Fin n) : RowSlice n d :=
  ⟨Finset.univ.map e, by simp⟩

theorem sliceOfEmbedding_eq_iff {n d : ℕ} (e : Fin d ↪ Fin n) (s : RowSlice n d) :
    sliceOfEmbedding e = s ↔ ∀ a, e a ∈ s.val := by
  constructor
  · intro h a
    have hm : e a ∈ (sliceOfEmbedding e).val := Finset.mem_map.mpr
      ⟨a, Finset.mem_univ a, rfl⟩
    rwa [h] at hm
  · intro h
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨a, _, rfl⟩
      exact h a
    · simp only [sliceOfEmbedding, Finset.card_map, Finset.card_univ, Fintype.card_fin,
        s.property, le_refl]

def sliceEmbeddingFiberEquiv {n d : ℕ} (s : RowSlice n d) :
    {e : Fin d ↪ Fin n // sliceOfEmbedding e = s} ≃ (Fin d ↪ ↥s.val) :=
  (Equiv.subtypeEquivRight (fun e => sliceOfEmbedding_eq_iff e s)).trans
    (Equiv.codRestrict (Fin d) (s.val : Set (Fin n)))

theorem card_sliceEmbedding_fiber {n d : ℕ} (s : RowSlice n d) :
    Nat.card {e : Fin d ↪ Fin n // sliceOfEmbedding e = s} = d.factorial := by
  rw [Nat.card_congr (sliceEmbeddingFiberEquiv s), Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, Fintype.card_coe, s.property, Fintype.card_fin,
    Nat.descFactorial_self]

theorem uniform_embedding_support {n d : ℕ} (event : RowSlice n d → Prop) :
    uniformProbability (fun e : Fin d ↪ Fin n => event (sliceOfEmbedding e)) =
      uniformProbability event :=
  uniformProbability_constant_fibers sliceOfEmbedding d.factorial (Nat.factorial_pos d)
    card_sliceEmbedding_fiber event

theorem ordered_distinct_probability (n d : ℕ) :
    uniformProbability (fun samples : Fin d → Fin n => Function.Injective samples) =
      (n.descFactorial d : ℝ) / (n : ℝ) ^ d := by
  rw [uniformProbability,
    Nat.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin d) (Fin n))]
  simp only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_fun, Nat.cast_pow]

abbrev OrderedRows (n d K : ℕ) := Fin K → (Fin d → Fin n)

def distinctRows {n d K : ℕ} (samples : OrderedRows n d K) : Prop :=
  ∀ i, Function.Injective (samples i)

def distinctRowsEquiv (n d K : ℕ) :
    {samples : OrderedRows n d K // distinctRows samples} ≃ (Fin K → (Fin d ↪ Fin n)) :=
  (Equiv.subtypePiEquivPi (p := fun _ : Fin K =>
    fun samples : Fin d → Fin n => Function.Injective samples)).trans
      (Equiv.piCongrRight (fun _ => Equiv.subtypeInjectiveEquivEmbedding (Fin d) (Fin n)))

def slicesOfDistinctRows {n d K : ℕ}
    (samples : {samples : OrderedRows n d K // distinctRows samples}) : Fin K → RowSlice n d :=
  fun i => sliceOfEmbedding (distinctRowsEquiv n d K samples i)

theorem card_ordered_matrix_support_fiber {n d K : ℕ} (s : Fin K → RowSlice n d) :
    Nat.card {e : Fin K → (Fin d ↪ Fin n) // (fun i => sliceOfEmbedding (e i)) = s} =
      d.factorial ^ K := by
  classical
  let e := (Equiv.subtypeEquivRight (fun x : Fin K → (Fin d ↪ Fin n) =>
    (funext_iff : (fun i => sliceOfEmbedding (x i)) = s ↔
      ∀ i, sliceOfEmbedding (x i) = s i))).trans
        (Equiv.subtypePiEquivPi (p := fun i x => sliceOfEmbedding x = s i))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi]
  have hc (i : Fin K) : Fintype.card {x : Fin d ↪ Fin n // sliceOfEmbedding x = s i} =
      d.factorial := by
    simpa only [Nat.card_eq_fintype_card] using card_sliceEmbedding_fiber (s i)
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_distinct_rows_support_fiber {n d K : ℕ} (s : Fin K → RowSlice n d) :
    Nat.card {x : {samples : OrderedRows n d K // distinctRows samples} //
      slicesOfDistinctRows x = s} = d.factorial ^ K := by
  unfold slicesOfDistinctRows
  rw [Nat.card_congr ((distinctRowsEquiv n d K).subtypeEquivOfSubtype
    (p := fun e => (fun i => sliceOfEmbedding (e i)) = s))]
  exact card_ordered_matrix_support_fiber s

theorem card_distinct_rows (n d K : ℕ) :
    Nat.card {samples : OrderedRows n d K // distinctRows samples} =
      (n.descFactorial d) ^ K := by
  rw [Nat.card_congr (distinctRowsEquiv n d K)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_embedding_eq,
    Fintype.card_fin]

theorem distinct_rows_probability (n d K : ℕ) :
    uniformProbability (fun samples : OrderedRows n d K => distinctRows samples) =
      ((n.descFactorial d : ℝ) / (n : ℝ) ^ d) ^ K := by
  unfold distinctRows
  rw [uniformProbability_pi (fun _ : Fin K =>
    fun samples : Fin d → Fin n => Function.Injective samples)]
  simp only [ordered_distinct_probability, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The exact Section 3 conditioning inequality, for arbitrary events on
`K` independent rows, with an explicit compatibility condition for their
with-replacement interpretation on the distinct-sampling event. -/
theorem condition_to_slice {n d K : ℕ} (hdn : d ≤ n)
    (E : (Fin K → RowSlice n d) → Prop) (F : OrderedRows n d K → Prop)
    (hcompat : ∀ samples : {samples : OrderedRows n d K // distinctRows samples},
      E (slicesOfDistinctRows samples) ↔ F samples.val) :
    uniformProbability E ≤ ((n : ℝ) ^ d / (n.descFactorial d : ℝ)) ^ K *
      uniformProbability F := by
  have hD : 0 < Nat.card {samples : OrderedRows n d K // distinctRows samples} := by
    rw [card_distinct_rows]
    exact pow_pos (Nat.descFactorial_pos.mpr hdn) K
  have h := uniformProbability_transfer_conditioning distinctRows hD slicesOfDistinctRows
    (d.factorial ^ K) (pow_pos (Nat.factorial_pos d) K)
      card_distinct_rows_support_fiber E F hcompat
  rw [distinct_rows_probability] at h
  convert h using 1
  simp only [div_eq_mul_inv, ← inv_pow, mul_inv_rev, inv_inv]
  ring

def withReplacementMatrix {n d K : ℕ} (samples : OrderedRows n d K) :
    Matrix (Fin K) (Fin n) ℂ :=
  fun i j => ∑ a : Fin d, if samples i a = j then 1 else 0

def sliceRectangularMatrix {n d K : ℕ} (s : Fin K → RowSlice n d) :
    Matrix (Fin K) (Fin n) ℂ := fun i j => rowEntry (s i) j

theorem embedding_coordinate_count {n d : ℕ} (e : Fin d ↪ Fin n) (j : Fin n) :
    (∑ a : Fin d, if e a = j then (1 : ℂ) else 0) = rowEntry (sliceOfEmbedding e) j := by
  classical
  have hsum : (∑ a : Fin d, if e a = j then (1 : ℂ) else 0) =
      ∑ k ∈ Finset.univ.map e, if k = j then (1 : ℂ) else 0 := by
    rw [Finset.sum_map]
  rw [hsum]
  simp only [Finset.sum_ite_eq', rowEntry, sliceOfEmbedding]

theorem withReplacementMatrix_eq_slice {n d K : ℕ}
    (samples : {samples : OrderedRows n d K // distinctRows samples}) :
    withReplacementMatrix samples.val = sliceRectangularMatrix (slicesOfDistinctRows samples) := by
  ext i j
  exact embedding_coordinate_count (distinctRowsEquiv n d K samples i) j

/-- The conditioning estimate for actual matrix events: compatibility of the
with-replacement and slice matrices is proved rather than assumed. -/
theorem condition_matrix_event_to_slice {n d K : ℕ} (hdn : d ≤ n)
    (E : Matrix (Fin K) (Fin n) ℂ → Prop) :
    uniformProbability (fun s : Fin K → RowSlice n d => E (sliceRectangularMatrix s)) ≤
      ((n : ℝ) ^ d / (n.descFactorial d : ℝ)) ^ K *
        uniformProbability (fun samples : OrderedRows n d K => E (withReplacementMatrix samples)) := by
  apply condition_to_slice hdn
  intro samples
  rw [withReplacementMatrix_eq_slice]

theorem conditioning_ratio_product {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    (n : ℝ) ^ d / (n.descFactorial d : ℝ) =
      ∏ j ∈ Finset.range d, (1 - (j : ℝ) / n)⁻¹ := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hterm (j : ℕ) (hj : j ∈ Finset.range d) :
      (n : ℝ) / (n - j : ℕ) = (1 - (j : ℝ) / n)⁻¹ := by
    have hjn : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hdn
    have hnj : (n : ℝ) - j ≠ 0 := by
      have : (j : ℝ) < n := by exact_mod_cast hjn
      linarith
    rw [Nat.cast_sub hjn.le]
    field_simp
  calc
    _ = (∏ j ∈ Finset.range d, (n : ℝ)) / ∏ j ∈ Finset.range d, (n - j : ℕ) := by
      rw [Finset.prod_const, Finset.card_range, ← Nat.descFactorial_eq_prod_range]
    _ = ∏ j ∈ Finset.range d, (n : ℝ) / (n - j : ℕ) := by
      rw [Nat.cast_prod, Finset.prod_div_distrib]
    _ = _ := Finset.prod_congr rfl hterm

theorem conditioning_log_ratio {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    Real.log ((n : ℝ) ^ d / (n.descFactorial d : ℝ)) =
      ∑ j ∈ Finset.range d, -Real.log (1 - (j : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [conditioning_ratio_product hn hdn, Real.log_prod]
  · simp only [Real.log_inv]
  · intro j hj
    have hjn : (j : ℝ) < n := by
      exact_mod_cast lt_of_lt_of_le (Finset.mem_range.mp hj) hdn
    exact inv_ne_zero (ne_of_gt (sub_pos.mpr ((div_lt_one hn').mpr hjn)))

theorem neg_log_one_sub_le_two_mul {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  apply h.trans
  apply (sub_le_iff_le_add).mpr
  apply (inv_le_iff_one_le_mul₀ hpos).mpr
  nlinarith

/-- A fully quantitative version of the `O(K*d^2/n)` conditioning cost. -/
theorem conditioning_log_cost {n d K : ℕ} (hn : 0 < n) (hdn : 2 * d ≤ n) :
    (K : ℝ) * Real.log ((n : ℝ) ^ d / (n.descFactorial d : ℝ)) ≤
      2 * K * (d : ℝ) ^ 2 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdhalf : (d : ℝ) / n ≤ 1 / 2 := by
    rw [div_le_iff₀ hn']
    have : (2 : ℝ) * d ≤ n := by exact_mod_cast hdn
    linarith
  have hlog : Real.log ((n : ℝ) ^ d / (n.descFactorial d : ℝ)) ≤
      2 * (d : ℝ) ^ 2 / n := by
    rw [conditioning_log_ratio hn (by omega)]
    calc
      _ ≤ ∑ _j ∈ Finset.range d, 2 * ((d : ℝ) / n) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjd : (j : ℝ) ≤ d := by exact_mod_cast (Finset.mem_range.mp hj).le
        have hjdiv := div_le_div_of_nonneg_right hjd hn'.le
        exact (neg_log_one_sub_le_two_mul (by positivity) (hjdiv.trans hdhalf)).trans
          (mul_le_mul_of_nonneg_left hjdiv (by norm_num))
      _ = 2 * (d : ℝ) ^ 2 / n := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg K)
  convert h using 1; ring

theorem conditioning_factor_le_exp {n d K : ℕ} (hn : 0 < n) (hdn : 2 * d ≤ n) :
    ((n : ℝ) ^ d / (n.descFactorial d : ℝ)) ^ K ≤
      Real.exp (2 * K * (d : ℝ) ^ 2 / n) := by
  have hpos : 0 < (n : ℝ) ^ d / (n.descFactorial d : ℝ) :=
    div_pos (pow_pos (by exact_mod_cast hn) d)
      (by exact_mod_cast Nat.descFactorial_pos.mpr (by omega : d ≤ n))
  calc
    _ = Real.exp ((K : ℝ) * Real.log ((n : ℝ) ^ d / (n.descFactorial d : ℝ))) := by
      rw [Real.exp_nat_mul, Real.exp_log hpos]
    _ ≤ _ := Real.exp_le_exp.mpr (conditioning_log_cost hn hdn)

theorem condition_matrix_event_to_slice_exp {n d K : ℕ} (hn : 0 < n) (hdn : 2 * d ≤ n)
    (E : Matrix (Fin K) (Fin n) ℂ → Prop) :
    uniformProbability (fun s : Fin K → RowSlice n d => E (sliceRectangularMatrix s)) ≤
      Real.exp (2 * K * (d : ℝ) ^ 2 / n) *
        uniformProbability (fun samples : OrderedRows n d K => E (withReplacementMatrix samples)) :=
  (condition_matrix_event_to_slice (by omega : d ≤ n) E).trans
    (mul_le_mul_of_nonneg_right (conditioning_factor_le_exp hn hdn)
      (uniformProbability_nonneg _))

end CircularLaw
