import CircularLaw.MultinomialEntropy
import CircularLaw.FiniteWeightEntropy

/-!
# Integer histograms of uniform coordinates

The occupied bins, their exact counts, and their total mass come from the
actual coordinate map. The histogram entropy exponent is exactly dimension
times the entropy of the pushforward law, with coincident bins aggregated.
-/

noncomputable section
open Classical
open scoped BigOperators Nat ENNReal

namespace CircularLaw

def integerHistogramSupport {α : Type*} [Fintype α] (B : α → ℤ) : Finset ℤ :=
  Finset.univ.image B

def integerHistogram {α : Type*} [Fintype α] (B : α → ℤ) (j : ℤ) : ℕ :=
  Nat.card {a : α // B a = j}

theorem integerHistogram_eq_filter_card {α : Type*} [Fintype α] (B : α → ℤ) (j : ℤ) :
    integerHistogram B j = (Finset.univ.filter (fun a => B a = j)).card := by
  simp only [integerHistogram, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem integerHistogram_ne_zero_iff {α : Type*} [Fintype α] (B : α → ℤ) (j : ℤ) :
    integerHistogram B j ≠ 0 ↔ j ∈ integerHistogramSupport B := by
  rw [integerHistogram_eq_filter_card]
  exact Finset.fiber_card_ne_zero_iff_mem_image Finset.univ B j

theorem integerHistogram_total {α : Type*} [Fintype α] (B : α → ℤ) :
    (∑ j ∈ integerHistogramSupport B, integerHistogram B j) = Fintype.card α := by
  simp only [integerHistogram_eq_filter_card]
  have hMaps : ∀ a ∈ (Finset.univ : Finset α), B a ∈ integerHistogramSupport B :=
    fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  exact (Finset.card_eq_sum_card_fiberwise hMaps).symm

theorem integerHistogram_zero_off_support {α : Type*} [Fintype α] (B : α → ℤ)
    {j : ℤ} (hj : j ∉ integerHistogramSupport B) : integerHistogram B j = 0 := by
  by_contra h
  exact hj ((integerHistogram_ne_zero_iff B j).mp h)

theorem uniformIntegerLaw_toReal_histogram {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ) (j : ℤ) :
    (uniformIntegerLaw B j).toReal = (integerHistogram B j : ℝ) / Fintype.card α := by
  rw [uniformIntegerLaw_apply,
    ENNReal.toReal_ofReal (uniformProbability_nonneg (fun a => B a = j))]
  simp only [uniformProbability, integerHistogram, Nat.card_eq_fintype_card]

theorem uniformIntegerLaw_entropy_atom_off_support {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ)
    {j : ℤ} (hj : j ∉ integerHistogramSupport B) :
    integerEntropyAtom (uniformIntegerLaw B) j = 0 := by
  rw [integerEntropyAtom, uniformIntegerLaw_toReal_histogram,
    integerHistogram_zero_off_support B hj]
  simp only [Nat.cast_zero, zero_div, neg_zero, zero_mul]

theorem uniformIntegerLaw_entropy_eq_histogram_sum {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ) :
    (∑' j : ℤ, integerEntropyAtom (uniformIntegerLaw B) j) =
      ∑ j ∈ integerHistogramSupport B, integerEntropyAtom (uniformIntegerLaw B) j :=
  tsum_eq_sum (fun _ hj => uniformIntegerLaw_entropy_atom_off_support B hj)

theorem multinomialEntropyExponent_eq_uniform_entropy {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ) :
    multinomialEntropyExponent (integerHistogramSupport B) (integerHistogram B) =
      (Fintype.card α : ℝ) * (∑' j : ℤ, integerEntropyAtom (uniformIntegerLaw B) j) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [multinomialEntropyExponent, integerHistogram_total,
    uniformIntegerLaw_entropy_eq_histogram_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [integerEntropyAtom, uniformIntegerLaw_toReal_histogram]
  field_simp

theorem integer_histogram_factorial_entropy {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ) :
    ((Fintype.card α)! : ℝ) /
        (∏ j ∈ integerHistogramSupport B, ((integerHistogram B j)! : ℝ)) ≤
      Real.exp ((Fintype.card α : ℝ) *
        (∑' j : ℤ, integerEntropyAtom (uniformIntegerLaw B) j)) := by
  have h := factorial_ratio_le_entropy (integerHistogramSupport B) (integerHistogram B)
    (fun j hj => (integerHistogram_ne_zero_iff B j).mp hj)
  rwa [integerHistogram_total, multinomialEntropyExponent_eq_uniform_entropy] at h

theorem integer_histogram_factorial_cancel {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {c K : ℝ}
    (hc : 0 < c) (hK : (Fintype.card α : ℝ) / 2 ≤ K) (B : α → ℤ) :
    (((Fintype.card α)! : ℝ) /
      (∏ j ∈ integerHistogramSupport B, ((integerHistogram B j)! : ℝ))) *
        Real.exp (-c * K * pairDispersion (fun a => (B a : ℝ))) ≤
      Real.exp (entropyPenaltyConstant (c / 2) * Fintype.card α) := by
  have h := uniform_integer_compression_cancel (A := 0) hc (Nat.cast_nonneg _) hK B
    (by simpa only [zero_mul, zero_add] using integer_histogram_factorial_entropy B)
  simpa only [zero_add] using h

end CircularLaw
