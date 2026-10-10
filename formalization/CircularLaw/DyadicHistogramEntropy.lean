import CircularLaw.IntegerHistogram
import CircularLaw.DyadicWeightEntropy

/-!
# Factorial entropy for the actual dyadic profile histogram

The bins are exactly the source intervals `[2^b,2^(b+1))` of the truncated
profile weights. The factorial ratio for these bin sizes is bounded by
dimension times the entropy of the same law used by the row-profile bound.
-/

noncomputable section
open Classical
open scoped BigOperators Nat ENNReal

namespace CircularLaw

theorem dyadic_order_floor_iff {w : ℝ} (hw : 0 < w) (b : ℤ) :
    Int.floor (Real.logb 2 w) = b ↔ (2 : ℝ) ^ b ≤ w ∧ w < (2 : ℝ) ^ (b + 1) := by
  rw [Int.floor_eq_iff, Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hw,
    Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hw, Real.rpow_intCast]
  rw [show (b : ℝ) + 1 = ((b + 1 : ℤ) : ℝ) by norm_cast, Real.rpow_intCast]

def dyadicProfileHistogramSupport {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (d : ℕ) : Finset ℤ :=
  integerHistogramSupport (fun a => Int.floor (Real.logb 2 (truncatedProfileWeight P d (P.part a))))

def dyadicProfileHistogram {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (d : ℕ) (b : ℤ) : ℕ :=
  integerHistogram (fun a => Int.floor (Real.logb 2 (truncatedProfileWeight P d (P.part a)))) b

theorem dyadicProfileHistogram_eq_source_bin {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) (b : ℤ) :
    dyadicProfileHistogram P d b = Nat.card {a : α //
      (2 : ℝ) ^ b ≤ truncatedProfileWeight P d (P.part a) ∧
        truncatedProfileWeight P d (P.part a) < (2 : ℝ) ^ (b + 1)} := by
  have hPred : (fun a : α => Int.floor (Real.logb 2 (truncatedProfileWeight P d (P.part a))) = b) =
      (fun a : α => (2 : ℝ) ^ b ≤ truncatedProfileWeight P d (P.part a) ∧
        truncatedProfileWeight P d (P.part a) < (2 : ℝ) ^ (b + 1)) := by
    funext a
    exact propext (dyadic_order_floor_iff (truncatedProfileWeight_pos P hd (P.part a)) b)
  change Nat.card {a : α // (fun a =>
    Int.floor (Real.logb 2 (truncatedProfileWeight P d (P.part a))) = b) a} = _
  rw [hPred]

theorem dyadicProfileHistogram_total {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (d : ℕ) :
    (∑ b ∈ dyadicProfileHistogramSupport P d, dyadicProfileHistogram P d b) = Fintype.card α :=
  integerHistogram_total _

theorem dyadicProfileLaw_histogram_mass {α ι : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P : RowProfile α ι) (d : ℕ) (b : ℤ) :
    (dyadicProfileLaw P d b).toReal = (dyadicProfileHistogram P d b : ℝ) / Fintype.card α :=
  uniformIntegerLaw_toReal_histogram _ b

theorem dyadic_histogram_factorial_entropy {α ι : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P : RowProfile α ι) (d : ℕ) :
    ((Fintype.card α)! : ℝ) /
        (∏ b ∈ dyadicProfileHistogramSupport P d, ((dyadicProfileHistogram P d b)! : ℝ)) ≤
      Real.exp ((Fintype.card α : ℝ) *
        (∑' b : ℤ, integerEntropyAtom (dyadicProfileLaw P d) b)) :=
  integer_histogram_factorial_entropy _

theorem dyadic_histogram_factorial_cancel {α ι : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {c K : ℝ}
    (hc : 0 < c) (hK : (Fintype.card α : ℝ) / 2 ≤ K) (P : RowProfile α ι) (d : ℕ) :
    (((Fintype.card α)! : ℝ) /
      (∏ b ∈ dyadicProfileHistogramSupport P d, ((dyadicProfileHistogram P d b)! : ℝ))) *
        Real.exp (-c * K *
          pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) ≤
      Real.exp (entropyPenaltyConstant (c / 2) * Fintype.card α) :=
  integer_histogram_factorial_cancel hc hK _

end CircularLaw
