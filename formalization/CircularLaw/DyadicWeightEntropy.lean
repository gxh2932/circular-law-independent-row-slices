import CircularLaw.FiniteWeightEntropy
import CircularLaw.ProfileEstimator

/-!
# The actual dyadic row-profile weight law

The integer label is the floor of the base-two logarithm of the actual
truncated weight. Its real cast agrees with `dyadicWeight`, so the entropy
and cancellation results use the same dispersion as the averaged profile
bound, including coincident dyadic bins.
-/

noncomputable section
open scoped BigOperators ENNReal

namespace CircularLaw

def dyadicProfileLaw {α ι : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P : RowProfile α ι) (d : ℕ) : PMF ℤ :=
  uniformIntegerLaw (fun a => Int.floor (Real.logb 2 (truncatedProfileWeight P d (P.part a))))

theorem dyadicProfileLaw_apply {α ι : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P : RowProfile α ι) (d : ℕ) (j : ℤ) :
    dyadicProfileLaw P d j = ENNReal.ofReal (uniformProbability (fun a =>
      Int.floor (Real.logb 2 (truncatedProfileWeight P d (P.part a))) = j)) :=
  uniformIntegerLaw_apply _ j

theorem dyadicProfileLaw_dispersion {α ι : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P : RowProfile α ι) (d : ℕ) :
    integerDispersion (dyadicProfileLaw P d) = ENNReal.ofReal
      (pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) :=
  uniformIntegerLaw_dispersion _

theorem dyadic_profile_entropy_bound {α ι : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P : RowProfile α ι) (d : ℕ) :
    (∑' j : ℤ, integerEntropyAtom (dyadicProfileLaw P d) j) ≤
      weightEntropyConstant + Real.log (1 +
        pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) :=
  uniform_integer_entropy_bound _

theorem dyadic_profile_compression_cancel {α ι : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {c n K A M : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n) (hK : n / 2 ≤ K) (P : RowProfile α ι) (d : ℕ)
    (hCompression : M ≤ Real.exp (A * n +
      n * ∑' j : ℤ, integerEntropyAtom (dyadicProfileLaw P d) j)) :
    M * Real.exp (-c * K *
      pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) ≤
      Real.exp ((A + entropyPenaltyConstant (c / 2)) * n) :=
  uniform_integer_compression_cancel hc hn hK _ hCompression

end CircularLaw
