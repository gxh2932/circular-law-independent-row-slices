import CircularLaw.BernoulliCenteringDistribution

/-!
# Clipped mean distances for one-index interlaced arrays

For two nonnegative descending arrays with both one-index interlacings,
the sum of their pointwise distances is at most the sum of their first
entries. Clipping to a fixed interval therefore bounds the normalized
distance by twice the interval radius divided by dimension. These
deterministic estimates apply to the actual Bernoulli centering.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem interlaced_array_distance_sum_bound {n : ℕ} (a b : Fin (n + 1) → ℝ)
    (ha : Antitone a) (hb : Antitone b) (haNonneg : ∀ i, 0 ≤ a i) (hbNonneg : ∀ i, 0 ≤ b i)
    (hAB : ∀ i : Fin n, a i.succ ≤ b i.castSucc)
    (hBA : ∀ i : Fin n, b i.succ ≤ a i.castSucc) :
    (∑ i, |a i - b i|) ≤ a 0 + b 0 := by
  have hPoint (i : Fin n) : |a i.castSucc - b i.castSucc| ≤
      (a i.castSucc - a i.succ) + (b i.castSucc - b i.succ) := by
    have hi : i.castSucc ≤ i.succ := by exact_mod_cast Nat.le_succ i.val
    have hA := ha hi
    have hB := hb hi
    have h1 := hAB i
    have h2 := hBA i
    by_cases h : a i.castSucc ≤ b i.castSucc
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
      linarith
  have hSum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hPoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hSum
  have hA : (∑ i : Fin n, a i.castSucc) + a (Fin.last n) = a 0 + ∑ i : Fin n, a i.succ := by
    rw [← Fin.sum_univ_castSucc, ← Fin.sum_univ_succ]
  have hB : (∑ i : Fin n, b i.castSucc) + b (Fin.last n) = b 0 + ∑ i : Fin n, b i.succ := by
    rw [← Fin.sum_univ_castSucc, ← Fin.sum_univ_succ]
  have hLast : |a (Fin.last n) - b (Fin.last n)| ≤ a (Fin.last n) + b (Fin.last n) := by
    have h := abs_sub_le (a (Fin.last n)) 0 (b (Fin.last n))
    simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (haNonneg _),
      abs_of_nonneg (hbNonneg _)] using h
  rw [Fin.sum_univ_castSucc]
  linarith

theorem clipped_interlaced_array_mean_distance_bound {n : ℕ} (a b : Fin n → ℝ)
    (ha : Antitone a) (hb : Antitone b) (haNonneg : ∀ i, 0 ≤ a i) (hbNonneg : ∀ i, 0 ≤ b i)
    (hAB : ∀ i j : Fin n, j.val = i.val + 1 → a j ≤ b i)
    (hBA : ∀ i j : Fin n, j.val = i.val + 1 → b j ≤ a i)
    (S : ℝ) (hS : 0 ≤ S) :
    finiteMean (fun i => |min (a i) S - min (b i) S|) ≤ 2 * S / n := by
  cases n with
  | zero => simp [finiteMean]
  | succ n =>
    have hClipA : Antitone (fun i => min (a i) S) := fun _ _ h => min_le_min (ha h) le_rfl
    have hClipB : Antitone (fun i => min (b i) S) := fun _ _ h => min_le_min (hb h) le_rfl
    have h := interlaced_array_distance_sum_bound (fun i => min (a i) S) (fun i => min (b i) S)
      hClipA hClipB (fun i => le_min (haNonneg i) hS) (fun i => le_min (hbNonneg i) hS)
      (fun i => min_le_min (hAB i.castSucc i.succ rfl) le_rfl)
      (fun i => min_le_min (hBA i.castSucc i.succ rfl) le_rfl)
    have hTotal : (∑ i, |min (a i) S - min (b i) S|) ≤ 2 * S :=
      h.trans (by nlinarith [min_le_right (a 0) S, min_le_right (b 0) S])
    rw [finiteMean, Fintype.card_fin]
    exact div_le_div_of_nonneg_right hTotal (by positivity)

theorem bernoulli_centering_clipped_mean_distance_bound {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) (S : ℝ) (hS : 0 ≤ S) :
    finiteMean (fun i =>
      |min (orderedSquareSingularValues (normalizedShiftedBernoulliMatrix d z x) i) S -
        min (orderedSquareSingularValues (normalizedCenteredBernoulliMatrix d x - z • 1) i) S|) ≤
          2 * S / n := by
  apply clipped_interlaced_array_mean_distance_bound _ _
    (orderedSquareSingularValues_antitone _) (orderedSquareSingularValues_antitone _)
    (orderedSquareSingularValues_nonneg _) (orderedSquareSingularValues_nonneg _)
    (fun i j h => (bernoulli_centering_singular_values_interlace d z x i j h).1)
    (fun i j h => (bernoulli_centering_singular_values_interlace d z x i j h).2) S hS

end CircularLaw
