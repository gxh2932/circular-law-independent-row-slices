import CircularLaw.ClosedFloorCells
import CircularLaw.RepeatedValueWeight
import CircularLaw.SourceK1Product

/-!
# The exact low-weight tail from a source coordinate cluster

Every cluster of radius at most `d^(-v)` yields low-weight coordinate
probability at least `delta/36`, at the literal source cutoff
`floor(log_2(72*sqrt(d)/delta))`. No gradual or high-height premise is
needed for this part of the clustered-Pv conclusion.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem degree_negative_scale_eq_reciprocal (d v : ℕ) :
    Real.rpow (d : ℝ) (-(v : ℝ)) = 1 / (d ^ v : ℕ) := by
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hNeg : Real.rpow (d : ℝ) (-(v : ℝ)) = ((d : ℝ) ^ v)⁻¹ := by
    simpa only [Real.rpow_natCast] using Real.rpow_neg hdR (v : ℝ)
  simpa only [Nat.cast_pow, one_div] using hNeg

theorem source_cluster_low_weight_tail {n d v : ℕ} (hn : 0 < n) (hd : 0 < d)
    (x : Fin n → ℂ) (c : ℂ) {δ ρ : ℝ} (hδ : 0 < δ)
    (hρ : ρ ≤ Real.rpow (d : ℝ) (-(v : ℝ)))
    (hCluster : δ * n ≤ ((Finset.univ.filter (fun i => ‖x i - c‖ ≤ ρ)).card : ℝ)) :
    δ / 36 ≤ uniformProbability (fun i =>
      dyadicProfilePartOrder (sourceScaleProfile d v x) d ((sourceScaleProfile d v x).part i) ≤
        ⌊Real.logb 2 (72 * Real.sqrt d / δ)⌋) := by
  have hk : 0 < d ^ v := pow_pos hd _
  have hρScale : ρ ≤ 1 / (d ^ v : ℕ) := by
    rwa [degree_negative_scale_eq_reciprocal d] at hρ
  obtain ⟨z, hRepeat⟩ := canonicalApprox_repeated_from_cluster hk x c hρScale hCluster
  exact orderedCanonical_repeated_value_low_tail hn hd
    (fun i => canonicalApprox (d ^ v) (x i)) ((d : ℝ) / (d ^ v : ℕ)) z hδ hRepeat

end CircularLaw
