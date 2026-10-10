import CircularLaw.SourceGradualCoordinates
import CircularLaw.Discretization

/-!
# Full coordinate-range lemma for canonical gradual net points

The target makes the surrounding lower degree band and the two source
codimensions explicit. A common threshold applies to every degree in
the band, every gradual vector, every positive integer discretization
scale, and every sorting permutation. All finite rank and floor-stride
conditions are discharged from the band.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem canonicalApprox_norm_le {k : ℕ} (hk : 0 < k) (z : ℂ) :
    ‖canonicalApprox k z‖ ≤ ‖z‖ + Real.sqrt 2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hError : ‖z - canonicalApprox k z‖ ≤ Real.sqrt 2 :=
    (canonicalApprox_norm_error hk z).trans (div_le_self (Real.sqrt_nonneg _) hkR)
  calc
    _ = ‖z - (z - canonicalApprox k z)‖ := by congr 1; ring
    _ ≤ ‖z‖ + ‖z - canonicalApprox k z‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (le_refl _) hError

theorem source_gradual_canonical_coordinate_ranges {n d L k : ℕ} {a₃ : ℝ}
    (hn : 2 ≤ n) (hConditions : SourceKernelConditions n d)
    (hL : IsKernelCodimension n d L) (hCubic : 4 * d ≤ steepStride d ^ 3)
    (hk : 0 < k) (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    (∀ j : Fin n, ‖canonicalApprox k (x j)‖ ≤ 2 * (n : ℝ) ^ 6) ∧
      ∀ σ : Equiv.Perm (Fin n), Antitone (fun i => ‖x (σ i)‖) →
        ∀ j : Fin n, secondSteepScale n d ≤ j.val →
          ‖canonicalApprox k (x (σ j))‖ ≤ 2 * Real.rpow (d : ℝ) (3 / 2) := by
  have hd : 0 < d := by have h := hConditions.degree_large; omega
  have hSqrt : Real.sqrt 2 ≤ 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    norm_num [Real.sq_sqrt]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnSix : (2 : ℝ) ≤ (n : ℝ) ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnR 6
    norm_num at h
    linarith
  have hdR : (2 : ℝ) ≤ d := by
    have h := hConditions.degree_large
    exact_mod_cast (by omega : 2 ≤ d)
  have hdHalf : (2 : ℝ) ≤ Real.rpow (d : ℝ) (3 / 2) := by
    have hRoot : (1 : ℝ) ≤ Real.sqrt d := by
      apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt (Nat.cast_nonneg d)]
      linarith
    rw [degree_three_halves_eq hd]
    nlinarith
  constructor
  · intro j
    have hNorm := (norm_le_first_orderedNormAt (by omega : 0 < n) x j).trans
      (source_gradual_first_modulus hConditions hL hCubic x hx)
    exact (canonicalApprox_norm_le hk (x j)).trans (by linarith)
  · intro σ hσ j hj
    have hRanks := secondSteepScale_valid hd hConditions.dimension_root
    have hNorm := source_gradual_sorted_tail hRanks.1 hRanks.2 x hx σ hσ j hj
    exact (canonicalApprox_norm_le hk (x (σ j))).trans (by linarith)

theorem eventually_source_gradual_coordinate_ranges_uniform {C : ℝ} (hC : 0 < C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ a₃ : ℝ, ∀ k : ℕ, 0 < k →
        ∀ x ∈ sourceGradual n d L a₃,
          (∀ j : Fin n, ‖canonicalApprox k (x j)‖ ≤ 2 * (n : ℝ) ^ 6) ∧
            ∀ τ : Equiv.Perm (Fin n), Antitone (fun i => ‖x (τ i)‖) →
              ∀ j : Fin n, secondSteepScale n d ≤ j.val →
                ‖canonicalApprox k (x (τ j))‖ ≤ 2 * Real.rpow (d : ℝ) (3 / 2) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC eventually_steepStride_cubic] with n hn hConditions hCubic
  intro d hBand L hL a₃ k hk x hx
  exact source_gradual_canonical_coordinate_ranges hn (hConditions d hBand.1 hBand.2)
    hL (hCubic d hBand.1) hk x hx

/-- Lemma 5.1A, with the surrounding source assumptions explicit. The
proof holds for every positive integer `k`, hence in particular for all
the source discretization scales. Zero-based rank `j.val >= n2` is the
manuscript's one-based condition `j > n2`. -/
def CoordinateRangesLemma : Prop :=
  ∀ a₃ : ℝ, 0 < a₃ → a₃ < 1 / 2 → ∀ C : ℝ, 0 < C →
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ d : ℕ, InLowerBand C σ n d → ∀ L : ℕ, IsKernelCodimension n d L →
        ∀ k : ℕ, 0 < k → ∀ x ∈ sourceGradual n d L a₃,
          (∀ j : Fin n, ‖canonicalApprox k (x j)‖ ≤ 2 * (n : ℝ) ^ 6) ∧
            ∀ τ : Equiv.Perm (Fin n), Antitone (fun i => ‖x (τ i)‖) →
              ∀ j : Fin n, secondSteepScale n d ≤ j.val →
                ‖canonicalApprox k (x (τ j))‖ ≤ 2 * Real.rpow (d : ℝ) (3 / 2)

theorem coordinate_ranges_lemma : CoordinateRangesLemma := by
  intro a₃ _ _ C hC σ _ _
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_source_gradual_coordinate_ranges_uniform hC σ)
  refine ⟨N, ?_⟩
  intro n hn d hBand L hL k hk x hx
  exact hN n hn d hBand L hL a₃ k hk x hx

end CircularLaw
