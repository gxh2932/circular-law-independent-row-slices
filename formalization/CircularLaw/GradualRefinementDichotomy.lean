import CircularLaw.PlanarQuantileCohorts
import CircularLaw.SeparatedOrderDichotomy
import CircularLaw.SourceGradualNormalization

/-!
# Successive-scale dichotomy for the actual gradual class

The exact normalized gradual class excludes a disk containing more than
`n-n3` coordinates. Its canonical approximations therefore have the
separated cohorts required by the checked level argument. The resulting
spread-or-shrinking alternative has no cohort construction as a premise.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem almostConstantRadius_pos {d : ℕ} (hd : 0 < d) : 0 < almostConstantRadius d := by
  unfold almostConstantRadius
  exact div_pos (by norm_num) (pow_pos (by exact_mod_cast hd) _)

theorem source_gradual_no_center_count {n d L : ℕ} {a₃ : ℝ}
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) (c : ℂ) :
    (Finset.univ.filter (fun i => ‖x i - c‖ ≤ almostConstantRadius d)).card ≤
      n - thirdSteepScale n a₃ := by
  by_contra h
  apply hx.2.1
  refine ⟨c, ?_⟩
  change n - thirdSteepScale n a₃ <
    (Finset.univ.filter (fun i => ‖x i - c‖ ≤
      almostConstantRadius d * orderedNormAt x (thirdSteepScale n a₃))).card
  rw [hx.2.2, mul_one]
  omega

theorem source_gradual_separated_cohorts {n d L k : ℕ} {a₃ : ℝ}
    (hn : 2 ≤ n) (hd : 0 < d) (hr : 0 < thirdSteepScale n a₃)
    (hrn : thirdSteepScale n a₃ ≤ n) (hk : 0 < k)
    (hScale : 5 / almostConstantRadius d ≤ (k : ℝ))
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    ∃ I J : Finset (Fin n), Disjoint I J ∧
      (thirdSteepScale n a₃ : ℝ) / 4 ≤ I.card ∧
      (thirdSteepScale n a₃ : ℝ) / 4 ≤ J.card ∧
      ∀ i ∈ I, ∀ j ∈ J,
        almostConstantRadius d / 2 ≤ dist (canonicalApprox k (x i)) (canonicalApprox k (x j)) :=
  canonicalApprox_separated_cohorts hn hr hrn hk (almostConstantRadius_pos hd) hScale x
    (source_gradual_no_center_count x hx)

theorem gradual_refinement_scale_bounds {d u : ℕ} (hd : 3 ≤ d) (hu : 4 ≤ u) :
    5 / almostConstantRadius d ≤ (d ^ u : ℕ) ∧
      (d : ℝ) / (d ^ u : ℕ) ≤ almostConstantRadius d / 2 := by
  have hdPos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hdThree : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hθ := almostConstantRadius_pos hdPos
  have hPower : (d : ℝ) ^ 4 ≤ (d ^ u : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ d) hu
  have hIdentity : almostConstantRadius d * (d : ℝ) ^ 4 = 10 * (d : ℝ) := by
    unfold almostConstantRadius
    calc
      (10 / (d : ℝ) ^ 3) * (d : ℝ) ^ 4 =
          ((10 / (d : ℝ) ^ 3) * (d : ℝ) ^ 3) * (d : ℝ) := by ring
      _ = 10 * (d : ℝ) := by rw [div_mul_cancel₀ _ (pow_ne_zero 3 hdR.ne')]
  have hProduct : 10 * (d : ℝ) ≤ almostConstantRadius d * (d ^ u : ℕ) := by
    rw [← hIdentity]
    exact mul_le_mul_of_nonneg_left hPower hθ.le
  constructor
  · apply (div_le_iff₀ hθ).mpr
    nlinarith
  · have hkR : (0 : ℝ) < (d ^ u : ℕ) := by exact_mod_cast pow_pos hdPos u
    apply (div_le_iff₀ hkR).mpr
    nlinarith

theorem source_gradual_scale_separated_cohorts {n d L u : ℕ} {a₃ : ℝ}
    (hn : 2 ≤ n) (hd : 3 ≤ d) (hu : 4 ≤ u)
    (hr : 0 < thirdSteepScale n a₃) (hrn : thirdSteepScale n a₃ ≤ n)
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    ∃ I J : Finset (Fin n), Disjoint I J ∧
      (thirdSteepScale n a₃ : ℝ) / 4 ≤ I.card ∧
      (thirdSteepScale n a₃ : ℝ) / 4 ≤ J.card ∧
      ∀ i ∈ I, ∀ j ∈ J, (d : ℝ) / (d ^ u : ℕ) ≤
        dist (canonicalApprox (d ^ u) (x i)) (canonicalApprox (d ^ u) (x j)) := by
  have hdPos : 0 < d := by omega
  have hScale := gradual_refinement_scale_bounds hd hu
  obtain ⟨I, J, hDisjoint, hI, hJ, hSep⟩ := source_gradual_separated_cohorts hn hdPos hr hrn
    (pow_pos hdPos u) hScale.1 x hx
  exact ⟨I, J, hDisjoint, hI, hJ, fun i hi j hj => hScale.2.trans (hSep i hi j hj)⟩

theorem source_gradual_scale_high_or_spread {n d L u : ℕ} {a₃ : ℝ}
    (hn : 2 ≤ n) (hd : 3 ≤ d) (hu : 4 ≤ u)
    (hr : 0 < thirdSteepScale n a₃) (hrn : thirdSteepScale n a₃ ≤ n)
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    (thirdSteepScale n a₃ : ℝ) / 8 ≤
      (highCombinedHeightCoordinates (fun i => canonicalApprox (d ^ u) (x i))).card ∨
    (thirdSteepScale n a₃ : ℝ) / 120 ≤
      (spreadCoordinates (fun i => canonicalApprox (d ^ u) (x i))
        ((d : ℝ) / (d ^ u : ℕ))).card := by
  obtain ⟨I, J, _, hI, hJ, hSep⟩ := source_gradual_scale_separated_cohorts hn hd hu hr hrn x hx
  have hδ : 0 < (d : ℝ) / (d ^ u : ℕ) := div_pos
    (by exact_mod_cast (show 0 < d by omega))
    (by exact_mod_cast pow_pos (show 0 < d by omega) u)
  exact separated_cohorts_high_or_spread _ I J hδ hSep hI hJ

theorem source_gradual_scale_spread_or_shrinking {n d L u : ℕ} {a₃ : ℝ}
    (hn : 2 ≤ n) (hd : 3 ≤ d) (hu : 4 ≤ u)
    (hr : 0 < thirdSteepScale n a₃) (hrn : thirdSteepScale n a₃ ≤ n)
    (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃) :
    (thirdSteepScale n a₃ : ℝ) / 120 ≤
      (spreadCoordinates (fun i => canonicalApprox (d ^ u) (x i))
        ((d : ℝ) / (d ^ u : ℕ))).card ∨
    (thirdSteepScale n a₃ : ℝ) / 4608 ≤
      (spreadCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
        ((d : ℝ) / (d ^ (u + 1) : ℕ))).card ∨
    (thirdSteepScale n a₃ : ℝ) / 656 ≤
      (shrinkingCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
        (fun i => canonicalApprox (d ^ u) (x i))).card := by
  obtain ⟨I, J, _, hI, hJ, hSep⟩ := source_gradual_scale_separated_cohorts hn hd hu hr hrn x hx
  exact canonicalApprox_pow_cohorts_spread_or_shrinking (by omega) u x I J hSep hI hJ

end CircularLaw
