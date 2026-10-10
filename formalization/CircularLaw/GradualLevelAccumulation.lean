import CircularLaw.SourceRefinementFamilies
import CircularLaw.AccumulatedShrinkage

/-!
# Many small final levels for vectors avoiding the spread families

The one-step gradual dichotomy is accumulated over the actual canonical
scales `d^(4+t)`. A fixed positive fraction of `n3` coordinates has final
level size at most `n*2^(-a3*T/5248)`. No shrinking count, independence,
or cohort condition is an additional premise.
-/

noncomputable section
open Classical

namespace CircularLaw

def gradualLevelSize {n : ℕ} (d : ℕ) (x : Fin n → ℂ) (t : ℕ) (i : Fin n) : ℕ :=
  (initialLevel (fun j => canonicalApprox (d ^ (4 + t)) (x j))
    (canonicalApprox (d ^ (4 + t)) (x i))).card

theorem gradualLevelSize_succ_le {n d : ℕ} (hd : 0 < d) (x : Fin n → ℂ)
    (t : ℕ) (i : Fin n) : gradualLevelSize d x (t + 1) i ≤ gradualLevelSize d x t i := by
  simpa only [gradualLevelSize, Nat.add_assoc] using
    canonicalApprox_pow_initialLevel_card_le hd (4 + t) x i

theorem gradualLevelSize_initial_le {n : ℕ} (d : ℕ) (x : Fin n → ℂ) (i : Fin n) :
    gradualLevelSize d x 0 i ≤ n :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

theorem gradualLevelSize_shrinkingAt {n : ℕ} (d : ℕ) (x : Fin n → ℂ) (t : ℕ) :
    shrinkingAt (gradualLevelSize d x) t =
      shrinkingCoordinates (fun i => canonicalApprox (d ^ (4 + t + 1)) (x i))
        (fun i => canonicalApprox (d ^ (4 + t)) (x i)) := by
  simp only [shrinkingAt, gradualLevelSize, shrinkingCoordinates, Nat.add_assoc]

theorem source_gradual_many_small_levels {n d L T : ℕ} {a₃ cK : ℝ}
    (hn : 2 ≤ n) (hd : 3 ≤ d) (hT : 0 < T)
    (hr : 0 < thirdSteepScale n a₃) (hrn : thirdSteepScale n a₃ ≤ n)
    (hThirdLower : a₃ * (n : ℝ) / 2 ≤ thirdSteepScale n a₃)
    (hc : cK ≤ 1 / 4608) (x : Fin n → ℂ) (hx : x ∈ sourceGradual n d L a₃)
    (hAvoid : ∀ u : ℕ, 4 ≤ u → u ≤ 4 + T → x ∉ sourceSpreadFamily n d L a₃ cK u) :
    ∃ G : Finset (Fin n), 3 * (thirdSteepScale n a₃ : ℝ) / 2624 ≤ G.card ∧
      ∀ i ∈ G,
        ((initialLevel (fun j => canonicalApprox (d ^ (4 + T)) (x j))
          (canonicalApprox (d ^ (4 + T)) (x i))).card : ℝ) ≤
          (n : ℝ) * Real.rpow 2 (-(a₃ * (T : ℝ) / 5248)) := by
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hdPos : 0 < d := by omega
  let B : ℝ := (thirdSteepScale n a₃ : ℝ) / 656
  have hB : 0 ≤ B := div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hCount : ∀ t < T, B ≤ (shrinkingAt (gradualLevelSize d x) t).card := by
    intro t ht
    rw [gradualLevelSize_shrinkingAt]
    exact source_gradual_shrinking_of_not_families hn hd (by omega) hr hrn hc x hx
      (hAvoid (4 + t) (by omega) (by omega)) (hAvoid (4 + t + 1) (by omega) (by omega))
  let G := largeWitnessRows (coordinateShrinkCount (gradualLevelSize d x) T)
    (B / (4 * (n : ℝ)) * T)
  have hMany := many_coordinates_shrink hnPos hT (gradualLevelSize d x) hB hCount
  refine ⟨G, by dsimp only [G]; dsimp only [B] at hMany; linarith, ?_⟩
  intro i hi
  have hContract := many_shrinking_coordinate_contraction (gradualLevelSize d x)
    (gradualLevelSize_succ_le hdPos x) (gradualLevelSize_initial_le d x) i hi
  have hBase : a₃ / 5248 ≤ B / (4 * (n : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ))).mpr
    dsimp only [B]
    nlinarith
  have hThreshold : a₃ * (T : ℝ) / 5248 ≤ B / (4 * (n : ℝ)) * T := by
    have h := mul_le_mul_of_nonneg_right hBase (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
    nlinarith
  apply hContract.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end CircularLaw
