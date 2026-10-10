import CircularLaw.SqrtHeightCutoff
import CircularLaw.SourceClusterLowTail
import CircularLaw.GradualDecomposition

/-!
# The upper weight population in the literal Pv family

The actual high-height mass and the checked small-bin estimate give an
upper tail at height threshold divided by `d*sqrt(cP*a3)`. This stronger
cutoff retains the manuscript's separation hypothesis and all integer
rounding. Its degree threshold is independent of the scale `v`.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def sourcePvHighWeightCutoff (a₃ cP : ℝ) (d v : ℕ) : ℝ :=
  sourceHeightThreshold a₃ cP v / ((d : ℝ) * Real.sqrt (cP * a₃))

theorem sourceHeightThreshold_pos {a₃ cP : ℝ} (ha : 0 < a₃) (hc : 0 < cP) (v : ℕ) :
    0 < sourceHeightThreshold a₃ cP v :=
  mul_pos (mul_pos hc ha) (Real.rpow_pos_of_pos (by norm_num) _)

theorem sourceHeightThreshold_logb {a₃ cP : ℝ} (ha : 0 < a₃) (hc : 0 < cP) (v : ℕ) :
    Real.logb 2 (sourceHeightThreshold a₃ cP v) =
      Real.logb 2 (cP * a₃) + cP * ((v : ℝ) - 4) * a₃ := by
  have hPower : Real.logb 2 (Real.rpow 2 (cP * ((v : ℝ) - 4) * a₃)) =
      cP * ((v : ℝ) - 4) * a₃ := by
    rw [Real.rpow_eq_pow]
    exact Real.logb_rpow (by norm_num) (by norm_num)
  unfold sourceHeightThreshold
  have hPositive : 0 < Real.rpow 2 (cP * ((v : ℝ) - 4) * a₃) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hMul : Real.logb 2 (cP * a₃ * Real.rpow 2 (cP * ((v : ℝ) - 4) * a₃)) =
      Real.logb 2 (cP * a₃) + Real.logb 2 (Real.rpow 2 (cP * ((v : ℝ) - 4) * a₃)) :=
    Real.logb_mul (mul_pos hc ha).ne' hPositive.ne'
  rw [hMul, hPower]

theorem sourcePvHighWeightCutoff_pos {a₃ cP : ℝ} {d : ℕ}
    (ha : 0 < a₃) (hc : 0 < cP) (hd : 0 < d) (v : ℕ) :
    0 < sourcePvHighWeightCutoff a₃ cP d v :=
  div_pos (sourceHeightThreshold_pos ha hc v)
    (mul_pos (by exact_mod_cast hd) (Real.sqrt_pos.mpr (mul_pos hc ha)))

theorem sourcePvHighWeightCutoff_logb {a₃ cP : ℝ} {d : ℕ}
    (ha : 0 < a₃) (hc : 0 < cP) (hd : 0 < d) (v : ℕ) :
    Real.logb 2 (sourcePvHighWeightCutoff a₃ cP d v) =
      cP * ((v : ℝ) - 4) * a₃ + Real.logb 2 (cP * a₃) / 2 - Real.logb 2 d := by
  unfold sourcePvHighWeightCutoff
  rw [sqrt_height_cutoff_log (sourceHeightThreshold_pos ha hc v) (mul_pos hc ha)
    (by exact_mod_cast hd), sourceHeightThreshold_logb ha hc]
  ring

theorem source_Pv_high_weight_tail {n d L v : ℕ} {a₃ cP : ℝ}
    (hn : 0 < n) (hd : 0 < d) (ha : 0 < a₃) (hc : 0 < cP)
    (hOne : cP * a₃ ≤ 1) (hSize : 2 ≤ a₃ * (n : ℝ))
    (hDegree : 1 ≤ Real.sqrt (cP * a₃) * (d : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ))
    (hBudget : 512 * (2 - Real.logb 2 (cP * a₃) / 2) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ cP * a₃ / 4)
    (x : Fin n → ℂ) (hx : x ∈ sourceHighHeightFamily n d L a₃ cP v) :
    cP * a₃ / 4 ≤ uniformProbability (fun i =>
      ⌊Real.logb 2 (sourcePvHighWeightCutoff a₃ cP d v)⌋ ≤
        dyadicProfilePartOrder (sourceScaleProfile d v x) d ((sourceScaleProfile d v x).part i)) := by
  let P := sourceScaleProfile d v x
  let H := sourceHeightThreshold a₃ cP v
  let s := cP * a₃
  let W := H / ((d : ℝ) * Real.sqrt s)
  have hH : 0 < H := sourceHeightThreshold_pos ha hc v
  have hs : 0 < s := mul_pos hc ha
  have hGeometry := orderedCanonical_profile_order_geometry
    (fun i => canonicalApprox (d ^ v) (x i)) ((d : ℝ) / (d ^ v : ℕ))
  have hBad := profile_sqrt_height_cutoff_mass hn P (orderedCanonicalCreationOrder _ _) hGeometry
    hd hH hs hOne hDegree
  have hBudgetN := mul_le_mul_of_nonneg_right hBudget (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hBadBudget : profileSelectedMass P (profileHighLowParts P d H W) ≤ s * n / 4 := by
    apply hBad.trans
    convert hBudgetN using 1
    ring
  have hHigh : s * n / 2 ≤ profileSelectedMass P (profileHighParts P H) := by
    have hThird := (thirdSteepScale_bounds ha hSize).2.1
    have hScaled := mul_le_mul_of_nonneg_left hThird hc.le
    have hActual := orderedCanonical_highHeight_mass
      (fun i => canonicalApprox (d ^ v) (x i)) ((d : ℝ) / (d ^ v : ℕ)) H
    change profileSelectedMass P (profileHighParts P H) = _ at hActual
    rw [hActual]
    have hMass := hx.2
    dsimp only [s, H] at *
    nlinarith
  have hW : 0 < W := sourcePvHighWeightCutoff_pos ha hc hd v
  have hTail := profile_high_height_upper_tail P d H hW
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLow : s / 4 ≤ (profileSelectedMass P (profileHighParts P H) -
      profileSelectedMass P (profileHighLowParts P d H W)) / n := by
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  exact hLow.trans hTail

theorem source_Pv_weight_cutoff_gap {a₃ cP δ : ℝ} {d v : ℕ}
    (ha : 0 < a₃) (hc : 0 < cP) (hd : 0 < d) (hv : 5 ≤ v)
    (hSep : cP * a₃ * ((v : ℝ) - 4) ≥ 2 * Real.logb 2 d +
      2 * Real.logb 2 (72 * Real.sqrt d / δ) + 2 - Real.logb 2 (cP * a₃)) :
    ⌊Real.logb 2 (72 * Real.sqrt d / δ)⌋ ≤ ⌊Real.logb 2 (sourcePvHighWeightCutoff a₃ cP d v)⌋ ∧
      (cP * a₃ / 2) * ((v : ℝ) - 4) ≤
        (⌊Real.logb 2 (sourcePvHighWeightCutoff a₃ cP d v)⌋ : ℝ) -
          ⌊Real.logb 2 (72 * Real.sqrt d / δ)⌋ := by
  have hUpper := Int.floor_le (Real.logb 2 (72 * Real.sqrt d / δ))
  have hLower := Int.sub_one_lt_floor (Real.logb 2 (sourcePvHighWeightCutoff a₃ cP d v))
  rw [sourcePvHighWeightCutoff_logb ha hc hd] at hLower
  have hGap : (cP * a₃ / 2) * ((v : ℝ) - 4) ≤
      (⌊Real.logb 2 (sourcePvHighWeightCutoff a₃ cP d v)⌋ : ℝ) -
        ⌊Real.logb 2 (72 * Real.sqrt d / δ)⌋ := by
    rw [sourcePvHighWeightCutoff_logb ha hc hd]
    nlinarith
  have hvR : (5 : ℝ) ≤ v := by exact_mod_cast hv
  have hGapNonneg : 0 ≤ (cP * a₃ / 2) * ((v : ℝ) - 4) :=
    mul_nonneg (by positivity) (by linarith)
  refine ⟨?_, hGap⟩
  have h : (⌊Real.logb 2 (72 * Real.sqrt d / δ)⌋ : ℝ) ≤
      ⌊Real.logb 2 (sourcePvHighWeightCutoff a₃ cP d v)⌋ := by linarith
  exact_mod_cast h

end CircularLaw
