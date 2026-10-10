import CircularLaw.CubeConcentration

/-!
# Selecting the first half-mass cube scale

Positive-radius cubes exhaust the plane. For a finite nonempty family of
probability laws whose concentration at the initial cube scale is below
one half, there is a first integer scale at which some translated cube
has mass above one half. All laws have concentration at most one half at
the preceding scale.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CircularLaw

theorem iUnion_planarCube_nat {r : ℝ} (hr : 0 < r) :
    (⋃ N : ℕ, planarCube (0 : ℂ) ((N : ℝ) * r)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ / r)
  have hNorm : ‖x‖ ≤ (N : ℝ) * r := ((div_lt_iff₀ hr).mp hN).le
  apply Set.mem_iUnion.mpr
  refine ⟨N, closedBall_subset_planarCube 0 _ ?_⟩
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hNorm

theorem exists_cube_mass_gt_half (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) : ∃ N : ℕ, 1 / 2 < μ.real (planarCube 0 ((N : ℝ) * r)) := by
  have hMono : Monotone (fun N : ℕ => planarCube (0 : ℂ) ((N : ℝ) * r)) := by
    intro N M hNM
    exact planarCube_mono 0 (mul_le_mul_of_nonneg_right (by exact_mod_cast hNM) hr.le)
  have hMass : (⨆ N : ℕ, μ (planarCube 0 ((N : ℝ) * r))) = 1 := by
    rw [← hMono.measure_iUnion, iUnion_planarCube_nat hr, measure_univ]
  by_contra h
  push_neg at h
  have hBound : (⨆ N : ℕ, μ (planarCube 0 ((N : ℝ) * r))) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    apply iSup_le
    intro N
    exact (ENNReal.le_ofReal_iff_toReal_le (by finiteness) (by norm_num)).mpr (h N)
  rw [hMass] at hBound
  norm_num at hBound

theorem exists_first_half_mass_cube {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {r : ℝ} (hr : 0 < r) (hSmall : ∀ i, cubeConcentration (μ i) r < 1 / 2) :
    ∃ (N : ℕ) (q : ι) (z : ℂ), 2 ≤ N ∧
      1 / 2 < (μ q).real (planarCube z ((N : ℝ) * r)) ∧
      ∀ i, cubeConcentration (μ i) (((N - 1 : ℕ) : ℝ) * r) ≤ 1 / 2 := by
  classical
  let P : ℕ → Prop := fun N => ∃ q z, 1 / 2 < (μ q).real (planarCube z ((N : ℝ) * r))
  have hExists : ∃ N, P N := by
    let q : ι := Classical.arbitrary ι
    obtain ⟨N, hN⟩ := exists_cube_mass_gt_half (μ q) hr
    exact ⟨N, q, 0, hN⟩
  let N := Nat.find hExists
  obtain ⟨q, z, hMass⟩ := Nat.find_spec hExists
  have hN : 2 ≤ N := by
    by_contra hN
    have hNle : (N : ℝ) ≤ 1 := by exact_mod_cast (show N ≤ 1 by omega)
    have hRadius : (N : ℝ) * r ≤ r := by nlinarith
    have hBound := (measureReal_mono (planarCube_mono z hRadius)).trans
      (probability_planarCube_le_concentration (μ q) r z)
    exact (not_lt_of_ge (hBound.trans (hSmall q).le)) hMass
  refine ⟨N, q, z, hN, hMass, ?_⟩
  intro i
  apply cubeConcentration_le_of_bounds
  intro w
  apply le_of_not_gt
  intro hw
  exact Nat.find_min hExists (show N - 1 < N by omega) ⟨i, w, hw⟩

end CircularLaw
