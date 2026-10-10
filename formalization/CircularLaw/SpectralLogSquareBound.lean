import CircularLaw.PlanarSquaredLog
import CircularLaw.SpectralEnergyTightness

/-!
# Uniform spatial L2 control by matrix energy

The negative logarithmic singularity has a fixed planar integral bound.
On a bounded disk the positive logarithm is controlled by the eigenvalue
second moment. Jensen and Schur therefore bound the squared actual ESD
potential by a constant plus its normalized matrix energy.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CircularLaw

theorem planar_unit_squared_log_integral_bound :
    (∫ z : ℂ in Metric.closedBall 0 1, (Real.log ‖z‖) ^ 2) ≤ 32 * Real.pi := by
  have hInt := planar_squared_log_norm_integrableOn_closedBall 1
  have h := planar_radial_absolute_lintegral_bound (fun r => (Real.log r) ^ 2) 1 16
    (fun r hr hr1 => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (radial_squared_log_bound hr).trans (by nlinarith))
  have hRect : volume (Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) =
      ENNReal.ofReal (2 * Real.pi) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
    simp only [sub_zero, ENNReal.ofReal_one, one_mul, sub_neg_eq_add, ← two_mul]
  have hEq : (∫⁻ z : ℂ in Metric.closedBall 0 1,
      ENNReal.ofReal |(Real.log ‖z‖) ^ 2|) =
      ENNReal.ofReal (∫ z : ℂ in Metric.closedBall 0 1, (Real.log ‖z‖) ^ 2) := by
    have hAbs (z : ℂ) : |(Real.log ‖z‖) ^ 2| = (Real.log ‖z‖) ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    simp only [hAbs]
    exact (ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ (fun _ => sq_nonneg _))).symm
  rw [hEq, hRect, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)] at h
  have hNonneg : 0 ≤ 16 * (2 * Real.pi) := by positivity
  have hReal := (ENNReal.ofReal_le_ofReal_iff hNonneg).mp h
  linarith

def nearLogSquare (w z : ℂ) : ℝ :=
  (Metric.closedBall (0 : ℂ) 1).indicator (fun u => (Real.log ‖u‖) ^ 2) (z - w)

theorem near_log_square_nonneg (w z : ℂ) : 0 ≤ nearLogSquare w z := by
  unfold nearLogSquare
  exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

theorem near_log_square_integrable (w : ℂ) : Integrable (nearLogSquare w) volume :=
  ((planar_squared_log_norm_integrableOn_closedBall 1).integrable_indicator
    measurableSet_closedBall).comp_sub_right w

theorem near_log_square_integral_bound (w : ℂ) :
    (∫ z, nearLogSquare w z) ≤ 32 * Real.pi := by
  unfold nearLogSquare
  rw [integral_sub_right_eq_self, integral_indicator measurableSet_closedBall]
  exact planar_unit_squared_log_integral_bound

theorem log_kernel_square_on_disk_bound (w : ℂ) {R : ℝ}
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 R) :
    (Real.log ‖z - w‖) ^ 2 ≤ nearLogSquare w z + 2 * R ^ 2 + 2 * ‖w‖ ^ 2 := by
  have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  by_cases hNear : ‖z - w‖ ≤ 1
  · have hMem : z - w ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hNear
    rw [nearLogSquare, Set.indicator_of_mem hMem]
    nlinarith [sq_nonneg R, sq_nonneg ‖w‖]
  · have hNorm : 1 ≤ ‖z - w‖ := le_of_lt (lt_of_not_ge hNear)
    have hLogNonneg := Real.log_nonneg hNorm
    have hLog := Real.log_le_self (norm_nonneg (z - w))
    have hNormBound := norm_sub_le z w
    have hLogSq := pow_le_pow_left₀ hLogNonneg hLog 2
    have hNormSq := pow_le_pow_left₀ (norm_nonneg (z - w)) hNormBound 2
    have hzSq := pow_le_pow_left₀ (norm_nonneg z) hzR 2
    have hNearNonneg := near_log_square_nonneg w z
    nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

theorem log_kernel_square_integral_disk_bound (w : ℂ) (R : ℝ) :
    (∫ z : ℂ in Metric.closedBall 0 R, (Real.log ‖z - w‖) ^ 2) ≤
      32 * Real.pi + (2 * R ^ 2 + 2 * ‖w‖ ^ 2) * volume.real (Metric.closedBall (0 : ℂ) R) := by
  have hNear : IntegrableOn (nearLogSquare w) (Metric.closedBall 0 R) volume :=
    (near_log_square_integrable w).integrableOn
  have hKernel := planar_squared_log_kernel_integrableOn_closedBall w R
  have hConst : IntegrableOn (fun _ : ℂ => 2 * R ^ 2 + 2 * ‖w‖ ^ 2)
      (Metric.closedBall 0 R) volume :=
    integrableOn_const ((isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne)
  have hMono : (∫ z : ℂ in Metric.closedBall 0 R, (Real.log ‖z - w‖) ^ 2) ≤
      ∫ z : ℂ in Metric.closedBall 0 R, nearLogSquare w z + (2 * R ^ 2 + 2 * ‖w‖ ^ 2) := by
    apply setIntegral_mono_on hKernel (hNear.add hConst) measurableSet_closedBall
    intro z hz
    change (Real.log ‖z - w‖) ^ 2 ≤ nearLogSquare w z + (2 * R ^ 2 + 2 * ‖w‖ ^ 2)
    have h := log_kernel_square_on_disk_bound w hz
    linarith
  rw [integral_add hNear hConst, setIntegral_const] at hMono
  have hNearIntegral : (∫ z : ℂ in Metric.closedBall 0 R, nearLogSquare w z) ≤ 32 * Real.pi := by
    exact (integral_mono_measure Measure.restrict_le_self (ae_of_all _ (near_log_square_nonneg w))
      (near_log_square_integrable w)).trans (near_log_square_integral_bound w)
  simp only [smul_eq_mul] at hMono
  linarith

theorem spectral_log_potential_squared_integral_disk_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) :
    (∫ z : ℂ in Metric.closedBall 0 R, (spectralLogPotential A z) ^ 2) ≤
      32 * Real.pi + 2 * R ^ 2 * volume.real (Metric.closedBall (0 : ℂ) R) +
        2 * volume.real (Metric.closedBall (0 : ℂ) R) * (squareMatrixEnergy A / n) := by
  let D : Set ℂ := Metric.closedBall 0 R
  let v : ℝ := volume.real D
  let C : ℝ := 32 * Real.pi + 2 * R ^ 2 * v
  have hSumInt (s : Multiset ℂ) :
      IntegrableOn (fun z : ℂ => (s.map (fun w => (Real.log ‖z - w‖) ^ 2)).sum) D volume := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons w s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (planar_squared_log_kernel_integrableOn_closedBall w R).add ih
  have hSumIntegral (s : Multiset ℂ) :
      (∫ z in D, (s.map (fun w => (Real.log ‖z - w‖) ^ 2)).sum) =
        (s.map (fun w => ∫ z in D, (Real.log ‖z - w‖) ^ 2)).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons w s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [integral_add (planar_squared_log_kernel_integrableOn_closedBall w R) (hSumInt s), ih]
  have hPointInt : (∫ z in D, (spectralLogPotential A z) ^ 2) ≤
      ∫ z in D, (A.charpoly.roots.map (fun w => (Real.log ‖z - w‖) ^ 2)).sum / n := by
    apply setIntegral_mono_on
      ((spectral_log_potential_squared_locallyIntegrable A).integrableOn_isCompact
        (isCompact_closedBall (0 : ℂ) R))
      ((hSumInt A.charpoly.roots).div_const (n : ℝ)) measurableSet_closedBall
    intro z _
    exact spectral_log_potential_square_bound hn A z
  rw [integral_div, hSumIntegral] at hPointInt
  have hRoots : A.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots]
    simp
  have hSumBound : (A.charpoly.roots.map (fun w => ∫ z in D, (Real.log ‖z - w‖) ^ 2)).sum ≤
      (n : ℝ) * C + 2 * v * squareEigenvalueEnergy A := by
    calc
      _ ≤ (A.charpoly.roots.map (fun w => C + 2 * v * ‖w‖ ^ 2)).sum := by
        apply Multiset.sum_map_le_sum_map
        intro w hw
        have h := log_kernel_square_integral_disk_bound w R
        dsimp only [D, v, C]
        linarith
      _ = (n : ℝ) * C + 2 * v * squareEigenvalueEnergy A := by
        rw [Multiset.sum_map_add, Multiset.sum_map_mul_left]
        simp only [Multiset.map_const', Multiset.sum_replicate, hRoots, nsmul_eq_mul,
          squareEigenvalueEnergy]
  have hv : 0 ≤ v := measureReal_nonneg
  have hSchur := mul_le_mul_of_nonneg_left (square_eigenvalue_energy_le A)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hv)
  have hTotal : (n : ℝ) * C + 2 * v * squareEigenvalueEnergy A ≤
      (n : ℝ) * C + 2 * v * squareMatrixEnergy A := by linarith
  have hFinal := div_le_div_of_nonneg_right (hSumBound.trans hTotal)
    (Nat.cast_nonneg n)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ ≤ ((n : ℝ) * C + 2 * v * squareMatrixEnergy A) / n := hPointInt.trans hFinal
    _ = _ := by dsimp only [C, v, D]; field_simp

theorem normalized_log_determinant_squared_integral_eq_spectral {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) :
    (∫ z : ℂ in Metric.closedBall 0 R, (normalizedLogDeterminant A z) ^ 2) =
      ∫ z : ℂ in Metric.closedBall 0 R, (spectralLogPotential A z) ^ 2 := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (spectral_log_potential_eq_log_determinant_ae A)] with z hz
  rw [hz]

theorem normalized_log_determinant_squared_locallyIntegrable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    LocallyIntegrable (fun z => (normalizedLogDeterminant A z) ^ 2) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  apply ((spectral_log_potential_squared_locallyIntegrable A).integrableOn_isCompact hk).congr_fun_ae
  filter_upwards [ae_restrict_of_ae (spectral_log_potential_eq_log_determinant_ae A)] with z hz
  rw [hz]

theorem degree_normalized_slice_log_determinant_squared_integral_bound {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (s : RowSliceMatrix n d) (R : ℝ) :
    (∫ z : ℂ in Metric.closedBall 0 R, (normalizedLogDeterminant (degreeNormalizedMatrix s) z) ^ 2) ≤
      32 * Real.pi + 2 * (R ^ 2 + 1) * volume.real (Metric.closedBall (0 : ℂ) R) := by
  rw [normalized_log_determinant_squared_integral_eq_spectral]
  have h := spectral_log_potential_squared_integral_disk_bound hn (degreeNormalizedMatrix s) R
  rw [degree_normalized_matrix_energy s hd, div_self (by exact_mod_cast hn.ne'), mul_one] at h
  nlinarith

theorem spectral_log_potential_spatial_square_bounded_in_probability_of_energy {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hEnergy : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n)) :
    VaryingBoundedInProbability μ (fun n ω =>
      ∫ z : ℂ in Metric.closedBall 0 R, (spectralLogPotential (A n ω) z) ^ 2) := by
  intro δ hδ
  obtain ⟨M, hM, hEvent⟩ := hEnergy δ hδ
  let v : ℝ := volume.real (Metric.closedBall (0 : ℂ) R)
  let C : ℝ := 32 * Real.pi + 2 * R ^ 2 * v
  let K : ℝ := 2 * v
  have hv : 0 ≤ v := measureReal_nonneg
  have hC : 0 < C := by dsimp [C]; positivity
  have hK : 0 ≤ K := mul_nonneg (by norm_num) hv
  let N : ℝ := C + K * M + 1
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨N, hN, ?_⟩
  filter_upwards [hEvent, eventually_gt_atTop 0] with n hn hnPos
  apply lt_of_le_of_lt _ hn
  apply measureReal_mono
  · intro ω hω
    have hNonneg : 0 ≤ ∫ z : ℂ in Metric.closedBall 0 R, (spectralLogPotential (A n ω) z) ^ 2 :=
      integral_nonneg (fun _ => sq_nonneg _)
    change N < |∫ z : ℂ in Metric.closedBall 0 R, (spectralLogPotential (A n ω) z) ^ 2| at hω
    rw [abs_of_nonneg hNonneg] at hω
    have hBound := spectral_log_potential_squared_integral_disk_bound hnPos (A n ω) R
    have hEnergyLarge : M < squareMatrixEnergy (A n ω) / n := by
      by_contra h
      have hKM := mul_le_mul_of_nonneg_left (le_of_not_gt h) hK
      change (∫ z : ℂ in Metric.closedBall 0 R, (spectralLogPotential (A n ω) z) ^ 2) ≤
        C + K * (squareMatrixEnergy (A n ω) / n) at hBound
      dsimp only [N] at hω
      linarith
    exact hEnergyLarge.trans_le (le_abs_self _)
  · finiteness

theorem normalized_log_determinant_spatial_square_bounded_in_probability_of_energy {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hEnergy : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n)) :
    VaryingBoundedInProbability μ (fun n ω =>
      ∫ z : ℂ in Metric.closedBall 0 R, (normalizedLogDeterminant (A n ω) z) ^ 2) := by
  have h := spectral_log_potential_spatial_square_bounded_in_probability_of_energy μ A R hEnergy
  simp only [VaryingBoundedInProbability, normalized_log_determinant_squared_integral_eq_spectral]
  exact h

theorem degree_normalized_bernoulli_log_determinant_spatial_square_bounded_in_probability
    (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d) (R : ℝ) :
    VaryingBoundedInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => ∫ z : ℂ in Metric.closedBall 0 R,
        (Real.log ‖(normalizedShiftedBernoulliMatrix (d n) z x).det‖ / n) ^ 2) :=
  normalized_log_determinant_spatial_square_bounded_in_probability_of_energy _ _ R
    (degree_normalized_bernoulli_energy_bounded_in_probability d hd hsparse)

end CircularLaw
