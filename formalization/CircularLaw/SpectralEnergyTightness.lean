import CircularLaw.EmpiricalSpectralIntegrals
import CircularLaw.SchurEigenvalueEnergy
import CircularLaw.VarianceNormalizationTransfer
import CircularLaw.SpectralLogConvergence

/-!
# ESD second moments and actual spectral tail bounds

Schur's energy inequality supplies the deterministic tightness input of
the replacement principle, without normality or diagonalizability.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal Topology

namespace CircularLaw

theorem empiricalSpectralMeasure_integrable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (f : ℂ → ℝ) :
    Integrable f (empiricalSpectralMeasure A) := by
  cases n with
  | zero => simp [empiricalSpectralMeasure]
  | succ n =>
    exact (integrable_multiset_dirac_sum A.charpoly.roots f).smul_measure (by simp)

theorem empirical_spectral_second_moment_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∫ w, ‖w‖ ^ 2 ∂empiricalSpectralMeasure A) ≤ squareMatrixEnergy A / n := by
  rw [empiricalSpectralMeasure_integral]
  exact div_le_div_of_nonneg_right (square_eigenvalue_energy_le A) (Nat.cast_nonneg n)

theorem empirical_spectral_tail_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) {R : ℝ} (hR : 0 < R) :
    (empiricalSpectralMeasure A).real {w | R ≤ ‖w‖} ≤
      (squareMatrixEnergy A / n) / R ^ 2 := by
  letI : IsProbabilityMeasure (empiricalSpectralMeasure A) :=
    ⟨empiricalSpectralMeasure_univ hn A⟩
  have hMono : (empiricalSpectralMeasure A).real {w | R ≤ ‖w‖} ≤
      (empiricalSpectralMeasure A).real {w | R ^ 2 ≤ ‖w‖ ^ 2} := by
    apply measureReal_mono
    · intro w hw
      dsimp only [Set.mem_setOf_eq] at hw ⊢
      nlinarith [norm_nonneg w]
    · finiteness
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (empiricalSpectralMeasure A) (fun w => sq_nonneg ‖w‖))
    (empiricalSpectralMeasure_integrable A (fun w => ‖w‖ ^ 2)) (R ^ 2)
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left hMono (sq_nonneg R)).trans
    (hMarkov.trans (empirical_spectral_second_moment_bound A))

theorem degree_normalized_slice_spectral_tail_bound {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (s : RowSliceMatrix n d) {R : ℝ} (hR : 0 < R) :
    (empiricalSpectralMeasure (degreeNormalizedMatrix s)).real {w | R ≤ ‖w‖} ≤ 1 / R ^ 2 := by
  have h := empirical_spectral_tail_bound hn (degreeNormalizedMatrix s) hR
  rw [degree_normalized_matrix_energy s hd, div_self (by exact_mod_cast hn.ne')] at h
  exact h

theorem degree_normalized_slice_uniform_spectral_tightness {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ (n d : ℕ), 0 < n → 0 < d →
      ∀ s : RowSliceMatrix n d,
        (empiricalSpectralMeasure (degreeNormalizedMatrix s)).real {w | R ≤ ‖w‖} < δ := by
  refine ⟨Real.sqrt δ⁻¹ + 1, by positivity, ?_⟩
  intro n d hn hd s
  apply (degree_normalized_slice_spectral_tail_bound hn hd s (by positivity)).trans_lt
  have hδInv : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hR : δ⁻¹ < (Real.sqrt δ⁻¹ + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt hδInv.le, Real.sqrt_nonneg δ⁻¹]
  have hPos : 0 < (Real.sqrt δ⁻¹ + 1) ^ 2 := lt_trans hδInv hR
  rw [div_lt_iff₀ hPos]
  have h := mul_lt_mul_of_pos_left hR hδ
  rw [mul_inv_cancel₀ hδ.ne'] at h
  exact h

theorem spectral_tightness_in_probability_of_energy_bound {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hEnergy : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n)) :
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ → ∃ R : ℝ, 0 < R ∧
      ∀ᶠ n in atTop, (μ n).real
        {ω | ε < (empiricalSpectralMeasure (A n ω)).real {w | R ≤ ‖w‖}} < δ := by
  intro ε δ hε hδ
  obtain ⟨M, hM, hEvent⟩ := hEnergy δ hδ
  let R : ℝ := Real.sqrt (M / ε) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hRatio : M / R ^ 2 < ε := by
    have hME : 0 < M / ε := div_pos hM hε
    have hSq : M / ε < R ^ 2 := by
      dsimp [R]
      nlinarith [Real.sq_sqrt hME.le, Real.sqrt_nonneg (M / ε)]
    have h := mul_lt_mul_of_pos_left hSq hε
    rw [mul_div_cancel₀ M hε.ne'] at h
    exact (div_lt_iff₀ (sq_pos_of_pos hR)).mpr h
  refine ⟨R, hR, ?_⟩
  filter_upwards [hEvent, eventually_gt_atTop 0] with n hn hnPos
  apply lt_of_le_of_lt _ hn
  apply measureReal_mono
  · intro ω hω
    have hTail := empirical_spectral_tail_bound hnPos (A n ω) hR
    change ε < (empiricalSpectralMeasure (A n ω)).real {w | R ≤ ‖w‖} at hω
    have hEnergyLarge : M < squareMatrixEnergy (A n ω) / n := by
      by_contra h
      have hDiv := div_le_div_of_nonneg_right (le_of_not_gt h) (sq_nonneg R)
      linarith
    exact hEnergyLarge.trans_le (le_abs_self _)
  · finiteness

theorem degree_normalized_bernoulli_energy_bounded_in_probability (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d) :
    VaryingBoundedInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => squareMatrixEnergy (degreeNormalizedBernoulliMatrix (d n) x) / n) := by
  have h := bernoulli_second_moment_bounded_in_probability d 0 hd hsparse
  simp only [VaryingBoundedInProbability, bernoulliSingularSecondMoment_eq,
    normalizedShiftedBernoulliMatrix, zero_smul, sub_zero,
    degreeNormalizedBernoulliMatrix] at h ⊢
  exact h

theorem degree_normalized_bernoulli_spectral_tightness_in_probability (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d) :
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ → ∃ R : ℝ, 0 < R ∧
      ∀ᶠ n in atTop, (sparseBernoulliMatrixLaw n (d n)).real
        {x | ε < (empiricalSpectralMeasure (degreeNormalizedBernoulliMatrix (d n) x)).real
          {w | R ≤ ‖w‖}} < δ :=
  spectral_tightness_in_probability_of_energy_bound _ _
    (degree_normalized_bernoulli_energy_bounded_in_probability d hd hsparse)

end CircularLaw
