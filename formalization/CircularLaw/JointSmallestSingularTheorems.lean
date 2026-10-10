import CircularLaw.JointSourceMinimumRegimes

/-!
# Reviewed quantitative joint smallest-singular-value targets

The logarithmic-degree result holds at every admissible dimension at
least two: enlarging its absolute degree coefficient excludes the finite
initial segment. The superlogarithmic result is uniform for sufficiently
large dimensions, with an absolute probability coefficient independent of
epsilon and a polynomial exponent depending only on epsilon.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def LLYSmallestSingularTheorem : Prop :=
  ∃ C C₁ C₂ : ℝ, 0 < C ∧ 0 < C₁ ∧ 0 < C₂ ∧
    ∃ β βB : ℕ → ℝ, ∀ n : ℕ, 2 ≤ n → ∀ d : ℕ,
      C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
        2 < β n ∧ β n ≤ C₂ * Real.log (Real.log n) ∧
        2 < βB n ∧ βB n ≤ C₂ * Real.log (Real.log n) ∧
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          smallestSingularFailureSum n d ζ (Real.rpow (n : ℝ) (-β n))
            (Real.rpow (n : ℝ) (-βB n)) ≤ C₁ / Real.sqrt d

def UniformPolynomialSmallestSingularTheorem : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 2 < B ∧
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      (Real.log (n : ℝ)) ^ (1 + ε) ≤ (d : ℝ) → 2 * d ≤ n →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          smallestSingularFailureSum n d ζ (Real.rpow (n : ℝ) (-B))
            (Real.rpow (n : ℝ) (-B)) ≤ D / Real.sqrt d

theorem lly_smallest_singular_theorem : LLYSmallestSingularTheorem := by
  obtain ⟨p⟩ := joint_source_minimum_parameters_nonempty
  have hLogLog := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hReady := (eventually_joint_source_lower_cutoff_probability p).and
    (hLogLog.eventually_ge_atTop 1)
  obtain ⟨N, hN⟩ := hReady.exists_forall_of_atTop
  let C : ℝ := max p.C ((N + 1 : ℕ) / Real.log 2)
  let C₂ : ℝ := 2 * llySourceLoglogRatioConstant + 12
  let β : ℕ → ℝ := fun n => C₂ * Real.log (Real.log n)
  have hC : p.C ≤ C := le_max_left _ _
  have hNcost : (N + 1 : ℕ) ≤ C * Real.log 2 := by
    exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp (le_max_right _ _)
  have hC₂ : 2 < C₂ := by
    dsimp [C₂]
    linarith only [lly_source_loglog_ratio_constant_ge_eight]
  refine ⟨C, jointSourceMinimumErrorConstant p, C₂,
    lt_of_lt_of_le (by linarith only [p.degree] : 0 < p.C) hC,
    joint_source_minimum_error_constant_pos p, by linarith only [hC₂], β, β, ?_⟩
  intro n hn d hDegree hSize
  have hLog : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hCPos : 0 ≤ C := (lt_of_lt_of_le (by linarith only [p.degree] : 0 < p.C) hC).le
  have hNle : N ≤ n := by
    have hBound := hNcost.trans ((mul_le_mul_of_nonneg_left hLog hCPos).trans hDegree)
    have hdn : d ≤ n := by omega
    have hnR : (d : ℝ) ≤ n := by exact_mod_cast hdn
    have : (N : ℝ) < n := by
      simp only [Nat.cast_add, Nat.cast_one] at hBound
      linarith only [hBound, hnR]
    exact_mod_cast this.le
  obtain ⟨hProbability, hExponent⟩ := hN n hNle
  change 1 ≤ Real.log (Real.log (n : ℝ)) at hExponent
  have hβ : 2 < β n := by
    have h := mul_le_mul_of_nonneg_left hExponent (by linarith only [hC₂] : 0 ≤ C₂)
    dsimp [β]
    linarith only [h, hC₂]
  refine ⟨hβ, le_rfl, hβ, le_rfl, ?_⟩
  intro ζ hShift
  have hSourceDegree : p.C * Real.log (n : ℝ) ≤ d :=
    (mul_le_mul_of_nonneg_right hC (Real.log_natCast_nonneg n)).trans hDegree
  exact hProbability d hSourceDegree hSize ζ hShift

theorem uniform_polynomial_smallest_singular_theorem : UniformPolynomialSmallestSingularTheorem := by
  obtain ⟨p⟩ := joint_source_minimum_parameters_nonempty
  refine ⟨jointSourceMinimumErrorConstant p, joint_source_minimum_error_constant_pos p, ?_⟩
  intro ε hε
  refine ⟨2 * (8 * (1 + ε) / ε) + 12, ?_, eventually_joint_source_superlog_probability p hε⟩
  have hPos : 0 < 8 * (1 + ε) / ε := by positivity
  linarith only [hPos]

end CircularLaw
