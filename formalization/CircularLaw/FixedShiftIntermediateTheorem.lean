import CircularLaw.IntermediateSingularValueTheorem
import Mathlib.Topology.Algebra.Order.Field

/-!
# The manuscript intermediate theorem for every fixed spectral shift

The uniform finite-dimensional estimate applies to `z*sqrt(d)`, and
the logarithmic lower bound forces the degree to infinity. The explicit
`B/d` failure estimate therefore gives the literal success probability
`1-o(1)`. Both introductory and Section 7 statements are covered.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem shifted_sqrt_degree_norm (z : ℂ) (d : ℕ) :
    ‖z * (Real.sqrt (d : ℝ) : ℂ)‖ = ‖z‖ * Real.sqrt d := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem degree_tendsto_atTop_of_log_lower_bound {C : ℝ} (hC : 0 < C)
    (d : ℕ → ℕ) (hLower : ∀ᶠ n : ℕ in atTop, C * Real.log n ≤ (d n : ℝ)) :
    Tendsto (fun n : ℕ => (d n : ℝ)) atTop atTop := by
  have hLog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  exact tendsto_atTop_mono' atTop hLower (Tendsto.const_mul_atTop hC hLog)

def fixedShiftIntermediateProbability (R : ℝ) (d : ℕ → ℕ) (z : ℂ) (n : ℕ) : ℝ :=
  uniformProbability (IntermediateSingularValueEvent (n := n) (d := d n)
    (z * (Real.sqrt (d n : ℝ) : ℂ)) R)

theorem intermediate_probability_tendsto_one {C R B : ℝ} (hC : 0 < C)
    (d : ℕ → ℕ) (z : ℂ)
    (hLower : ∀ᶠ n : ℕ in atTop, C * Real.log n ≤ (d n : ℝ))
    (hProbability : ∀ᶠ n : ℕ in atTop,
      1 - B / (d n : ℝ) ≤ fixedShiftIntermediateProbability R d z n) :
    Tendsto (fixedShiftIntermediateProbability R d z) atTop (𝓝 1) := by
  have hD := degree_tendsto_atTop_of_log_lower_bound hC d hLower
  have hDiv : Tendsto (fun n : ℕ => B / (d n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := B)).mul hD.inv_tendsto_atTop
  have hOne : Tendsto (fun n : ℕ => 1 - B / (d n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hDiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hOne tendsto_const_nhds hProbability
    (Eventually.of_forall (fun n => uniformProbability_le_one _))

/-- Literal fixed-shift manuscript conclusion, with the exact source
deletion count, positive scale constants, uniform `B/d` failure bound,
and success probability tending to one for every lower-band sequence. -/
def FixedShiftIntermediateSingularValueTheorem : Prop :=
  ∃ Cstar R Cq B : ℝ, 0 < Cstar ∧ 0 < R ∧ 0 < Cq ∧ 0 < B ∧
    ∀ C : ℝ, Cstar ≤ C → ∀ σ : ℝ, 0 < σ → σ < 1 →
      ∀ d : ℕ → ℕ, (∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) → ∀ z : ℂ,
        (∀ᶠ n : ℕ in atTop, intermediateDeletionCount n (d n) < n ∧
          (intermediateDeletionCount n (d n) : ℝ) ≤ Cq * ((n : ℝ) / (d n : ℝ) ^ 2) ∧
          1 - B / (d n : ℝ) ≤ fixedShiftIntermediateProbability R d z n) ∧
        Tendsto (fixedShiftIntermediateProbability R d z) atTop (𝓝 1)

theorem fixed_shift_intermediate_singular_value_theorem : FixedShiftIntermediateSingularValueTheorem := by
  obtain ⟨Cstar, R, B, hCstar, hR, hB, hUniform⟩ := intermediate_singular_value_theorem
  refine ⟨Cstar, R, 5, B, hCstar, hR, by norm_num, hB, ?_⟩
  intro C hC σ hσ0 hσ1 d hBand z
  obtain ⟨N, hN⟩ := hUniform C hC σ ‖z‖ hσ0 hσ1
  have hConclusions : ∀ᶠ n : ℕ in atTop, intermediateDeletionCount n (d n) < n ∧
      (intermediateDeletionCount n (d n) : ℝ) ≤ 5 * ((n : ℝ) / (d n : ℝ) ^ 2) ∧
      1 - B / (d n : ℝ) ≤ fixedShiftIntermediateProbability R d z n := by
    filter_upwards [eventually_ge_atTop N, hBand] with n hn hDegree
    obtain ⟨hIndex, hScale, hProbability⟩ := hN n hn (d n) hDegree
    exact ⟨hIndex, hScale, hProbability (z * (Real.sqrt (d n : ℝ) : ℂ))
      (shifted_sqrt_degree_norm z (d n)).le⟩
  exact ⟨hConclusions, intermediate_probability_tendsto_one (hCstar.trans_le hC) d z
    (hBand.mono (fun _ h => h.1)) (hConclusions.mono (fun _ h => h.2.2))⟩

theorem intro_intermediate_singular_value_theorem : FixedShiftIntermediateSingularValueTheorem :=
  fixed_shift_intermediate_singular_value_theorem

end CircularLaw
