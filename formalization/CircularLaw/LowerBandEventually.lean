import CircularLaw.SourceSteepWitness

/-!
# Uniform eventual degree conditions in the lower band

An eventual property of the integer degree holds uniformly for every
degree above `C*log(n)` once `n` is large. This makes the threshold
independent of a separately chosen degree sequence.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def InLowerBand (C σ : ℝ) (n d : ℕ) : Prop :=
  C * Real.log n ≤ (d : ℝ) ∧ (d : ℝ) ≤ Real.rpow (Real.log n) (1 + σ)

theorem eventually_degree_property_uniform {C : ℝ} (hC : 0 < C) {P : ℕ → Prop}
    (hP : ∀ᶠ d : ℕ in atTop, P d) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → P d := by
  obtain ⟨D, hD⟩ := eventually_atTop.mp hP
  have hLog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [hLog.eventually_ge_atTop ((D : ℝ) / C)] with n hn
  dsimp only [Function.comp_apply] at hn
  intro d hd
  have hScaled := (div_le_iff₀ hC).mp hn
  have hReal : (D : ℝ) ≤ d := by nlinarith
  exact hD d (by exact_mod_cast hReal)

end CircularLaw
