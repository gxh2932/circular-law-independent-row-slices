import Mathlib

/-!
# Assembly across two degree regimes

This checks the index-splitting step in the final proof in
`sections/09_hermitization.tex`. The convergence hypotheses are explicit:
neither the lower-band theorem nor the superlogarithmic bridge is assumed
as an axiom of this project.
-/

open Filter
open scoped Topology

namespace CircularLaw

/-- If both restrictions of a sequence converge, the whole sequence converges.
The filters may be trivial when a regime occurs only finitely often. -/
theorem tendsto_of_two_regimes {α β : Type*} [TopologicalSpace β]
    {f : α → β} {l : Filter α} {target : β} (regime : Set α)
    (hlow : Tendsto f (l ⊓ 𝓟 regime) (𝓝 target))
    (hhigh : Tendsto f (l ⊓ 𝓟 regimeᶜ) (𝓝 target)) :
    Tendsto f l (𝓝 target) := by
  have hcover : (l ⊓ 𝓟 regime) ⊔ (l ⊓ 𝓟 regimeᶜ) = l := by
    rw [← inf_sup_left, sup_principal]
    simp
  rw [← hcover]
  exact hlow.sup hhigh

/-- The paper's common logarithmic cutoff `(log n)^(3/2)`. -/
def lowerRegime (d : ℕ → ℕ) : Set ℕ :=
  {n | (d n : ℝ) ≤ Real.rpow (Real.log n) (3 / 2 : ℝ)}

/-- The final assembly step, expressed for tail-probability sequences. -/
theorem tail_tendsto_of_degree_regimes (d : ℕ → ℕ) (tail : ℕ → ℝ)
    (hlow : Tendsto tail (atTop ⊓ 𝓟 (lowerRegime d)) (𝓝 0))
    (hhigh : Tendsto tail (atTop ⊓ 𝓟 (lowerRegime d)ᶜ) (𝓝 0)) :
    Tendsto tail atTop (𝓝 0) :=
  tendsto_of_two_regimes (lowerRegime d) hlow hhigh

end CircularLaw
