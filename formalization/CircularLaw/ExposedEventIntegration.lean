import CircularLaw.EqualBlockFiberNorm

/-!
# Integrating a bound on an exposed event

A structural event determined by the finite exposure is intersected with
the small-ball event before integration. Its complement is not charged
once for each coefficient vector or net point.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem uniformProbability_inter_exposed {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (f : α → β) (E G : α → Prop) {B : ℝ} (hB : 0 ≤ B)
    (hConstant : ∀ a b, f a = f b → (G a ↔ G b))
    (hBound : ∀ reference : α, G reference →
      uniformProbability (fun a : {a // f a = f reference} => E a.val) ≤ B) :
    uniformProbability (fun a => E a ∧ G a) ≤ B := by
  have hAverage : uniformProbability (fun a => E a ∧ G a) ≤
      finiteMean (fun _ : α => B) := by
    apply uniformProbability_le_fiber_reference f (fun a => E a ∧ G a) (fun _ => B)
      (fun _ _ _ => rfl)
    intro reference
    by_cases hGood : G reference
    · exact (uniformProbability_mono (fun _ h => h.1)).trans (hBound reference hGood)
    · calc
        _ ≤ uniformProbability (fun _ : {a // f a = f reference} => False) := by
          apply uniformProbability_mono
          intro a ha
          exact hGood ((hConstant a.val reference a.property).mp ha.2)
        _ = 0 := by simp [uniformProbability]
        _ ≤ B := hB
  simpa only [finiteMean_const] using hAverage

end CircularLaw
