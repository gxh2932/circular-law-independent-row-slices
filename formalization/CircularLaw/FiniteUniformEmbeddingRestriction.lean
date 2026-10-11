import CircularLaw.FiniteProductFibers

/-!
# The actual finite uniform product law under any injective restriction
-/

noncomputable section
open Classical

namespace CircularLaw

theorem uniformProbability_pi_embedding_restrict {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [Nonempty α]
    (u : ι ↪ κ) (E : (ι → α) → Prop) :
    uniformProbability (fun x : κ → α => E (fun i => x (u i))) = uniformProbability E := by
  let I : Finset κ := Finset.univ.image u
  let v : ι ≃ I := Equiv.ofBijective
    (fun i => (⟨u i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ : I)) (by
      constructor
      · intro i j h
        exact u.injective (congrArg Subtype.val h)
      · intro i
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.property
        exact ⟨j, Subtype.ext hj⟩)
  let e : (I → α) ≃ (ι → α) :=
    { toFun := fun x i => x (v i)
      invFun := fun x i => x (v.symm i)
      left_inv := by intro x; funext i; simp only [Equiv.apply_symm_apply]
      right_inv := by intro x; funext i; simp only [Equiv.symm_apply_apply] }
  have h := uniformProbability_pi_restrict (α := fun _ : κ => α) I
    (fun x : I → α => E (e x))
  change uniformProbability (fun x : κ → α => E (fun i => x (u i))) =
    uniformProbability (fun x : I → α => E (e x)) at h
  exact h.trans (uniformProbability_reindex e E)

end CircularLaw
