import CircularLaw.SingletonExposureConcentration

/-!
# Independent uniform fibers after coordinatewise exposure

For an independent finite uniform product, exposing a separate statistic
in each coordinate leaves the product of the corresponding uniform fibers.
This applies to actual row-slice exposures across retained rows.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def finiteProductFiberEquiv {ι : Type*} [Fintype ι]
    {α β : ι → Type*} (f : ∀ i, α i → β i) (reference : ∀ i, α i) :
    {x : ∀ i, α i // (fun i => f i (x i)) = (fun i => f i (reference i))} ≃
      (∀ i, {a : α i // f i a = f i (reference i)}) :=
  { toFun := fun x i => ⟨x.val i, congrFun x.property i⟩
    invFun := fun x => ⟨fun i => (x i).val, funext (fun i => (x i).property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem uniformProbability_product_fiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (β i)]
    (f : ∀ i, α i → β i) (reference : ∀ i, α i) (E : ∀ i, α i → Prop) :
    uniformProbability (fun x : {x : ∀ i, α i //
      (fun i => f i (x i)) = (fun i => f i (reference i))} => ∀ i, E i (x.val i)) =
        ∏ i, uniformProbability (fun a : {a : α i // f i a = f i (reference i)} => E i a.val) := by
  classical
  let e := finiteProductFiberEquiv f reference
  rw [← uniformProbability_reindex e.symm]
  change uniformProbability (fun x : ∀ i, {a : α i // f i a = f i (reference i)} =>
    ∀ i, E i (x i).val) = _
  exact uniformProbability_pi (fun i (a : {a : α i // f i a = f i (reference i)}) => E i a.val)

theorem uniformProbability_product_fiber_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (β i)]
    (f : ∀ i, α i → β i) (reference : ∀ i, α i) (E : (∀ i, α i) → Prop) :
    uniformProbability (fun x : {x : ∀ i, α i //
      (fun i => f i (x i)) = (fun i => f i (reference i))} => E x.val) =
        uniformProbability (fun x : ∀ i, {a : α i // f i a = f i (reference i)} =>
          E (fun i => (x i).val)) := by
  classical
  exact (uniformProbability_reindex (finiteProductFiberEquiv f reference).symm
    (fun x => E x.val)).symm

theorem uniformProbability_pi_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (I : Finset ι) (E : (∀ i : I, α i.val) → Prop) :
    uniformProbability (fun x : ∀ i, α i => E (fun i : I => x i.val)) =
      uniformProbability E := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ I) α
  rw [← uniformProbability_reindex e.symm]
  have hRestrict (x : (∀ i : I, α i.val) × (∀ i : {i : ι // i ∉ I}, α i.val)) :
      (fun i : I => e.symm x i.val) = x.1 := by
    funext i
    simp only [e, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk, dif_pos i.property]
  simp_rw [hRestrict]
  rw [uniformProbability_prod_fubini]
  change finiteMean (fun _ : ∀ i : {i : ι // i ∉ I}, α i.val => uniformProbability E) = _
  exact finiteMean_const _

end CircularLaw
