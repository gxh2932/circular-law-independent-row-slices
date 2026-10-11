import CircularLaw.DependentUniformSum

/-!
# Conditional concentration of a row with singleton witnesses

The exposed row-slice fiber has the exact uniform product law of its
remaining singleton positions. The actual bilinear row action equals the
fixed contribution plus the witnessed-block sum. All deterministic terms
are absorbed into the center.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def rowLinearForm {n d : ℕ} (S : RowSlice n d) (y : Fin n → ℂ) : ℂ :=
  ∑ j, rowEntry S j * y j

theorem rowLinearForm_eq_support_sum {n d : ℕ} (S : RowSlice n d) (y : Fin n → ℂ) :
    rowLinearForm S y = ∑ j ∈ S.val, y j := by
  simp [rowLinearForm, rowEntry]

theorem singletonBlockSliceFiberEquiv_sum {n d : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (hFixed : ∀ q, Disjoint fixed (J q)) (hDegree : fixed.card + Fintype.card ι = d)
    (U : SingletonBlockChoices J) (y : Fin n → ℂ) :
    rowLinearForm ((singletonBlockSliceFiberEquiv fixed J hDis hFixed hDegree).symm U).val y =
      (∑ j ∈ fixed, y j) + ∑ q, y (U q).val := by
  rw [rowLinearForm_eq_support_sum]
  exact singletonBlockCompletion_sum fixed J hDis hFixed U y

theorem singleton_block_conditional_small_ball {n d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (hFixed : ∀ q, Disjoint fixed (J q)) (hDegree : fixed.card + Fintype.card ι = d)
    (hNonempty : ∀ q, (J q).Nonempty) (hb : 1 ≤ Fintype.card ι)
    (y : Fin n → ℂ) {r : ℝ} (hr : 0 < r)
    (hAtom : ∀ q z, uniformProbability (fun j : {j : Fin n // j ∈ J q} =>
      ‖y j.val - z‖ ≤ r) ≤ 1 / 2) (a z : ℂ) :
    uniformProbability (fun S : SingletonBlockSliceFiber (d := d) fixed J =>
      ‖rowLinearForm S.val y + a - z‖ ≤ r) ≤
        min (1 / 2) ((2 * (24 * Real.exp 1 / Real.pi)) / Real.sqrt (Fintype.card ι : ℝ)) := by
  haveI : ∀ q, Nonempty {j : Fin n // j ∈ J q} := fun q => (hNonempty q).to_subtype
  let e := singletonBlockSliceFiberEquiv fixed J hDis hFixed hDegree
  rw [← uniformProbability_reindex e.symm]
  have hEvent : (fun U : SingletonBlockChoices J =>
      ‖rowLinearForm (e.symm U).val y + a - z‖ ≤ r) =
      (fun U : SingletonBlockChoices J =>
        ‖(∑ q, y (U q).val) - (z - a - ∑ j ∈ fixed, y j)‖ ≤ r) := by
    funext U
    rw [singletonBlockSliceFiberEquiv_sum]
    have hEq : ((∑ j ∈ fixed, y j) + ∑ q, y (U q).val) + a - z =
        (∑ q, y (U q).val) - (z - a - ∑ j ∈ fixed, y j) := by abel
    rw [hEq]
  rw [hEvent]
  exact uniform_dependent_sum_half_deficit
    (fun q (j : {j : Fin n // j ∈ J q}) => y j.val) hb hr hAtom _

theorem equal_block_conditional_small_ball {n d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (fixed : Finset (Fin n)) (L R : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (L q ∪ R q) (L p ∪ R p)))
    (hHalves : ∀ q, Disjoint (L q) (R q)) (hSize : ∀ q, (L q).card = (R q).card)
    (hLeft : ∀ q, (L q).Nonempty) (hFixed : ∀ q, Disjoint fixed (L q ∪ R q))
    (hDegree : fixed.card + Fintype.card ι = d) (hb : 1 ≤ Fintype.card ι)
    (y : Fin n → ℂ) {r : ℝ} (hr : 0 < r)
    (hSep : ∀ q l, l ∈ L q → ∀ j, j ∈ R q → 2 * r < dist (y l) (y j)) (a z : ℂ) :
    uniformProbability (fun S : SingletonBlockSliceFiber (d := d) fixed (fun q => L q ∪ R q) =>
      ‖rowLinearForm S.val y + a - z‖ ≤ r) ≤
        min (1 / 2) ((2 * (24 * Real.exp 1 / Real.pi)) / Real.sqrt (Fintype.card ι : ℝ)) := by
  exact singleton_block_conditional_small_ball fixed (fun q => L q ∪ R q) hDis hFixed hDegree
    (fun q => (hLeft q).mono Finset.subset_union_left) hb y hr
    (fun q z => equal_halves_small_ball (L q) (R q) (hHalves q) (hSize q) (hLeft q) y (hSep q) z) a z

end CircularLaw
