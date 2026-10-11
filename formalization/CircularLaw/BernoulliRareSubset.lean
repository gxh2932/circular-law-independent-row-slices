import CircularLaw.RareBernoulliSmallBall
import CircularLaw.FiniteProductConditioning

/-!
# Rare Bernoulli small balls from a selected coefficient family

The complement of the selected coordinates contributes a deterministic
shift after conditioning. Only the selected family needs large coefficients
or the rare-density hypothesis; all original Bernoulli coordinates remain.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem finite_product_integral_split_subset {ι α : Type*} [Fintype ι] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (S : Finset ι)
    (f : (ι → α) → ℝ) :
    (∫ x, f x ∂Measure.pi (fun _ : ι => ν)) =
      ∫ rest, ∫ selected,
        f ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => α)
          (fun i => i ∈ S)).symm (selected, rest))
        ∂Measure.pi (fun _ : {i : ι // i ∈ S} => ν)
        ∂Measure.pi (fun _ : {i : ι // i ∉ S} => ν) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => α) (fun i => i ∈ S)
  have hPres := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) (fun i => i ∈ S)
  have h := hPres.symm.integral_comp e.symm.measurableEmbedding f
  rw [← h]
  have hIndex : (Subtype.fintype (fun i : ι => i ∈ S)) = Finset.Subtype.fintype S :=
    Subsingleton.elim _ _
  simp only [hIndex]
  exact integral_prod_symm
    (μ := Measure.pi (fun _ : {i : ι // i ∈ S} => ν))
    (ν := Measure.pi (fun _ : {i : ι // i ∉ S} => ν))
    (fun pair => f (e.symm pair)) Integrable.of_finite

theorem bernoulli_cube_rare_subset_linear_form_small_ball {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (a : ι → ℂ) (S : Finset ι)
    (hRare : (S.card : ℝ) * p ≤ 1 / 2) {t : ℝ} (ht : 0 < t)
    (hLarge : ∀ i ∈ S, t ≤ ‖a i‖) (z : ℂ) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖(∑ i, weightedBernoulliValue (a i) (x i)) - z‖ ≤ t / 3} ≤
        1 - (S.card : ℝ) * p / 2 := by
  let E : Set (ι → Bool) :=
    {x | ‖(∑ i, weightedBernoulliValue (a i) (x i)) - z‖ ≤ t / 3}
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Bool) (fun i => i ∈ S)
  have hSum (selected : {i : ι // i ∈ S} → Bool) (rest : {i : ι // i ∉ S} → Bool) :
      (∑ i, weightedBernoulliValue (a i) (e.symm (selected, rest) i)) - z =
        (∑ i : {i : ι // i ∈ S}, weightedBernoulliValue (a i.val) (selected i)) -
          (z - ∑ i : {i : ι // i ∉ S}, weightedBernoulliValue (a i.val) (rest i)) := by
    have hSelected : ∀ i : {i : ι // i ∈ S}, e.symm (selected, rest) i.val = selected i := by
      intro i
      change (Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ S) (fun _ => Bool)).symm
        (selected, rest) i.val = selected i
      simp only [Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk, dif_pos i.property]
    have hRest : ∀ i : {i : ι // i ∉ S}, e.symm (selected, rest) i.val = rest i := by
      intro i
      change (Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ S) (fun _ => Bool)).symm
        (selected, rest) i.val = rest i
      simp only [Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk, dif_neg i.property]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i : ι => i ∈ S)
      (fun i => weightedBernoulliValue (a i) (e.symm (selected, rest) i))]
    simp_rw [hSelected, hRest]
    have hIndex : (Subtype.fintype (fun i : ι => i ∈ S)) = Finset.Subtype.fintype S :=
      Subsingleton.elim _ _
    simp only [hIndex]
    ring
  have hIntegral : (∫ x, E.indicator (fun _ => (1 : ℝ)) x
      ∂bernoulliCubeLaw ι p hp) = (bernoulliCubeLaw ι p hp).real E := by
    simpa only [smul_eq_mul, mul_one] using integral_indicator_const
      (μ := bernoulliCubeLaw ι p hp) (1 : ℝ) (Set.toFinite E).measurableSet
  change (bernoulliCubeLaw ι p hp).real E ≤ _
  rw [← hIntegral, bernoulliCubeLaw, finite_product_integral_split_subset]
  calc
    _ ≤ ∫ _ : {i : ι // i ∉ S} → Bool, 1 - (S.card : ℝ) * p / 2
        ∂Measure.pi (fun _ : {i : ι // i ∉ S} => bernoulliCoordinateLaw p hp) := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro rest
      let center := z - ∑ i : {i : ι // i ∉ S}, weightedBernoulliValue (a i.val) (rest i)
      let ES : Set ({i : ι // i ∈ S} → Bool) :=
        {selected | ‖(∑ i : {i : ι // i ∈ S}, weightedBernoulliValue (a i.val) (selected i)) - center‖ ≤ t / 3}
      have hPoint (selected : {i : ι // i ∈ S} → Bool) :
          E.indicator (fun _ => (1 : ℝ)) (e.symm (selected, rest)) =
            ES.indicator (fun _ => (1 : ℝ)) selected := by
        have hMem : e.symm (selected, rest) ∈ E ↔ selected ∈ ES := by
          dsimp only [E, ES, center, Set.mem_setOf_eq]
          rw [hSum]
        by_cases h : selected ∈ ES
        · rw [Set.indicator_of_mem (hMem.mpr h), Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem (fun h' => h (hMem.mp h')),
            Set.indicator_of_notMem h]
      change (∫ selected, E.indicator (fun _ => (1 : ℝ)) (e.symm (selected, rest))
        ∂bernoulliCubeLaw {i : ι // i ∈ S} p hp) ≤ _
      simp_rw [hPoint]
      rw [integral_indicator_const _ (Set.toFinite ES).measurableSet, smul_eq_mul, mul_one]
      simpa only [Fintype.card_coe] using bernoulli_cube_rare_linear_form_small_ball p hp
        (by simpa only [Fintype.card_coe] using hRare) (fun i : {i : ι // i ∈ S} => a i.val)
        ht (fun i => hLarge i.val i.property) center
    _ = _ := by simp

end CircularLaw
