import CircularLaw.DiscreteConcentration
import CircularLaw.PlanarPacking
import CircularLaw.MeasureModel

/-!
# Concentration of a regular profile block

The proved discrete concentration theorem applies to the actual uniform
samples of a balanced finite level partition. The regular source scale
then gives the inverse-weight bound required by the conditional row proof.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CircularLaw

theorem balanced_separated_uniform_law {α β : Type*}
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype β]
    (level : α → β) (value : β → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hSep : ∀ a b, a ≠ b → δ ≤ dist (value a) (value b))
    (hBalance : ∀ a b, Nat.card {x // level x = a} ≤ 4 * Nat.card {x // level x = b}) :
    SeparatedPlanarLaw ((finiteUniformMeasure α).map (fun x => value (level x)))
      δ (4 / ((Fintype.card β : ℝ) + 3)) := by
  classical
  have hMeas : Measurable (fun x => value (level x)) := measurable_of_finite _
  have hInj : Function.Injective value := by
    intro a b hab
    by_contra hne
    have h := hSep a b hne
    rw [hab, dist_self] at h
    linarith
  refine ⟨Set.range value, ?_, ?_, ?_⟩
  · apply (ae_map_iff (μ := finiteUniformMeasure α) (p := fun x => x ∈ Set.range value)
      hMeas.aemeasurable (Set.finite_range value).measurableSet).mpr
    exact ae_of_all _ (fun x => ⟨level x, rfl⟩)
  · intro x hx y hy hxy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact hSep a b (fun h => hxy (congrArg value h))
  · intro z
    rw [Measure.map_apply hMeas (measurableSet_singleton z)]
    have hEvent : (fun x => value (level x)) ⁻¹' {z} = {x | value (level x) = z} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [hEvent, finiteUniformMeasure_apply]
    exact ENNReal.ofReal_le_ofReal (balanced_complex_atom_bound level value hInj hBalance z)

theorem balanced_separated_uniform_sum {α β : Type*}
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype β]
    (level : α → β) (value : β → ℂ) {m : ℕ} (hm : 1 ≤ m)
    {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    (hSep : ∀ a b, a ≠ b → δ ≤ dist (value a) (value b))
    (hBalance : ∀ a b, Nat.card {x // level x = a} ≤ 4 * Nat.card {x // level x = b}) (z : ℂ) :
    uniformProbability (fun x : Fin m → α => ‖(∑ i, value (level (x i))) - z‖ ≤ t) ≤
      10000 * max ((4 / ((Fintype.card β : ℝ) + 3)) * t ^ 2 / ((m : ℝ) * δ ^ 2))
        (4 / ((Fintype.card β : ℝ) + 3)) := by
  classical
  let μ := finiteUniformMeasure (Fin m → α)
  let X := fun i (x : Fin m → α) => value (level (x i))
  have hX : ∀ i, Measurable (X i) := fun _ => measurable_of_finite _
  have hInd : iIndepFun X μ := by
    dsimp only [μ, X]
    rw [finiteUniformMeasure_pi]
    exact iIndepFun_pi (fun _ => (measurable_of_finite (fun x => value (level x))).aemeasurable)
  have hLaw (i : Fin m) : μ.map (X i) =
      (finiteUniformMeasure α).map (fun x => value (level x)) := by
    have hCoord : Measurable (fun x : Fin m → α => x i) := measurable_pi_apply i
    have h := (measurePreserving_eval (fun _ : Fin m => finiteUniformMeasure α) i).map_eq
    rw [← finiteUniformMeasure_pi] at h
    rw [← h, Measure.map_map (measurable_of_finite _) hCoord]
    rfl
  have h := separated_planar_independent_sum_small_ball μ hm X hX hInd hδ
    (by positivity : 0 < 4 / ((Fintype.card β : ℝ) + 3)) ht
    (fun i => by rw [hLaw i]; exact balanced_separated_uniform_law level value hδ hSep hBalance) z
  rw [finiteUniformMeasure_apply] at h
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [μ, X, ENNReal.toReal_ofReal (uniformProbability_nonneg _),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 10000 *
      max ((4 / ((Fintype.card β : ℝ) + 3)) * t ^ 2 / ((m : ℝ) * δ ^ 2))
        (4 / ((Fintype.card β : ℝ) + 3)))] using hReal

theorem regular_block_scale_bound {h m d : ℕ} (hh : 0 < h) (hm : 1 ≤ m) (hmd : m ≤ d)
    {τ k : ℝ} (hτ : 1 ≤ τ) (hk : 0 < k) :
    10000 * max ((4 / ((h : ℝ) + 3)) * (τ * Real.sqrt (d : ℝ) / k) ^ 2 /
        ((m : ℝ) * (1 / k) ^ 2)) (4 / ((h : ℝ) + 3)) ≤
      40000 * τ ^ 2 * ((h : ℝ) * ((m : ℝ) / (d : ℝ)))⁻¹ := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmdR : (m : ℝ) ≤ d := by exact_mod_cast hmd
  have hdR : (0 : ℝ) < d := hmR.trans_le hmdR
  have hτ2 : 1 ≤ τ ^ 2 := by nlinarith
  have hScale : (τ * Real.sqrt (d : ℝ) / k) ^ 2 / ((m : ℝ) * (1 / k) ^ 2) =
      τ ^ 2 * (d : ℝ) / (m : ℝ) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hdR.le]
    field_simp
  have hWeight : ((h : ℝ) * ((m : ℝ) / (d : ℝ)))⁻¹ = (d : ℝ) / ((h : ℝ) * (m : ℝ)) := by
    field_simp
  have hMax : max ((4 / ((h : ℝ) + 3)) * (τ * Real.sqrt (d : ℝ) / k) ^ 2 /
      ((m : ℝ) * (1 / k) ^ 2)) (4 / ((h : ℝ) + 3)) ≤
      4 * τ ^ 2 * (d : ℝ) / ((h : ℝ) * (m : ℝ)) := by
    apply max_le
    · rw [mul_div_assoc, hScale]
      have hAtom : 4 / ((h : ℝ) + 3) ≤ 4 / (h : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hhR (by linarith)
      exact (mul_le_mul_of_nonneg_right hAtom (by positivity)).trans_eq (by field_simp)
    · apply (le_div_iff₀ (mul_pos hhR hmR)).mpr
      have hAtom : 4 / ((h : ℝ) + 3) * (h : ℝ) ≤ 4 := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (h : ℝ) + 3)).mpr
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hAtom hmR.le]
  calc
    _ ≤ 10000 * (4 * τ ^ 2 * (d : ℝ) / ((h : ℝ) * (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hMax (by norm_num)
    _ = _ := by rw [hWeight]; ring

theorem regular_balanced_block_small_ball {α β : Type*}
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype β]
    (level : α → β) (value : β → ℂ) {m d : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    {τ k : ℝ} (hτ : 1 ≤ τ) (hk : 0 < k)
    (hSep : ∀ a b, a ≠ b → 1 / k ≤ dist (value a) (value b))
    (hBalance : ∀ a b, Nat.card {x // level x = a} ≤ 4 * Nat.card {x // level x = b}) (z : ℂ) :
    uniformProbability (fun x : Fin m → α =>
      ‖(∑ i, value (level (x i))) - z‖ ≤ τ * Real.sqrt (d : ℝ) / k) ≤
      40000 * τ ^ 2 * ((Fintype.card β : ℝ) * ((m : ℝ) / (d : ℝ)))⁻¹ := by
  haveI : Nonempty β := ⟨level (Classical.choice inferInstance)⟩
  exact (balanced_separated_uniform_sum level value hm (by positivity : 0 < 1 / k)
    (by positivity : 0 ≤ τ * Real.sqrt (d : ℝ) / k) hSep hBalance z).trans
    (regular_block_scale_bound Fintype.card_pos hm hmd hτ hk)

end CircularLaw
