import CircularLaw.FiniteProbabilitySupremum
import CircularLaw.FiniteConditioning
import CircularLaw.CoordinateDiskEvents
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The actual concentration function of finite complex samples

The supremum over all complex disk centres is attained. Its value is in
[0,1], and for continuously varying finite sample values it is measurable,
including closed disk boundaries. This supports the expectation of the
fresh row-slice concentration function in the manuscript.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def finiteDiskConcentration {α : Type*} [Fintype α] (y : α → ℂ) (r : ℝ) : ℝ :=
  ⨆ w : ℂ, uniformProbability (fun s : α => ‖y s - w‖ ≤ r)

theorem finiteDiskConcentration_attained {α : Type*} [Fintype α] (y : α → ℂ) (r : ℝ) :
    ∃ w : ℂ, uniformProbability (fun s : α => ‖y s - w‖ ≤ r) = finiteDiskConcentration y r :=
  uniformProbability_ciSup_attained _

theorem finiteDiskConcentration_nonneg {α : Type*} [Fintype α] (y : α → ℂ) (r : ℝ) :
    0 ≤ finiteDiskConcentration y r := by
  obtain ⟨w, hw⟩ := finiteDiskConcentration_attained y r
  rw [← hw]
  exact uniformProbability_nonneg _

theorem finiteDiskConcentration_le_one {α : Type*} [Fintype α] (y : α → ℂ) (r : ℝ) :
    finiteDiskConcentration y r ≤ 1 := by
  obtain ⟨w, hw⟩ := finiteDiskConcentration_attained y r
  rw [← hw]
  exact uniformProbability_le_one _

theorem uniformProbability_le_finiteDiskConcentration {α : Type*} [Fintype α]
    (y : α → ℂ) (r : ℝ) (w : ℂ) :
    uniformProbability (fun s : α => ‖y s - w‖ ≤ r) ≤ finiteDiskConcentration y r := by
  have hBound : BddAbove (Set.range (fun v : ℂ =>
      uniformProbability (fun s : α => ‖y s - v‖ ≤ r))) :=
    ⟨1, by rintro _ ⟨v, rfl⟩; exact uniformProbability_le_one _⟩
  exact le_ciSup hBound w

theorem finiteDiskConcentration_le {α : Type*} [Fintype α]
    (y : α → ℂ) (r B : ℝ)
    (h : ∀ w : ℂ, uniformProbability (fun s : α => ‖y s - w‖ ≤ r) ≤ B) :
    finiteDiskConcentration y r ≤ B := by
  obtain ⟨w, hw⟩ := finiteDiskConcentration_attained y r
  rw [← hw]
  exact h w

theorem finiteDiskConcentration_mono_radius {α : Type*} [Fintype α]
    (y : α → ℂ) {r R : ℝ} (h : r ≤ R) : finiteDiskConcentration y r ≤ finiteDiskConcentration y R := by
  apply finiteDiskConcentration_le
  intro w
  exact (uniformProbability_mono (α := α) (fun _ hs => hs.trans h)).trans
    (uniformProbability_le_finiteDiskConcentration y R w)

theorem finiteDiskConcentration_measurable {X α : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [Fintype α] [Nonempty α]
    (Y : X → α → ℂ) (hY : ∀ s, Continuous (fun x => Y x s)) (r : ℝ) :
    Measurable (fun x => finiteDiskConcentration (Y x) r) := by
  apply measurable_of_Ioi
  intro b
  by_cases hb : b < 0
  · have hEq : (fun x => finiteDiskConcentration (Y x) r) ⁻¹' Set.Ioi b = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact hb.trans_le (finiteDiskConcentration_nonneg _ _)
    rw [hEq]
    exact MeasurableSet.univ
  · have hb0 : 0 ≤ b := le_of_not_gt hb
    let D := Fintype.card α
    let e := Fintype.equivFin α
    have hD : (0 : ℝ) < D := by exact_mod_cast Fintype.card_pos
    have hProb (x : X) (w : ℂ) :
        uniformProbability (fun s : α => ‖Y x s - w‖ ≤ r) =
          ((Finset.univ.filter (fun j : Fin D => ‖Y x (e.symm j) - w‖ ≤ r)).card : ℝ) / D := by
      have h := uniformProbability_reindex e (fun j : Fin D => ‖Y x (e.symm j) - w‖ ≤ r)
      simpa only [Equiv.symm_apply_apply, uniformProbability, Nat.card_eq_fintype_card,
        Fintype.card_subtype, Fintype.card_fin] using h
    have hEq : (fun x => finiteDiskConcentration (Y x) r) ⁻¹' Set.Ioi b =
        {x | ∃ w : ℂ, ⌊b * D⌋₊ + 1 ≤
          (Finset.univ.filter (fun j : Fin D => ‖Y x (e.symm j) - w‖ ≤ r)).card} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq]
      constructor
      · intro hx
        obtain ⟨w, hw⟩ := finiteDiskConcentration_attained (Y x) r
        refine ⟨w, ?_⟩
        rw [← hw, hProb] at hx
        have hFloor := (Nat.floor_lt (mul_nonneg hb0 hD.le)).mpr ((lt_div_iff₀ hD).mp hx)
        omega
      · rintro ⟨w, hw⟩
        have hFloor : ⌊b * D⌋₊ <
            (Finset.univ.filter (fun j : Fin D => ‖Y x (e.symm j) - w‖ ≤ r)).card := by omega
        have hReal := (Nat.floor_lt (mul_nonneg hb0 hD.le)).mp hFloor
        apply lt_of_lt_of_le _ (uniformProbability_le_finiteDiskConcentration (Y x) r w)
        rw [hProb]
        exact (lt_div_iff₀ hD).mpr hReal
    rw [hEq]
    exact coordinate_large_disk_measurableSet (fun x j => Y x (e.symm j))
      (fun j => hY (e.symm j)) Finset.univ (⌊b * D⌋₊ + 1) r

def rowSliceDiskConcentration {n d : ℕ} (y : Fin n → ℂ) (r : ℝ) : ℝ :=
  finiteDiskConcentration (fun s : RowSlice n d => ∑ j ∈ s.val, y j) r

theorem rowSliceDiskConcentration_measurable {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {n d : ℕ} (hdn : d ≤ n)
    (Y : X → Fin n → ℂ) (hY : ∀ j, Continuous (fun x => Y x j)) (r : ℝ) :
    Measurable (fun x => rowSliceDiskConcentration (d := d) (Y x) r) := by
  haveI := rowSlice_nonempty hdn
  apply finiteDiskConcentration_measurable
  intro s
  exact continuous_finset_sum _ (fun j _ => hY j)

end CircularLaw
