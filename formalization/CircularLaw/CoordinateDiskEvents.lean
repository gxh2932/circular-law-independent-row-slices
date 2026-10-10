import CircularLaw.ClusterPairCounting
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Measurability of coordinate disk events

For finitely many continuous complex coordinates, the existence of a disk
containing a prescribed number of coordinates is closed. A member of a
nonempty cluster anchors its centre in a fixed compact ball; compact
projection proves closedness, including closed-disk boundary cases.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem coordinate_common_disk_isClosed {X : Type*} [TopologicalSpace X] {n : ℕ}
    (Y : X → Fin n → ℂ) (hY : ∀ j, Continuous (fun x => Y x j))
    (S : Finset (Fin n)) (r : ℝ) :
    IsClosed {x | ∃ w : ℂ, ∀ j ∈ S, ‖Y x j - w‖ ≤ r} := by
  by_cases hS : S.Nonempty
  · obtain ⟨i, hi⟩ := hS
    let B := Metric.closedBall (0 : ℂ) r
    letI : CompactSpace B := (isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) r))
    let F : Set (X × B) := {p | ∀ j ∈ S, ‖Y p.1 j - Y p.1 i - (p.2 : ℂ)‖ ≤ r}
    have hClosed : IsClosed F := by
      simp only [F, Set.setOf_forall]
      apply isClosed_iInter
      intro j
      apply isClosed_iInter
      intro _hj
      exact isClosed_le
        ((((hY j).comp continuous_fst).sub ((hY i).comp continuous_fst)).sub
          (continuous_subtype_val.comp continuous_snd)).norm continuous_const
    have hEq : Prod.fst '' F = {x | ∃ w : ℂ, ∀ j ∈ S, ‖Y x j - w‖ ≤ r} := by
      ext x
      constructor
      · rintro ⟨⟨x', v⟩, hv, rfl⟩
        refine ⟨Y x' i + (v : ℂ), fun j hj => ?_⟩
        have h := hv j hj
        convert h using 1
        congr 1
        ring
      · rintro ⟨w, hw⟩
        have hv : w - Y x i ∈ B := by
          simpa only [B, Metric.mem_closedBall, dist_zero_right, norm_sub_rev] using hw i hi
        refine ⟨(x, ⟨w - Y x i, hv⟩), ?_, rfl⟩
        intro j hj
        convert hw j hj using 1
        congr 1
        ring
    rw [← hEq]
    exact isClosedMap_fst_of_compactSpace F hClosed
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty]

theorem coordinate_large_disk_iff {n t : ℕ} (K : Finset (Fin n)) (y : Fin n → ℂ) (r : ℝ) :
    (∃ w : ℂ, t ≤ (K.filter (fun j => ‖y j - w‖ ≤ r)).card) ↔
      ∃ S ∈ K.powerset, t ≤ S.card ∧ ∃ w : ℂ, ∀ j ∈ S, ‖y j - w‖ ≤ r := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨K.filter (fun j => ‖y j - w‖ ≤ r),
      Finset.mem_powerset.mpr (Finset.filter_subset _ _), hw,
      w, fun _ hj => (Finset.mem_filter.mp hj).2⟩
  · rintro ⟨S, hSK, ht, w, hw⟩
    refine ⟨w, ht.trans (Finset.card_le_card ?_)⟩
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mp hSK hj, hw j hj⟩

theorem coordinate_large_disk_isClosed {X : Type*} [TopologicalSpace X] {n : ℕ}
    (Y : X → Fin n → ℂ) (hY : ∀ j, Continuous (fun x => Y x j))
    (K : Finset (Fin n)) (t : ℕ) (r : ℝ) :
    IsClosed {x | ∃ w : ℂ, t ≤ (K.filter (fun j => ‖Y x j - w‖ ≤ r)).card} := by
  have hEq : {x | ∃ w : ℂ, t ≤ (K.filter (fun j => ‖Y x j - w‖ ≤ r)).card} =
      ⋃ S ∈ K.powerset.filter (fun S => t ≤ S.card),
        {x | ∃ w : ℂ, ∀ j ∈ S, ‖Y x j - w‖ ≤ r} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter]
    rw [coordinate_large_disk_iff]
    aesop
  rw [hEq]
  exact isClosed_biUnion_finset (fun S _ => coordinate_common_disk_isClosed Y hY S r)

theorem coordinate_large_disk_measurableSet {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {n : ℕ}
    (Y : X → Fin n → ℂ) (hY : ∀ j, Continuous (fun x => Y x j))
    (K : Finset (Fin n)) (t : ℕ) (r : ℝ) :
    MeasurableSet {x | ∃ w : ℂ, t ≤ (K.filter (fun j => ‖Y x j - w‖ ≤ r)).card} :=
  (coordinate_large_disk_isClosed Y hY K t r).measurableSet

theorem coordinate_all_disks_card_measurableSet {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {n : ℕ}
    (Y : X → Fin n → ℂ) (hY : ∀ j, Continuous (fun x => Y x j))
    (K : Finset (Fin n)) (t : ℕ) (r : ℝ) :
    MeasurableSet {x | ∀ w : ℂ, (K.filter (fun j => ‖Y x j - w‖ ≤ r)).card ≤ t} := by
  have hEq : {x | ∀ w : ℂ, (K.filter (fun j => ‖Y x j - w‖ ≤ r)).card ≤ t} =
      {x | ∃ w : ℂ, t + 1 ≤ (K.filter (fun j => ‖Y x j - w‖ ≤ r)).card}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_le, Nat.lt_succ_iff]
  rw [hEq]
  exact (coordinate_large_disk_measurableSet Y hY K (t + 1) r).compl

end CircularLaw
