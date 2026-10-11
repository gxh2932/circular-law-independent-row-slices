import CircularLaw.GreedyCorrelationClusters
import CircularLaw.GaussianClusterAveraging
import CircularLaw.CoordinateDiskEvents

/-!
# The actual Gaussian greedy exceptional set

The relation uses the actual projected Gaussian probability. Its greedy star
clusters give the source exceptional set and the complete averaging estimate
after its removal. Controlling the size of this set from the structural
hypothesis remains a separate forbidden-vector obligation.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem projectedGaussianStronglyCorrelated_refl {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (i : Fin n) :
    projectedGaussianStronglyCorrelated E α β i i := by
  unfold projectedGaussianStronglyCorrelated
  have hSet : {z | α ≤ ‖projectedComplexGaussian E z i - projectedComplexGaussian E z i‖} =
      (∅ : Set (Fin n → ℂ)) := by
    ext z
    simp only [sub_self, norm_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    linarith
  rw [hSet, measureReal_empty]
  exact hβ

theorem projectedGaussianStronglyCorrelated_symm {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (α β : ℝ) (i j : Fin n) :
    projectedGaussianStronglyCorrelated E α β i j ↔
      projectedGaussianStronglyCorrelated E α β j i := by
  unfold projectedGaussianStronglyCorrelated
  simp only [norm_sub_rev]

theorem projectedGaussianStronglyCorrelated_triangle {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j k : Fin n)
    {α₁ α₂ β₁ β₂ : ℝ}
    (h₁ : projectedGaussianStronglyCorrelated E α₁ β₁ i j)
    (h₂ : projectedGaussianStronglyCorrelated E α₂ β₂ j k) :
    projectedGaussianStronglyCorrelated E (α₁ + α₂) (β₁ + β₂) i k := by
  have hContain :
      {z | α₁ + α₂ ≤ ‖projectedComplexGaussian E z i - projectedComplexGaussian E z k‖} ⊆
        {z | α₁ ≤ ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j‖} ∪
        {z | α₂ ≤ ‖projectedComplexGaussian E z j - projectedComplexGaussian E z k‖} := by
    intro z hz
    simp only [Set.mem_union, Set.mem_setOf_eq] at hz ⊢
    by_contra h
    push_neg at h
    have hTriangle : ‖projectedComplexGaussian E z i - projectedComplexGaussian E z k‖ ≤
        ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j‖ +
        ‖projectedComplexGaussian E z j - projectedComplexGaussian E z k‖ := by
      calc
        _ = ‖(projectedComplexGaussian E z i - projectedComplexGaussian E z j) +
          (projectedComplexGaussian E z j - projectedComplexGaussian E z k)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_add_le _ _
    linarith
  unfold projectedGaussianStronglyCorrelated at h₁ h₂ ⊢
  exact (measureReal_mono hContain).trans
    ((measureReal_union_le _ _).trans (add_le_add h₁ h₂))

def projectedGaussianExceptional {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (b : ℕ) : Finset (Fin n) :=
  greedyCorrelationExceptional (projectedGaussianStronglyCorrelated E α β)
    (projectedGaussianStronglyCorrelated_refl E hα hβ) b

theorem projectedGaussian_greedy_cluster_pairs {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (α β : ℝ) (k : ℕ)
    {i j : Fin n}
    (hi : i ∈ greedyCorrelationStage (projectedGaussianStronglyCorrelated E α β) k)
    (hj : j ∈ greedyCorrelationStage (projectedGaussianStronglyCorrelated E α β) k) :
    projectedGaussianStronglyCorrelated E (2 * α) (2 * β) i j := by
  obtain ⟨u, _, hU⟩ := greedyCorrelationStage_representative
    (projectedGaussianStronglyCorrelated E α β) k ⟨i, hi⟩
  have h₁ := (projectedGaussianStronglyCorrelated_symm E α β u i).mp (hU i hi)
  have h₂ := hU j hj
  simpa only [two_mul] using projectedGaussianStronglyCorrelated_triangle E i u j h₁ h₂

theorem projectedGaussianExceptional_neighbors {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (b : ℕ) {i : Fin n}
    (hi : i ∈ Finset.univ \ projectedGaussianExceptional E hα hβ b) :
    ((Finset.univ \ projectedGaussianExceptional E hα hβ b).filter
      (projectedGaussianStronglyCorrelated E α β i)).card ≤ b :=
  greedyCorrelationExceptional_neighbors (projectedGaussianStronglyCorrelated E α β)
    (projectedGaussianStronglyCorrelated_refl E hα hβ) b hi

theorem projectedGaussian_greedy_anti_cluster {n b : ℕ} (hb : 0 < b)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (hs : 0 ≤ s) :
    (standardComplexGaussianVectorLaw n).real
      {z | ∃ w : ℂ, 2 * b ≤
        ((Finset.univ \ projectedGaussianExceptional E hα hβ.le b).filter
          (fun j => ‖projectedComplexGaussian E z j - w‖ ≤
            gaussianClusterRadius α β s)).card} ≤ (s * (n : ℝ)) ^ 2 / (2 * (b : ℝ) ^ 2) :=
  projectedGaussian_bounded_correlation_anti_cluster hb E _ hα hβ hβ1 hs
    (fun _ hi => projectedGaussianExceptional_neighbors E hα hβ.le b hi)

theorem projectedGaussian_greedy_anti_cluster_success {n b : ℕ} (hb : 0 < b)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (hs : 0 ≤ s) :
    1 - (s * (n : ℝ)) ^ 2 / (2 * (b : ℝ) ^ 2) ≤
      (standardComplexGaussianVectorLaw n).real
        {z | ∀ w : ℂ,
          ((Finset.univ \ projectedGaussianExceptional E hα hβ.le b).filter
            (fun j => ‖projectedComplexGaussian E z j - w‖ ≤
              gaussianClusterRadius α β s)).card < 2 * b} := by
  have hContinuous (j : Fin n) : Continuous (fun z => projectedComplexGaussian E z j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
      (projectedComplexGaussian_continuous E)
  have hMeas := coordinate_large_disk_measurableSet
    (fun z j => projectedComplexGaussian E z j) hContinuous
    (Finset.univ \ projectedGaussianExceptional E hα hβ.le b) (2 * b)
    (gaussianClusterRadius α β s)
  have hBound := projectedGaussian_greedy_anti_cluster hb E hα hβ hβ1 hs
  have hComplement :
      {z | ∃ w : ℂ, 2 * b ≤
        ((Finset.univ \ projectedGaussianExceptional E hα hβ.le b).filter
          (fun j => ‖projectedComplexGaussian E z j - w‖ ≤ gaussianClusterRadius α β s)).card}ᶜ =
      {z | ∀ w : ℂ,
        ((Finset.univ \ projectedGaussianExceptional E hα hβ.le b).filter
          (fun j => ‖projectedComplexGaussian E z j - w‖ ≤ gaussianClusterRadius α β s)).card <
            2 * b} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_le]
  rw [← hComplement, probReal_compl_eq_one_sub hMeas]
  linarith

theorem projectedGaussian_greedy_anti_cluster_card_le {n b L : ℕ} (hb : 0 < b)
    (hL : 2 * b ≤ L) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β s r : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (hs : 0 ≤ s)
    (hr : r ≤ gaussianClusterRadius α β s) :
    1 - (s * (n : ℝ)) ^ 2 / (2 * (b : ℝ) ^ 2) ≤
      (standardComplexGaussianVectorLaw n).real
        {z | ∀ w : ℂ,
          ((Finset.univ \ projectedGaussianExceptional E hα hβ.le b).filter
            (fun j => ‖projectedComplexGaussian E z j - w‖ ≤ r)).card ≤ L} := by
  apply (projectedGaussian_greedy_anti_cluster_success hb E hα hβ hβ1 hs).trans
  refine measureReal_mono ?_
  intro z hz w
  have hSubset :
      (Finset.univ \ projectedGaussianExceptional E hα hβ.le b).filter
        (fun j => ‖projectedComplexGaussian E z j - w‖ ≤ r) ⊆
      (Finset.univ \ projectedGaussianExceptional E hα hβ.le b).filter
        (fun j => ‖projectedComplexGaussian E z j - w‖ ≤ gaussianClusterRadius α β s) := by
    intro j hj
    obtain ⟨hjK, hjr⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hjK, hjr.trans hr⟩
  exact ((Finset.card_le_card hSubset).trans (hz w).le).trans hL

end CircularLaw
