import CircularLaw.GaussianGreedyClusters
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# A unit combination with equal representative coordinates

For any `p+1` vectors and `p+1` cluster representatives, the `p` coordinate
difference constraints have a nonzero kernel. Normalization supplies the
unit coefficient vector used in the source forbidden-vector construction.
The resulting combination remains in the original orthogonal complement.
Nonzero output and its ordered-coordinate bounds require the separate
Gaussian non-flatness and non-steepness estimates.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def gaussianCopiesCombination {n p : ℕ} (Y : Fin p → EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin p) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  ∑ k, (PiLp.projₗ (𝕜 := ℂ) (β := fun _ : Fin p => ℂ) 2 k).smulRight (Y k)

theorem gaussianCopiesCombination_apply {n p : ℕ} (Y : Fin p → EuclideanSpace ℂ (Fin n))
    (x : EuclideanSpace ℂ (Fin p)) : gaussianCopiesCombination Y x = ∑ k, x k • Y k := by
  simp [gaussianCopiesCombination]

def gaussianRepresentativeConstraints {n p : ℕ}
    (Y : Fin (p + 1) → EuclideanSpace ℂ (Fin n)) (u : Fin (p + 1) → Fin n) :
    EuclideanSpace ℂ (Fin (p + 1)) →ₗ[ℂ] (Fin p → ℂ) :=
  LinearMap.pi (fun j =>
    ((PiLp.projₗ (𝕜 := ℂ) (β := fun _ : Fin n => ℂ) 2 (u j.castSucc)) -
      (PiLp.projₗ (𝕜 := ℂ) (β := fun _ : Fin n => ℂ) 2 (u (Fin.last p)))).comp
      (gaussianCopiesCombination Y))

theorem gaussianRepresentativeConstraints_apply {n p : ℕ}
    (Y : Fin (p + 1) → EuclideanSpace ℂ (Fin n)) (u : Fin (p + 1) → Fin n)
    (x : EuclideanSpace ℂ (Fin (p + 1))) (j : Fin p) :
    gaussianRepresentativeConstraints Y u x j =
      gaussianCopiesCombination Y x (u j.castSucc) -
        gaussianCopiesCombination Y x (u (Fin.last p)) := by
  simp [gaussianRepresentativeConstraints]

theorem gaussianRepresentativeConstraints_ker_ne_bot {n p : ℕ}
    (Y : Fin (p + 1) → EuclideanSpace ℂ (Fin n)) (u : Fin (p + 1) → Fin n) :
    LinearMap.ker (gaussianRepresentativeConstraints Y u) ≠ ⊥ := by
  apply LinearMap.ker_ne_bot_of_finrank_lt
  simp [finrank_euclideanSpace]

theorem gaussianRepresentative_unit_combination {n p : ℕ}
    (Y : Fin (p + 1) → EuclideanSpace ℂ (Fin n)) (u : Fin (p + 1) → Fin n) :
    ∃ x : EuclideanSpace ℂ (Fin (p + 1)), ‖x‖ = 1 ∧
      ∀ j : Fin (p + 1), gaussianCopiesCombination Y x (u j) =
        gaussianCopiesCombination Y x (u (Fin.last p)) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (gaussianRepresentativeConstraints_ker_ne_bot Y u)
  let x : EuclideanSpace ℂ (Fin (p + 1)) := (‖v‖⁻¹ : ℂ) • v
  have hx : x ∈ LinearMap.ker (gaussianRepresentativeConstraints Y u) :=
    (LinearMap.ker _).smul_mem _ hv
  refine ⟨x, norm_smul_inv_norm hv0, ?_⟩
  intro j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
  · have h := congrFun (LinearMap.mem_ker.mp hx) k
    rw [gaussianRepresentativeConstraints_apply] at h
    exact sub_eq_zero.mp h
  · rfl

theorem gaussianCopiesCombination_mem_submodule {n p : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (Y : Fin p → EuclideanSpace ℂ (Fin n))
    (hY : ∀ k, Y k ∈ F) (x : EuclideanSpace ℂ (Fin p)) :
    gaussianCopiesCombination Y x ∈ F := by
  rw [gaussianCopiesCombination_apply]
  exact F.sum_mem (fun k _ => F.smul_mem (x k) (hY k))

theorem gaussianRepresentative_unit_combination_of_pos {n p : ℕ} (hp : 0 < p)
    (Y : Fin p → EuclideanSpace ℂ (Fin n)) (u : Fin p → Fin n) :
    ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
      ∃ w : ℂ, ∀ j : Fin p, gaussianCopiesCombination Y x (u j) = w := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  obtain ⟨x, hx, hEqual⟩ := gaussianRepresentative_unit_combination Y u
  exact ⟨x, hx, gaussianCopiesCombination Y x (u (Fin.last q)), hEqual⟩

theorem projectedGaussianCopies_unit_representative_combination {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (z : Fin (p + 1) → (Fin n → ℂ)) (u : Fin (p + 1) → Fin n) :
    ∃ x : EuclideanSpace ℂ (Fin (p + 1)), ‖x‖ = 1 ∧
      gaussianCopiesCombination (fun k => projectedComplexGaussian E (z k)) x ∈ Eᗮ ∧
      ∀ j : Fin (p + 1),
        gaussianCopiesCombination (fun k => projectedComplexGaussian E (z k)) x (u j) =
          gaussianCopiesCombination (fun k => projectedComplexGaussian E (z k)) x (u (Fin.last p)) := by
  obtain ⟨x, hx, hRep⟩ := gaussianRepresentative_unit_combination
    (fun k => projectedComplexGaussian E (z k)) u
  exact ⟨x, hx, gaussianCopiesCombination_mem_submodule Eᗮ _
    (fun k => projectedComplexGaussian_mem_orthogonal E (z k)) x, hRep⟩

end CircularLaw
