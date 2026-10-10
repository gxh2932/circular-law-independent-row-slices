import CircularLaw.SparseGridNet

/-!
# Finite sparse grids assembled from individually counted layers

Each layer chooses its actual coordinate support and grid values.
The final net is the image of their finite product under vector addition.
Its cardinality is bounded by the product of the literal layer counts.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def sparseCoordinateGrid {n : ℕ} (S : Finset (Fin n)) (A : Finset ℂ) : Finset (Fin n → ℂ) :=
  Fintype.piFinset (fun j => if j ∈ S then A else {0})

def sparseGridFamily (n s : ℕ) (A : Finset ℂ) : Finset (Fin n → ℂ) :=
  (smallCoordinateSets n s).biUnion (fun S => sparseCoordinateGrid S A)

def layeredSparseGridNet {q : ℕ} (n : ℕ) (b : Fin q → ℕ) (A : Fin q → Finset ℂ)
    (s : ℕ) (B : Finset ℂ) : Finset (Fin n → ℂ) :=
  ((Fintype.piFinset (fun i => sparseGridFamily n (b i) (A i))).product
    (sparseGridFamily n s B)).image (fun p => fun j => (∑ i, p.1 i j) + p.2 j)

theorem sparseCoordinateGrid_card {n : ℕ} (S : Finset (Fin n)) (A : Finset ℂ) :
    (sparseCoordinateGrid S A).card = A.card ^ S.card := by
  unfold sparseCoordinateGrid
  rw [Fintype.card_piFinset]
  simp only [apply_ite, Finset.card_singleton]
  rw [Finset.prod_ite_mem_eq]
  simp only [Finset.prod_const]

theorem sparseGridFamily_mem {n s : ℕ} (A : Finset ℂ) (u : Fin n → ℂ) :
    u ∈ sparseGridFamily n s A ↔ ∃ S : Finset (Fin n), S.card ≤ s ∧
      (∀ j ∈ S, u j ∈ A) ∧ (∀ j, j ∉ S → u j = 0) := by
  simp only [sparseGridFamily, Finset.mem_biUnion, mem_smallCoordinateSets,
    sparseCoordinateGrid, Fintype.mem_piFinset]
  constructor
  · rintro ⟨S, hS, hValues⟩
    exact ⟨S, hS, fun j hj => by simpa only [if_pos hj] using hValues j,
      fun j hj => by simpa only [if_neg hj, Finset.mem_singleton] using hValues j⟩
  · rintro ⟨S, hS, hValues, hZero⟩
    refine ⟨S, hS, ?_⟩
    intro j
    by_cases hj : j ∈ S
    · simpa only [if_pos hj] using hValues j hj
    · simpa only [if_neg hj, Finset.mem_singleton] using hZero j hj

theorem sparseGridFamily_card_le {n s : ℕ} (A : Finset ℂ) (hA : A.Nonempty) :
    (sparseGridFamily n s A).card ≤ (smallCoordinateSets n s).card * A.card ^ s := by
  unfold sparseGridFamily
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _S ∈ smallCoordinateSets n s, A.card ^ s := by
      apply Finset.sum_le_sum
      intro S hS
      rw [sparseCoordinateGrid_card]
      exact Nat.pow_le_pow_right (Finset.card_pos.mpr hA) ((mem_smallCoordinateSets S).mp hS)
    _ = _ := by simp only [Finset.sum_const, smul_eq_mul]

theorem layeredSparseGridNet_mem {n q s : ℕ} (b : Fin q → ℕ) (A : Fin q → Finset ℂ)
    (B : Finset ℂ) (v : Fin q → Fin n → ℂ) (w u : Fin n → ℂ)
    (hv : ∀ i, v i ∈ sparseGridFamily n (b i) (A i)) (hw : w ∈ sparseGridFamily n s B)
    (hSum : ∀ j, (∑ i, v i j) + w j = u j) :
    u ∈ layeredSparseGridNet n b A s B := by
  apply Finset.mem_image.mpr
  refine ⟨(v, w), Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr hv, hw⟩, ?_⟩
  exact funext hSum

theorem layeredSparseGridNet_card_le {n q s : ℕ} (b : Fin q → ℕ) (A : Fin q → Finset ℂ)
    (B : Finset ℂ) (hA : ∀ i, (A i).Nonempty) (hB : B.Nonempty) :
    (layeredSparseGridNet n b A s B).card ≤
      (∏ i, (smallCoordinateSets n (b i)).card * (A i).card ^ b i) *
        ((smallCoordinateSets n s).card * B.card ^ s) := by
  unfold layeredSparseGridNet
  apply Finset.card_image_le.trans
  rw [Finset.product_eq_sprod, Finset.card_product, Fintype.card_piFinset]
  apply Nat.mul_le_mul
  · exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      (fun i _ => sparseGridFamily_card_le (A i) (hA i))
  · exact sparseGridFamily_card_le B hB

end CircularLaw
