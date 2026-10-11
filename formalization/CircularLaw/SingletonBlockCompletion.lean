import CircularLaw.EqualBlockAtom

/-!
# Completing a row from singleton block choices

After fixing all other selected coordinates, each disjoint singleton block
contributes one coordinate. Their union is an actual row support, and its
cardinality is the number of fixed coordinates plus the number of blocks.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def singletonBlockUnion {n : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → Finset (Fin n)) : Finset (Fin n) := Finset.univ.biUnion J

abbrev SingletonBlockChoices {n : ℕ} {ι : Type*} (J : ι → Finset (Fin n)) :=
  ∀ q, {j : Fin n // j ∈ J q}

def singletonBlockSelected {n : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → Finset (Fin n)) (U : SingletonBlockChoices J) : Finset (Fin n) :=
  Finset.univ.image (fun q => (U q).val)

def singletonBlockCompletion {n : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n)) (U : SingletonBlockChoices J) :
    Finset (Fin n) := fixed ∪ singletonBlockSelected J U

theorem mem_singletonBlockUnion {n : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → Finset (Fin n)) (j : Fin n) :
    j ∈ singletonBlockUnion J ↔ ∃ q, j ∈ J q := by
  simp only [singletonBlockUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]

theorem singletonBlockSelected_subset_union {n : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → Finset (Fin n)) (U : SingletonBlockChoices J) :
    singletonBlockSelected J U ⊆ singletonBlockUnion J := by
  intro j hj
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hj
  exact (mem_singletonBlockUnion J _).mpr ⟨q, (U q).property⟩

theorem singletonBlockChoices_injective {n : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → Finset (Fin n)) (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (U : SingletonBlockChoices J) : Function.Injective (fun q => (U q).val) := by
  intro q p hEq
  change (U q).val = (U p).val at hEq
  by_contra hne
  have hInP : (U q).val ∈ J p := by
    rw [hEq]
    exact (U p).property
  exact Finset.disjoint_left.mp (hDis hne) (U q).property hInP

theorem singletonBlockSelected_card {n : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → Finset (Fin n)) (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (U : SingletonBlockChoices J) : (singletonBlockSelected J U).card = Fintype.card ι := by
  rw [singletonBlockSelected, Finset.card_image_of_injective _ (singletonBlockChoices_injective J hDis U)]
  exact Finset.card_univ

theorem fixed_disjoint_singletonBlockSelected {n : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hFixed : ∀ q, Disjoint fixed (J q)) (U : SingletonBlockChoices J) :
    Disjoint fixed (singletonBlockSelected J U) := by
  apply Finset.disjoint_left.mpr
  intro j hjFixed hjSelected
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hjSelected
  exact Finset.disjoint_left.mp (hFixed q) hjFixed (U q).property

theorem singletonBlockCompletion_card {n : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (hFixed : ∀ q, Disjoint fixed (J q)) (U : SingletonBlockChoices J) :
    (singletonBlockCompletion fixed J U).card = fixed.card + Fintype.card ι := by
  rw [singletonBlockCompletion, Finset.card_union_of_disjoint
    (fixed_disjoint_singletonBlockSelected fixed J hFixed U), singletonBlockSelected_card J hDis U]

theorem singletonBlockCompletion_outside {n : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hFixed : ∀ q, Disjoint fixed (J q)) (U : SingletonBlockChoices J) :
    singletonBlockCompletion fixed J U \ singletonBlockUnion J = fixed := by
  ext j
  constructor
  · intro hj
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hj).1 with hjFixed | hjSelected
    · exact hjFixed
    · exact False.elim ((Finset.mem_sdiff.mp hj).2
        (singletonBlockSelected_subset_union J U hjSelected))
  · intro hjFixed
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_union_left _ hjFixed, ?_⟩
    intro hjUnion
    obtain ⟨q, hjq⟩ := (mem_singletonBlockUnion J j).mp hjUnion
    exact Finset.disjoint_left.mp (hFixed q) hjFixed hjq

theorem singletonBlockCompletion_inter {n : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (hFixed : ∀ q, Disjoint fixed (J q)) (U : SingletonBlockChoices J) (q : ι) :
    singletonBlockCompletion fixed J U ∩ J q = {(U q).val} := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨hjSupport, hjq⟩ := Finset.mem_inter.mp hj
    rcases Finset.mem_union.mp hjSupport with hjFixed | hjSelected
    · exact False.elim (Finset.disjoint_left.mp (hFixed q) hjFixed hjq)
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hjSelected
      have hpq : p = q := by
        by_contra hne
        exact Finset.disjoint_left.mp (hDis hne) (U p).property hjq
      subst p
      exact Finset.mem_singleton_self _
  · intro hj
    have hEq := Finset.mem_singleton.mp hj
    subst j
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩), (U q).property⟩

theorem singletonBlockCompletion_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (hFixed : ∀ q, Disjoint fixed (J q)) (U : SingletonBlockChoices J) (y : Fin n → ℂ) :
    ∑ j ∈ singletonBlockCompletion fixed J U, y j = (∑ j ∈ fixed, y j) + ∑ q, y (U q).val := by
  rw [singletonBlockCompletion, Finset.sum_union (fixed_disjoint_singletonBlockSelected fixed J hFixed U)]
  congr 1
  rw [singletonBlockSelected, Finset.sum_image]
  intro q _ p _ hEq
  exact singletonBlockChoices_injective J hDis U hEq

end CircularLaw
