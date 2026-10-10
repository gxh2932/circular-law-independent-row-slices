import CircularLaw.SingletonBlockCompletion

/-!
# Exact singleton-block exposure fibers

Fixing the coordinates outside disjoint witness blocks and requiring one
selected coordinate in each block leaves exactly the Cartesian product
of those blocks. The equivalence is proved for genuine support sets and
then for row slices of the prescribed degree.
-/

noncomputable section

namespace CircularLaw

abbrev SingletonBlockFiber {n : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n)) :=
  {S : Finset (Fin n) // S \ singletonBlockUnion J = fixed ∧ ∀ q, (S ∩ J q).card = 1}

def singletonBlockFiberChoice {n : ℕ} {ι : Type*} [Fintype ι]
    {fixed : Finset (Fin n)} {J : ι → Finset (Fin n)}
    (S : SingletonBlockFiber fixed J) : SingletonBlockChoices J := fun q =>
  let h := Finset.card_eq_one.mp (S.property.2 q)
  ⟨Classical.choose h, by
    have hMem : Classical.choose h ∈ S.val ∩ J q := by
      exact Eq.mpr (congrArg (fun T : Finset (Fin n) => Classical.choose h ∈ T)
        (Classical.choose_spec h)) (Finset.mem_singleton_self _)
    exact (Finset.mem_inter.mp hMem).2⟩

theorem singletonBlockFiberChoice_inter {n : ℕ} {ι : Type*} [Fintype ι]
    {fixed : Finset (Fin n)} {J : ι → Finset (Fin n)}
    (S : SingletonBlockFiber fixed J) (q : ι) :
    S.val ∩ J q = {(singletonBlockFiberChoice S q).val} :=
  Classical.choose_spec (Finset.card_eq_one.mp (S.property.2 q))

theorem singletonBlockFiberChoice_mem {n : ℕ} {ι : Type*} [Fintype ι]
    {fixed : Finset (Fin n)} {J : ι → Finset (Fin n)}
    (S : SingletonBlockFiber fixed J) (q : ι) : (singletonBlockFiberChoice S q).val ∈ S.val := by
  have h : (singletonBlockFiberChoice S q).val ∈ S.val ∩ J q := by
    rw [singletonBlockFiberChoice_inter S q]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_inter.mp h).1

theorem singletonBlockFiber_eq_completion {n : ℕ} {ι : Type*} [Fintype ι]
    {fixed : Finset (Fin n)} {J : ι → Finset (Fin n)}
    (S : SingletonBlockFiber fixed J) :
    S.val = singletonBlockCompletion fixed J (singletonBlockFiberChoice S) := by
  ext j
  constructor
  · intro hj
    by_cases hUnion : j ∈ singletonBlockUnion J
    · obtain ⟨q, hjq⟩ := (mem_singletonBlockUnion J j).mp hUnion
      have hInter := Finset.mem_inter.mpr ⟨hj, hjq⟩
      rw [singletonBlockFiberChoice_inter S q] at hInter
      have hEq := Finset.mem_singleton.mp hInter
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hEq.symm⟩)
    · have hFixed : j ∈ fixed := by
        rw [← S.property.1]
        exact Finset.mem_sdiff.mpr ⟨hj, hUnion⟩
      exact Finset.mem_union_left _ hFixed
  · intro hj
    rcases Finset.mem_union.mp hj with hFixed | hChoice
    · rw [← S.property.1] at hFixed
      exact (Finset.mem_sdiff.mp hFixed).1
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hChoice
      exact singletonBlockFiberChoice_mem S q

def singletonBlockFiberEquiv {n : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (hFixed : ∀ q, Disjoint fixed (J q)) :
    SingletonBlockFiber fixed J ≃ SingletonBlockChoices J where
  toFun := singletonBlockFiberChoice
  invFun U := ⟨singletonBlockCompletion fixed J U,
    singletonBlockCompletion_outside fixed J hFixed U,
    fun q => by rw [singletonBlockCompletion_inter fixed J hDis hFixed U q]; exact Finset.card_singleton _⟩
  left_inv S := Subtype.ext (singletonBlockFiber_eq_completion S).symm
  right_inv U := by
    funext q
    apply Subtype.ext
    have hEq := singletonBlockFiberChoice_inter
      (⟨singletonBlockCompletion fixed J U,
        singletonBlockCompletion_outside fixed J hFixed U,
        fun q => by rw [singletonBlockCompletion_inter fixed J hDis hFixed U q]; exact Finset.card_singleton _⟩ :
        SingletonBlockFiber fixed J) q
    rw [singletonBlockCompletion_inter fixed J hDis hFixed U q] at hEq
    exact (Finset.singleton_injective hEq).symm

theorem singletonBlockFiber_card_support {n : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (hFixed : ∀ q, Disjoint fixed (J q)) (S : SingletonBlockFiber fixed J) :
    S.val.card = fixed.card + Fintype.card ι := by
  rw [singletonBlockFiber_eq_completion S]
  exact singletonBlockCompletion_card fixed J hDis hFixed _

abbrev SingletonBlockSliceFiber {n d : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n)) :=
  {S : RowSlice n d // S.val \ singletonBlockUnion J = fixed ∧ ∀ q, (S.val ∩ J q).card = 1}

def singletonBlockSliceSupportEquiv {n d : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (hFixed : ∀ q, Disjoint fixed (J q)) (hDegree : fixed.card + Fintype.card ι = d) :
    SingletonBlockSliceFiber (d := d) fixed J ≃ SingletonBlockFiber fixed J where
  toFun S := ⟨S.val.val, S.property⟩
  invFun S := ⟨⟨S.val, (singletonBlockFiber_card_support fixed J hDis hFixed S).trans hDegree⟩, S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def singletonBlockSliceFiberEquiv {n d : ℕ} {ι : Type*} [Fintype ι]
    (fixed : Finset (Fin n)) (J : ι → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (hFixed : ∀ q, Disjoint fixed (J q)) (hDegree : fixed.card + Fintype.card ι = d) :
    SingletonBlockSliceFiber (d := d) fixed J ≃ SingletonBlockChoices J :=
  (singletonBlockSliceSupportEquiv fixed J hDis hFixed hDegree).trans
    (singletonBlockFiberEquiv fixed J hDis hFixed)

end CircularLaw
