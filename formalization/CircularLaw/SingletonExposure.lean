import CircularLaw.SingletonBlockConcentration

/-!
# The actual row exposure used for equal-block witnesses

The statistic records which disjoint blocks have singleton intersection
and fixes all selected coordinates outside those singleton blocks. Its
fiber is exactly the support fiber constructed above, not an assumed
conditional distribution.
-/

noncomputable section

namespace CircularLaw

def singletonWitnessMask {n d : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → Finset (Fin n)) (S : RowSlice n d) : Finset ι :=
  Finset.univ.filter (fun q => (S.val ∩ J q).card = 1)

def singletonWitnessFixed {n d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → Finset (Fin n)) (S : RowSlice n d) : Finset (Fin n) :=
  S.val \ (singletonWitnessMask J S).biUnion J

def singletonExposure {n d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → Finset (Fin n)) (S : RowSlice n d) : Finset ι × Finset (Fin n) :=
  (singletonWitnessMask J S, singletonWitnessFixed J S)

abbrev SingletonWitnessIndices {n d : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → Finset (Fin n)) (S : RowSlice n d) :=
  {q : ι // q ∈ singletonWitnessMask J S}

theorem mem_singletonWitnessMask {n d : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → Finset (Fin n)) (S : RowSlice n d) (q : ι) :
    q ∈ singletonWitnessMask J S ↔ (S.val ∩ J q).card = 1 := by
  simp only [singletonWitnessMask, Finset.mem_filter, Finset.mem_univ, true_and]

theorem singletonWitnessUnion_eq {n d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → Finset (Fin n)) (S : RowSlice n d) :
    singletonBlockUnion (fun q : SingletonWitnessIndices J S => J q.val) =
      (singletonWitnessMask J S).biUnion J := by
  ext j
  rw [mem_singletonBlockUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hj⟩
    exact ⟨q.val, q.property, hj⟩
  · rintro ⟨q, hq, hj⟩
    exact ⟨⟨q, hq⟩, hj⟩

theorem singletonWitnessFixed_disjoint {n d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → Finset (Fin n)) (S : RowSlice n d) (q : SingletonWitnessIndices J S) :
    Disjoint (singletonWitnessFixed J S) (J q.val) := by
  apply Finset.disjoint_left.mpr
  intro j hjFixed hjq
  exact (Finset.mem_sdiff.mp hjFixed).2 (Finset.mem_biUnion.mpr ⟨q.val, q.property, hjq⟩)

theorem singletonWitness_reference_fiber {n d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → Finset (Fin n)) (S : RowSlice n d) :
    S.val \ singletonBlockUnion (fun q : SingletonWitnessIndices J S => J q.val) =
      singletonWitnessFixed J S ∧
      ∀ q : SingletonWitnessIndices J S, (S.val ∩ J q.val).card = 1 := by
  refine ⟨?_, fun q => (mem_singletonWitnessMask J S q.val).mp q.property⟩
  rw [singletonWitnessUnion_eq]
  rfl

theorem singletonWitness_degree {n d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → Finset (Fin n)) (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (S : RowSlice n d) :
    (singletonWitnessFixed J S).card + Fintype.card (SingletonWitnessIndices J S) = d := by
  have hDisSub : Pairwise (fun q p : SingletonWitnessIndices J S => Disjoint (J q.val) (J p.val)) :=
    fun _ _ hne => hDis (fun h => hne (Subtype.ext h))
  have h := singletonBlockFiber_card_support (singletonWitnessFixed J S)
    (fun q : SingletonWitnessIndices J S => J q.val) hDisSub
    (singletonWitnessFixed_disjoint J S) ⟨S.val, singletonWitness_reference_fiber J S⟩
  exact h.symm.trans S.property

theorem sdiff_inter_eq_of_disjoint {α : Type*} [DecidableEq α]
    (S U T : Finset α) (hDis : Disjoint U T) : (S \ U) ∩ T = S ∩ T := by
  ext j
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, fun hjU => Finset.disjoint_left.mp hDis hjU h.2⟩, h.2⟩

theorem singletonWitnessUnion_disjoint_inactive {n d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → Finset (Fin n)) (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (S : RowSlice n d) (q : ι) (hq : q ∉ singletonWitnessMask J S) :
    Disjoint ((singletonWitnessMask J S).biUnion J) (J q) := by
  apply (Finset.disjoint_biUnion_left _ _ _).mpr
  intro p hp
  exact hDis (fun h => hq (h ▸ hp))

theorem singletonExposure_eq_iff_fiber {n d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → Finset (Fin n)) (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (reference S : RowSlice n d) :
    singletonExposure J S = singletonExposure J reference ↔
      S.val \ singletonBlockUnion (fun q : SingletonWitnessIndices J reference => J q.val) =
        singletonWitnessFixed J reference ∧
      ∀ q : SingletonWitnessIndices J reference, (S.val ∩ J q.val).card = 1 := by
  constructor
  · intro hExposure
    have hMask := congrArg Prod.fst hExposure
    have hFixed := congrArg Prod.snd hExposure
    change singletonWitnessMask J S = singletonWitnessMask J reference at hMask
    change singletonWitnessFixed J S = singletonWitnessFixed J reference at hFixed
    refine ⟨?_, ?_⟩
    · rw [singletonWitnessUnion_eq]
      simpa only [singletonWitnessFixed, hMask] using hFixed
    · intro q
      apply (mem_singletonWitnessMask J S q.val).mp
      rw [hMask]
      exact q.property
  · rintro ⟨hOutside, hSingleton⟩
    rw [singletonWitnessUnion_eq] at hOutside
    have hMask : singletonWitnessMask J S = singletonWitnessMask J reference := by
      ext q
      by_cases hq : q ∈ singletonWitnessMask J reference
      · have hqS := (mem_singletonWitnessMask J S q).mpr (hSingleton ⟨q, hq⟩)
        exact iff_of_true hqS hq
      · have hDisq := singletonWitnessUnion_disjoint_inactive J hDis reference q hq
        have hInter : S.val ∩ J q = reference.val ∩ J q := by
          rw [← sdiff_inter_eq_of_disjoint S.val _ (J q) hDisq, hOutside]
          exact sdiff_inter_eq_of_disjoint reference.val _ (J q) hDisq
        have hqS : q ∉ singletonWitnessMask J S := by
          intro h
          apply hq
          apply (mem_singletonWitnessMask J reference q).mpr
          rw [← hInter]
          exact (mem_singletonWitnessMask J S q).mp h
        exact iff_of_false hqS hq
    apply Prod.ext hMask
    change singletonWitnessFixed J S = singletonWitnessFixed J reference
    simpa only [singletonWitnessFixed, hMask] using hOutside

def singletonExposureFiberEquiv {n d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → Finset (Fin n)) (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (reference : RowSlice n d) :
    {S : RowSlice n d // singletonExposure J S = singletonExposure J reference} ≃
      SingletonBlockChoices (fun q : SingletonWitnessIndices J reference => J q.val) :=
  (Equiv.subtypeEquivRight (singletonExposure_eq_iff_fiber J hDis reference)).trans
    (singletonBlockSliceFiberEquiv (singletonWitnessFixed J reference)
      (fun q : SingletonWitnessIndices J reference => J q.val)
      (fun _ _ hne => hDis (fun h => hne (Subtype.ext h)))
      (singletonWitnessFixed_disjoint J reference) (singletonWitness_degree J hDis reference))

end CircularLaw
