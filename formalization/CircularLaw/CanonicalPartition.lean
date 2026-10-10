import CircularLaw.LevelInvariants

/-!
# The actual canonical coordinate partition

Nonempty spread and regular parts form a disjoint cover. The induced
coordinate-to-part map is surjective and defines a `RowProfile` whose
heights are the actual numbers of represented values. Internal labels
retain the part kind and order; re-enumeration can be performed separately.
-/

noncomputable section

namespace CircularLaw

theorem levelPart_disjoint_orders {n : ℕ} (y : Fin n → ℂ) (A B : Finset ℂ)
    {j l : ℕ} (hjl : j ≠ l) : Disjoint (levelPart y j A) (levelPart y l B) := by
  apply Finset.disjoint_left.mpr
  intro i hiJ hiL
  obtain ⟨z, _, hiz⟩ := Finset.mem_biUnion.mp hiJ
  obtain ⟨w, _, hiw⟩ := Finset.mem_biUnion.mp hiL
  have hEq : w = z := (selectedLevelAt_value y l w hiw).symm.trans
    (selectedLevelAt_value y j z hiz)
  rw [hEq] at hiw
  rcases lt_or_gt_of_ne hjl with h | h
  · exact Finset.disjoint_left.mp (selectedLevelAt_disjoint_orders y z h) hiz hiw
  · exact Finset.disjoint_left.mp (selectedLevelAt_disjoint_orders y z h) hiw hiz

theorem levelPart_disjoint_values {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (A B : Finset ℂ)
    (hAB : Disjoint A B) : Disjoint (levelPart y j A) (levelPart y j B) := by
  apply Finset.disjoint_left.mpr
  intro i hiA hiB
  exact Finset.disjoint_left.mp hAB (levelPart_value_mem y j A hiA)
    (levelPart_value_mem y j B hiB)

def taggedValues {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (q : Bool × Fin (n + 2)) : Finset ℂ :=
  if q.1 then spreadValueSet y q.2.val δ else regularValueSet y q.2.val δ

def taggedPart {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (q : Bool × Fin (n + 2)) : Finset (Fin n) :=
  levelPart y q.2.val (taggedValues y δ q)

theorem taggedValues_subset {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (q : Bool × Fin (n + 2)) :
    taggedValues y δ q ⊆ representedValues y q.2.val := by
  unfold taggedValues
  split
  · exact spreadValueSet_subset y _ δ
  · exact regularValueSet_subset y _ δ

theorem taggedParts_disjoint {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    {q p : Bool × Fin (n + 2)} (hqp : q ≠ p) : Disjoint (taggedPart y δ q) (taggedPart y δ p) := by
  rcases q with ⟨b, j⟩
  rcases p with ⟨c, l⟩
  by_cases hjl : j = l
  · subst l
    have hbc : b ≠ c := fun h => hqp (Prod.ext h rfl)
    apply levelPart_disjoint_values
    cases b <;> cases c
    · exact (hbc rfl).elim
    · apply Finset.disjoint_left.mpr
      intro z hzR hzS
      exact (Finset.mem_sdiff.mp hzR).2 hzS
    · apply Finset.disjoint_left.mpr
      intro z hzS hzR
      exact (Finset.mem_sdiff.mp hzR).2 hzS
    · exact (hbc rfl).elim
  · exact levelPart_disjoint_orders y _ _ (fun h => hjl (Fin.ext h))

theorem taggedParts_cover {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (i : Fin n) :
    ∃ q : Bool × Fin (n + 2), i ∈ taggedPart y δ q := by
  obtain ⟨j, hj, hi⟩ := selectedLevelAt_coordinate y i
  have hRep : y i ∈ representedValues y j :=
    (selectedLevelAt_nonempty_mem y j (y i)).mp ⟨i, hi⟩
  by_cases hS : y i ∈ spreadValueSet y j δ
  · exact ⟨(true, ⟨j, hj⟩), Finset.mem_biUnion.mpr ⟨y i, hS, hi⟩⟩
  · exact ⟨(false, ⟨j, hj⟩), Finset.mem_biUnion.mpr
      ⟨y i, Finset.mem_sdiff.mpr ⟨hRep, hS⟩, hi⟩⟩

abbrev CanonicalLabel {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :=
  {q : Bool × Fin (n + 2) // (taggedPart y δ q).Nonempty}

theorem canonicalLabel_exists {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (i : Fin n) :
    ∃ q : CanonicalLabel y δ, i ∈ taggedPart y δ q.val := by
  obtain ⟨q, hq⟩ := taggedParts_cover y δ i
  exact ⟨⟨q, ⟨i, hq⟩⟩, hq⟩

def canonicalCoordinateLabel {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (i : Fin n) : CanonicalLabel y δ :=
  Classical.choose (canonicalLabel_exists y δ i)

theorem canonicalCoordinateLabel_mem {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (i : Fin n) :
    i ∈ taggedPart y δ (canonicalCoordinateLabel y δ i).val :=
  Classical.choose_spec (canonicalLabel_exists y δ i)

theorem canonicalCoordinateLabel_eq_iff {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (i : Fin n) (q : CanonicalLabel y δ) :
    canonicalCoordinateLabel y δ i = q ↔ i ∈ taggedPart y δ q.val := by
  constructor
  · intro h
    rw [← h]
    exact canonicalCoordinateLabel_mem y δ i
  · intro hi
    apply Subtype.ext
    by_contra h
    exact Finset.disjoint_left.mp (taggedParts_disjoint y δ h)
      (canonicalCoordinateLabel_mem y δ i) hi

theorem canonicalCoordinateLabel_surjective {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    Function.Surjective (canonicalCoordinateLabel y δ) := by
  intro q
  obtain ⟨i, hi⟩ := q.property
  exact ⟨i, (canonicalCoordinateLabel_eq_iff y δ i q).mpr hi⟩

def canonicalRowProfile {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) : RowProfile (Fin n) (CanonicalLabel y δ) where
  part := canonicalCoordinateLabel y δ
  part_surjective := canonicalCoordinateLabel_surjective y δ
  height q := (taggedValues y δ q.val).card
  height_pos q := Finset.card_pos.mpr
    ((levelPart_nonempty_iff y q.val.2.val _ (taggedValues_subset y δ q.val)).mp q.property)
  spread q := q.val.1

def canonicalPartFiberEquiv {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (q : CanonicalLabel y δ) :
    {i : Fin n // (canonicalRowProfile y δ).part i = q} ≃
      {i : Fin n // i ∈ taggedPart y δ q.val} :=
  Equiv.subtypeEquivRight (fun i => canonicalCoordinateLabel_eq_iff y δ i q)

theorem canonicalPart_card {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (q : CanonicalLabel y δ) :
    Nat.card {i : Fin n // (canonicalRowProfile y δ).part i = q} =
      (taggedPart y δ q.val).card := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_congr (canonicalPartFiberEquiv y δ q)

theorem canonicalPart_size_height {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) (q : CanonicalLabel y δ) :
    2 ^ (q.val.2.val - 1) * (canonicalRowProfile y δ).height q ≤
        Nat.card {i : Fin n // (canonicalRowProfile y δ).part i = q} ∧
    Nat.card {i : Fin n // (canonicalRowProfile y δ).part i = q} ≤
        2 ^ (q.val.2.val + 1) * (canonicalRowProfile y δ).height q := by
  rw [canonicalPart_card]
  exact levelPart_size_height y _ _ (taggedValues_subset y δ q.val)

theorem canonicalPart_size_height_source {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (q : CanonicalLabel y δ) :
    (2 : ℝ) ^ ((q.val.2.val : ℤ) - 1) * ((canonicalRowProfile y δ).height q : ℝ) ≤
        Nat.card {i : Fin n // (canonicalRowProfile y δ).part i = q} ∧
    (Nat.card {i : Fin n // (canonicalRowProfile y δ).part i = q} : ℝ) ≤
        (2 : ℝ) ^ ((q.val.2.val : ℤ) + 1) * ((canonicalRowProfile y δ).height q : ℝ) := by
  rw [canonicalPart_card]
  exact levelPart_size_height_source y _ _ (taggedValues_subset y δ q.val)

end CircularLaw
