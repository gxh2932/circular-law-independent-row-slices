import CircularLaw.GaussianFirstPairNoncrossing

/-!
# Exact first-pair decomposition of compatible noncrossing matchings

For each fixed first adjoint partner, restriction and assembly are inverse.
Partitioning by that partner gives a sigma equivalence and an exact sum of
products for the count of noncrossing compatible matchings.
-/

noncomputable section
open Classical

namespace CircularLaw

abbrev GaussianNoncrossingPairings {n : ℕ} (b : Fin n → Bool) :=
  {e : GaussianWordPairing b // GaussianWordNoncrossing b e}

abbrev GaussianNoncrossingFirstFiber {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) (q : GaussianAdjointPositions b) :=
  {e : GaussianNoncrossingPairings b // e.val ⟨0, hZero⟩ = q}

theorem gaussian_first_interior_closed_at {k : ℕ} (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false)
    (q : GaussianAdjointPositions b) (hPartner : e ⟨0, hZero⟩ = q)
    (a : GaussianDirectPositions b) :
    a.val ∈ Set.range (gaussianFirstInteriorMap q.val) ↔
      (e a).val ∈ Set.range (gaussianFirstInteriorMap q.val) := by
  rw [← congrArg Subtype.val hPartner]
  exact gaussian_first_interior_closed k b e hNC hZero a

theorem gaussian_first_outer_closed_at {k : ℕ} (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false)
    (q : GaussianAdjointPositions b) (hPartner : e ⟨0, hZero⟩ = q)
    (a : GaussianDirectPositions b) :
    a.val ∈ Set.range (gaussianFirstOuterMap q.val) ↔
      (e a).val ∈ Set.range (gaussianFirstOuterMap q.val) := by
  rw [← congrArg Subtype.val hPartner]
  exact gaussian_first_outer_closed k b e hNC hZero a

def gaussianFirstFiberInteriorRestriction {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) (q : GaussianAdjointPositions b)
    (e : GaussianNoncrossingFirstFiber b hZero q) :
    GaussianWordPairing (b ∘ gaussianFirstInteriorMap q.val) :=
  gaussianWordRestriction b e.val.val _ (gaussian_first_interior_map_strictMono _).injective
    (gaussian_first_interior_closed_at b e.val.val e.val.property hZero q e.property)

def gaussianFirstFiberOuterRestriction {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) (q : GaussianAdjointPositions b)
    (e : GaussianNoncrossingFirstFiber b hZero q) :
    GaussianWordPairing (b ∘ gaussianFirstOuterMap q.val) :=
  gaussianWordRestriction b e.val.val _ (gaussian_first_outer_map_strictMono _).injective
    (gaussian_first_outer_closed_at b e.val.val e.val.property hZero q e.property)

theorem gaussian_first_fiber_interior_noncrossing {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) (q : GaussianAdjointPositions b)
    (e : GaussianNoncrossingFirstFiber b hZero q) :
    GaussianWordNoncrossing (b ∘ gaussianFirstInteriorMap q.val)
      (gaussianFirstFiberInteriorRestriction b hZero q e) :=
  gaussian_word_restriction_noncrossing b e.val.val e.val.property _
    (gaussian_first_interior_map_strictMono _)
    (gaussian_first_interior_closed_at b e.val.val e.val.property hZero q e.property)

theorem gaussian_first_fiber_outer_noncrossing {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) (q : GaussianAdjointPositions b)
    (e : GaussianNoncrossingFirstFiber b hZero q) :
    GaussianWordNoncrossing (b ∘ gaussianFirstOuterMap q.val)
      (gaussianFirstFiberOuterRestriction b hZero q e) :=
  gaussian_word_restriction_noncrossing b e.val.val e.val.property _
    (gaussian_first_outer_map_strictMono _)
    (gaussian_first_outer_closed_at b e.val.val e.val.property hZero q e.property)

abbrev GaussianFirstPairData {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : GaussianAdjointPositions b) :=
  GaussianNoncrossingPairings (b ∘ gaussianFirstInteriorMap q.val) ×
    GaussianNoncrossingPairings (b ∘ gaussianFirstOuterMap q.val)

def gaussianFirstFiberSplit {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) (q : GaussianAdjointPositions b)
    (e : GaussianNoncrossingFirstFiber b hZero q) : GaussianFirstPairData b q :=
  (⟨gaussianFirstFiberInteriorRestriction b hZero q e,
    gaussian_first_fiber_interior_noncrossing b hZero q e⟩,
   ⟨gaussianFirstFiberOuterRestriction b hZero q e,
    gaussian_first_fiber_outer_noncrossing b hZero q e⟩)

def gaussianFirstFiberAssemble {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) (q : GaussianAdjointPositions b)
    (p : GaussianFirstPairData b q) : GaussianNoncrossingFirstFiber b hZero q :=
  ⟨⟨gaussianFirstPairAssembly b q.val hZero q.property p.1.val p.2.val,
    gaussian_first_pair_assembly_noncrossing b q.val hZero q.property p.1.val p.2.val
      p.1.property p.2.property⟩,
   gaussian_first_pair_assembly_first b q.val hZero q.property p.1.val p.2.val⟩

theorem gaussian_first_fiber_assemble_split {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) (q : GaussianAdjointPositions b)
    (e : GaussianNoncrossingFirstFiber b hZero q) :
    gaussianFirstFiberAssemble b hZero q (gaussianFirstFiberSplit b hZero q e) = e := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro a
  obtain ⟨a, rfl⟩ := (gaussianFirstFiberEquiv b q.val hZero q.property false).surjective a
  change gaussianFirstPairAssembly b q.val hZero q.property
    (gaussianFirstFiberInteriorRestriction b hZero q e)
    (gaussianFirstFiberOuterRestriction b hZero q e)
    (gaussianFirstFiberEquiv b q.val hZero q.property false a) =
    e.val.val (gaussianFirstFiberEquiv b q.val hZero q.property false a)
  rw [gaussian_first_pair_assembly_on_piece]
  rcases a with u | (i | o)
  · exact e.property.symm
  · apply Subtype.ext
    exact gaussian_word_restriction_image b e.val.val _ _ _ i
  · apply Subtype.ext
    exact gaussian_word_restriction_image b e.val.val _ _ _ o

theorem gaussian_first_fiber_split_assemble {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) (q : GaussianAdjointPositions b)
    (p : GaussianFirstPairData b q) :
    gaussianFirstFiberSplit b hZero q (gaussianFirstFiberAssemble b hZero q p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    apply gaussian_word_restriction_eq_of_image b _ _ _ _ p.1.val
    intro a
    exact congrArg Subtype.val
      (gaussian_first_pair_assembly_interior b q.val hZero q.property p.1.val p.2.val a)
  · apply Subtype.ext
    apply gaussian_word_restriction_eq_of_image b _ _ _ _ p.2.val
    intro a
    exact congrArg Subtype.val
      (gaussian_first_pair_assembly_outer b q.val hZero q.property p.1.val p.2.val a)

def gaussianFirstPairFiberEquiv {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) (q : GaussianAdjointPositions b) :
    GaussianNoncrossingFirstFiber b hZero q ≃ GaussianFirstPairData b q where
  toFun := gaussianFirstFiberSplit b hZero q
  invFun := gaussianFirstFiberAssemble b hZero q
  left_inv := gaussian_first_fiber_assemble_split b hZero q
  right_inv := gaussian_first_fiber_split_assemble b hZero q

def gaussianFirstPairDecomposition {k : ℕ} (b : Fin (k + 1) → Bool) (hZero : b 0 = false) :
    GaussianNoncrossingPairings b ≃ Σ q : GaussianAdjointPositions b, GaussianFirstPairData b q :=
  (Equiv.sigmaFiberEquiv (fun e : GaussianNoncrossingPairings b => e.val ⟨0, hZero⟩)).symm.trans
    (Equiv.sigmaCongrRight (gaussianFirstPairFiberEquiv b hZero))

theorem gaussian_noncrossing_first_pair_card {k : ℕ} (b : Fin (k + 1) → Bool)
    (hZero : b 0 = false) :
    Fintype.card (GaussianNoncrossingPairings b) =
      ∑ q : GaussianAdjointPositions b,
        Fintype.card (GaussianNoncrossingPairings (b ∘ gaussianFirstInteriorMap q.val)) *
          Fintype.card (GaussianNoncrossingPairings (b ∘ gaussianFirstOuterMap q.val)) := by
  rw [Fintype.card_congr (gaussianFirstPairDecomposition b hZero), Fintype.card_sigma]
  simp only [GaussianFirstPairData, Fintype.card_prod]

theorem gaussian_noncrossing_empty_card (b : Fin 0 → Bool) :
    Fintype.card (GaussianNoncrossingPairings b) = 1 := by
  let e : GaussianWordPairing b := Equiv.equivOfIsEmpty _ _
  have hNC : GaussianWordNoncrossing b e := by
    intro a
    exact Fin.elim0 a.val
  letI : Unique (GaussianNoncrossingPairings b) := uniqueOfSubsingleton ⟨e, hNC⟩
  exact Fintype.card_unique

end CircularLaw
