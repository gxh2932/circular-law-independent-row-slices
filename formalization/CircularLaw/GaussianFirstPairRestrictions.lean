import CircularLaw.GaussianWordRestrictions

/-!
# The two smaller words cut off by the first Gaussian pair

The first partner divides positions into the initial endpoint pair, the
strict interior and the remaining final interval. The latter two pieces
are reindexed by increasing maps. Their actual restricted matchings are
noncrossing, including when a smaller word has length zero.
-/

noncomputable section
open Classical

namespace CircularLaw

def gaussianFirstInteriorMap {k : ℕ} (q : Fin (k + 1)) :
    Fin (q.val - 1) → Fin (k + 1) := fun v =>
  ⟨v.val + 1, by have := v.isLt; have := q.isLt; omega⟩

def gaussianFirstOuterMap {k : ℕ} (q : Fin (k + 1)) :
    Fin (k - q.val) → Fin (k + 1) := fun v =>
  ⟨q.val + 1 + v.val, by have := v.isLt; have := q.isLt; omega⟩

theorem gaussian_first_interior_map_strictMono {k : ℕ} (q : Fin (k + 1)) :
    StrictMono (gaussianFirstInteriorMap q) := by
  intro i j hij
  simp only [gaussianFirstInteriorMap, Fin.lt_def] at hij ⊢
  omega

theorem gaussian_first_outer_map_strictMono {k : ℕ} (q : Fin (k + 1)) :
    StrictMono (gaussianFirstOuterMap q) := by
  intro i j hij
  simp only [gaussianFirstOuterMap, Fin.lt_def] at hij ⊢
  omega

theorem gaussian_first_interior_map_range {k : ℕ} (q v : Fin (k + 1)) :
    v ∈ Set.range (gaussianFirstInteriorMap q) ↔ 0 < v ∧ v < q := by
  constructor
  · rintro ⟨u, rfl⟩
    simp only [gaussianFirstInteriorMap, Fin.lt_def, Fin.val_zero]
    have := u.isLt
    omega
  · intro h
    simp only [Fin.lt_def, Fin.val_zero] at h
    refine ⟨⟨v.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [gaussianFirstInteriorMap]
    omega

theorem gaussian_first_outer_map_range {k : ℕ} (q v : Fin (k + 1)) :
    v ∈ Set.range (gaussianFirstOuterMap q) ↔ q < v := by
  constructor
  · rintro ⟨u, rfl⟩
    simp only [gaussianFirstOuterMap, Fin.lt_def]
    omega
  · intro h
    simp only [Fin.lt_def] at h
    refine ⟨⟨v.val - q.val - 1, by have := v.isLt; omega⟩, ?_⟩
    apply Fin.ext
    simp only [gaussianFirstOuterMap]
    omega

theorem gaussian_first_interior_closed (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false)
    (a : GaussianDirectPositions b) :
    a.val ∈ Set.range (gaussianFirstInteriorMap (e ⟨0, hZero⟩).val) ↔
      (e a).val ∈ Set.range (gaussianFirstInteriorMap (e ⟨0, hZero⟩).val) := by
  rw [gaussian_first_interior_map_range, gaussian_first_interior_map_range]
  have h := gaussian_noncrossing_pair_interior_iff k b e hNC ⟨0, hZero⟩ a
  simpa only [Subtype.coe_mk, min_eq_left (Fin.zero_le _), max_eq_right (Fin.zero_le _)] using h

theorem gaussian_first_outer_closed (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false)
    (a : GaussianDirectPositions b) :
    a.val ∈ Set.range (gaussianFirstOuterMap (e ⟨0, hZero⟩).val) ↔
      (e a).val ∈ Set.range (gaussianFirstOuterMap (e ⟨0, hZero⟩).val) := by
  rw [gaussian_first_outer_map_range, gaussian_first_outer_map_range]
  exact gaussian_noncrossing_first_outer_iff k b e hNC hZero a

def gaussianFirstInteriorRestriction (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false) :
    GaussianWordPairing (b ∘ gaussianFirstInteriorMap (e ⟨0, hZero⟩).val) :=
  gaussianWordRestriction b e _
    (gaussian_first_interior_map_strictMono _).injective
    (gaussian_first_interior_closed k b e hNC hZero)

def gaussianFirstOuterRestriction (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false) :
    GaussianWordPairing (b ∘ gaussianFirstOuterMap (e ⟨0, hZero⟩).val) :=
  gaussianWordRestriction b e _
    (gaussian_first_outer_map_strictMono _).injective
    (gaussian_first_outer_closed k b e hNC hZero)

theorem gaussian_first_interior_restriction_noncrossing (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false) :
    GaussianWordNoncrossing (b ∘ gaussianFirstInteriorMap (e ⟨0, hZero⟩).val)
      (gaussianFirstInteriorRestriction k b e hNC hZero) :=
  gaussian_word_restriction_noncrossing b e hNC _
    (gaussian_first_interior_map_strictMono _) (gaussian_first_interior_closed k b e hNC hZero)

theorem gaussian_first_outer_restriction_noncrossing (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false) :
    GaussianWordNoncrossing (b ∘ gaussianFirstOuterMap (e ⟨0, hZero⟩).val)
      (gaussianFirstOuterRestriction k b e hNC hZero) :=
  gaussian_word_restriction_noncrossing b e hNC _
    (gaussian_first_outer_map_strictMono _) (gaussian_first_outer_closed k b e hNC hZero)

theorem gaussian_first_interior_restriction_image (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false)
    (a : GaussianDirectPositions (b ∘ gaussianFirstInteriorMap (e ⟨0, hZero⟩).val)) :
    gaussianFirstInteriorMap (e ⟨0, hZero⟩).val
      ((gaussianFirstInteriorRestriction k b e hNC hZero) a).val =
      (e ⟨gaussianFirstInteriorMap (e ⟨0, hZero⟩).val a.val, a.property⟩).val :=
  gaussian_word_restriction_image b e _ _ _ a

theorem gaussian_first_outer_restriction_image (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false)
    (a : GaussianDirectPositions (b ∘ gaussianFirstOuterMap (e ⟨0, hZero⟩).val)) :
    gaussianFirstOuterMap (e ⟨0, hZero⟩).val
      ((gaussianFirstOuterRestriction k b e hNC hZero) a).val =
      (e ⟨gaussianFirstOuterMap (e ⟨0, hZero⟩).val a.val, a.property⟩).val :=
  gaussian_word_restriction_image b e _ _ _ a

theorem gaussian_first_interior_counts_equal (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false) :
    Fintype.card (GaussianDirectPositions (b ∘ gaussianFirstInteriorMap (e ⟨0, hZero⟩).val)) =
      Fintype.card (GaussianAdjointPositions (b ∘ gaussianFirstInteriorMap (e ⟨0, hZero⟩).val)) :=
  Fintype.card_congr (gaussianFirstInteriorRestriction k b e hNC hZero)

theorem gaussian_first_outer_counts_equal (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false) :
    Fintype.card (GaussianDirectPositions (b ∘ gaussianFirstOuterMap (e ⟨0, hZero⟩).val)) =
      Fintype.card (GaussianAdjointPositions (b ∘ gaussianFirstOuterMap (e ⟨0, hZero⟩).val)) :=
  Fintype.card_congr (gaussianFirstOuterRestriction k b e hNC hZero)

theorem gaussian_first_interior_length_lt {k : ℕ} (q : Fin (k + 1)) :
    q.val - 1 < k + 1 := by
  have := q.isLt
  omega

theorem gaussian_first_outer_length_lt {k : ℕ} (q : Fin (k + 1)) :
    k - q.val < k + 1 := by omega

end CircularLaw
