import CircularLaw.GaussianFirstPairRestrictions

/-!
# Reassembling the first pair and its two smaller matchings

The direct positions partition into the initial endpoint, the interior
word and the final word. The adjoint positions have the same partition,
with the first partner as endpoint. Their explicit equivalences assemble
any two compatible smaller matchings into a matching of the full word.
-/

noncomputable section
open Classical

namespace CircularLaw

def gaussianFirstPiecePosition {k : ℕ} (q : Fin (k + 1)) (s : Bool) :
    Unit ⊕ (Fin (q.val - 1) ⊕ Fin (k - q.val)) → Fin (k + 1)
  | .inl _ => bif s then q else 0
  | .inr (.inl a) => gaussianFirstInteriorMap q a
  | .inr (.inr a) => gaussianFirstOuterMap q a

theorem gaussian_first_piece_position_injective {k : ℕ} (q : Fin (k + 1)) (s : Bool) :
    Function.Injective (gaussianFirstPiecePosition q s) := by
  rintro (u | (i | o)) (v | (j | p)) h
  all_goals cases s
  all_goals simp only [gaussianFirstPiecePosition, Bool.cond_false, Bool.cond_true,
    gaussianFirstInteriorMap, gaussianFirstOuterMap, Fin.ext_iff, Fin.val_zero,
    Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at h ⊢
  all_goals first | exact Subsingleton.elim _ _ | omega

abbrev GaussianFirstFiberPieces {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (s : Bool) :=
  Unit ⊕ ({a : Fin (q.val - 1) // b (gaussianFirstInteriorMap q a) = s} ⊕
    {a : Fin (k - q.val) // b (gaussianFirstOuterMap q a) = s})

def gaussianFirstFiberInclusion {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (hZero : b 0 = false) (hQ : b q = true) (s : Bool) :
    GaussianFirstFiberPieces b q s → {a : Fin (k + 1) // b a = s}
  | .inl _ => ⟨bif s then q else 0, by cases s <;> assumption⟩
  | .inr (.inl a) => ⟨gaussianFirstInteriorMap q a.val, a.property⟩
  | .inr (.inr a) => ⟨gaussianFirstOuterMap q a.val, a.property⟩

theorem gaussian_first_fiber_inclusion_injective {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (hZero : b 0 = false) (hQ : b q = true) (s : Bool) :
    Function.Injective (gaussianFirstFiberInclusion b q hZero hQ s) := by
  intro x y h
  have hPos : gaussianFirstPiecePosition q s (Sum.map id (Sum.map Subtype.val Subtype.val) x) =
      gaussianFirstPiecePosition q s (Sum.map id (Sum.map Subtype.val Subtype.val) y) := by
    rcases x with u | (i | o) <;> rcases y with v | (j | p)
    all_goals exact congrArg Subtype.val h
  have hPieces := gaussian_first_piece_position_injective q s hPos
  rcases x with u | (i | o) <;> rcases y with v | (j | p)
  all_goals simp only [Sum.map_inl, Sum.map_inr, id_eq, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl] at hPieces ⊢
  all_goals first | exact hPieces | exact Subtype.ext hPieces

theorem gaussian_first_fiber_inclusion_surjective {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (hZero : b 0 = false) (hQ : b q = true) (s : Bool) :
    Function.Surjective (gaussianFirstFiberInclusion b q hZero hQ s) := by
  intro a
  by_cases h0 : a.val = 0
  · have hs : s = false := by simpa only [h0, hZero] using a.property.symm
    subst s
    exact ⟨.inl (), Subtype.ext h0.symm⟩
  by_cases hq : a.val = q
  · have hs : s = true := by simpa only [hq, hQ] using a.property.symm
    subst s
    exact ⟨.inl (), Subtype.ext hq.symm⟩
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · have hPos : (0 : Fin (k + 1)) < a.val := by
      simp only [Fin.ext_iff, Fin.val_zero] at h0
      simp only [Fin.lt_def, Fin.val_zero]
      omega
    obtain ⟨i, hi⟩ := (gaussian_first_interior_map_range q a.val).mpr ⟨hPos, hlt⟩
    exact ⟨.inr (.inl ⟨i, hi ▸ a.property⟩), Subtype.ext hi⟩
  · obtain ⟨o, ho⟩ := (gaussian_first_outer_map_range q a.val).mpr hgt
    exact ⟨.inr (.inr ⟨o, ho ▸ a.property⟩), Subtype.ext ho⟩

def gaussianFirstFiberEquiv {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (hZero : b 0 = false) (hQ : b q = true) (s : Bool) :
    GaussianFirstFiberPieces b q s ≃ {a : Fin (k + 1) // b a = s} :=
  Equiv.ofBijective (gaussianFirstFiberInclusion b q hZero hQ s)
    ⟨gaussian_first_fiber_inclusion_injective b q hZero hQ s,
      gaussian_first_fiber_inclusion_surjective b q hZero hQ s⟩

def gaussianFirstPairAssembly {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (hZero : b 0 = false) (hQ : b q = true)
    (eI : GaussianWordPairing (b ∘ gaussianFirstInteriorMap q))
    (eO : GaussianWordPairing (b ∘ gaussianFirstOuterMap q)) : GaussianWordPairing b :=
  (gaussianFirstFiberEquiv b q hZero hQ false).symm.trans
    ((Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr eI eO)).trans
      (gaussianFirstFiberEquiv b q hZero hQ true))

theorem gaussian_first_pair_assembly_on_piece {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (hZero : b 0 = false) (hQ : b q = true)
    (eI : GaussianWordPairing (b ∘ gaussianFirstInteriorMap q))
    (eO : GaussianWordPairing (b ∘ gaussianFirstOuterMap q))
    (x : GaussianFirstFiberPieces b q false) :
    gaussianFirstPairAssembly b q hZero hQ eI eO (gaussianFirstFiberEquiv b q hZero hQ false x) =
      gaussianFirstFiberEquiv b q hZero hQ true (Sum.map id (Sum.map eI eO) x) := by
  simp only [gaussianFirstPairAssembly, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem gaussian_first_pair_assembly_first {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (hZero : b 0 = false) (hQ : b q = true)
    (eI : GaussianWordPairing (b ∘ gaussianFirstInteriorMap q))
    (eO : GaussianWordPairing (b ∘ gaussianFirstOuterMap q)) :
    gaussianFirstPairAssembly b q hZero hQ eI eO ⟨0, hZero⟩ = ⟨q, hQ⟩ :=
  gaussian_first_pair_assembly_on_piece b q hZero hQ eI eO (.inl ())

theorem gaussian_first_pair_assembly_interior {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (hZero : b 0 = false) (hQ : b q = true)
    (eI : GaussianWordPairing (b ∘ gaussianFirstInteriorMap q))
    (eO : GaussianWordPairing (b ∘ gaussianFirstOuterMap q))
    (a : GaussianDirectPositions (b ∘ gaussianFirstInteriorMap q)) :
    gaussianFirstPairAssembly b q hZero hQ eI eO ⟨gaussianFirstInteriorMap q a.val, a.property⟩ =
      ⟨gaussianFirstInteriorMap q (eI a).val, (eI a).property⟩ :=
  gaussian_first_pair_assembly_on_piece b q hZero hQ eI eO (.inr (.inl a))

theorem gaussian_first_pair_assembly_outer {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (hZero : b 0 = false) (hQ : b q = true)
    (eI : GaussianWordPairing (b ∘ gaussianFirstInteriorMap q))
    (eO : GaussianWordPairing (b ∘ gaussianFirstOuterMap q))
    (a : GaussianDirectPositions (b ∘ gaussianFirstOuterMap q)) :
    gaussianFirstPairAssembly b q hZero hQ eI eO ⟨gaussianFirstOuterMap q a.val, a.property⟩ =
      ⟨gaussianFirstOuterMap q (eO a).val, (eO a).property⟩ :=
  gaussian_first_pair_assembly_on_piece b q hZero hQ eI eO (.inr (.inr a))

end CircularLaw
