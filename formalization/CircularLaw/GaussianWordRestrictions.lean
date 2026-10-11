import CircularLaw.GaussianNoncrossingIntervals

/-!
# Restricting actual Gaussian word matchings to closed position ranges

An injective position map identifies a smaller word with its actual
image. If a matching preserves that image, its restriction is a genuine
bijection between the smaller word's direct and adjoint positions. A
strictly increasing map also preserves the noncrossing condition.
-/

noncomputable section
open Classical

namespace CircularLaw

def predicateRangeRestrictionEquiv {α β : Type*} (p : α → Prop) (f : β → α)
    (hf : Function.Injective f) :
    {x : β // p (f x)} ≃ {y : {y : α // p y} // y.val ∈ Set.range f} where
  toFun x := ⟨⟨f x.val, x.property⟩, x.val, rfl⟩
  invFun y := ⟨Classical.choose y.property, by
    rw [Classical.choose_spec y.property]
    exact y.val.property⟩
  left_inv x := by
    apply Subtype.ext
    exact hf (Classical.choose_spec (show f x.val ∈ Set.range f from ⟨x.val, rfl⟩))
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact Classical.choose_spec y.property

theorem predicate_range_restriction_symm_image {α β : Type*} (p : α → Prop) (f : β → α)
    (hf : Function.Injective f) (y : {y : {y : α // p y} // y.val ∈ Set.range f}) :
    f ((predicateRangeRestrictionEquiv p f hf).symm y).val = y.val.val :=
  Classical.choose_spec y.property

def gaussianWordRestriction {α β : Type*} (b : α → Bool) (e : GaussianWordPairing b)
    (f : β → α) (hf : Function.Injective f)
    (hClosed : ∀ a : GaussianDirectPositions b, a.val ∈ Set.range f ↔ (e a).val ∈ Set.range f) :
    GaussianWordPairing (b ∘ f) :=
  (predicateRangeRestrictionEquiv (fun v => b v = false) f hf).trans
    ((e.subtypeEquiv hClosed).trans
      (predicateRangeRestrictionEquiv (fun v => b v = true) f hf).symm)

theorem gaussian_word_restriction_image {α β : Type*} (b : α → Bool) (e : GaussianWordPairing b)
    (f : β → α) (hf : Function.Injective f)
    (hClosed : ∀ a : GaussianDirectPositions b, a.val ∈ Set.range f ↔ (e a).val ∈ Set.range f)
    (a : GaussianDirectPositions (b ∘ f)) :
    f ((gaussianWordRestriction b e f hf hClosed) a).val = (e ⟨f a.val, a.property⟩).val := by
  simp only [gaussianWordRestriction, Equiv.trans_apply]
  exact predicate_range_restriction_symm_image (fun v => b v = true) f hf
    ((e.subtypeEquiv hClosed)
      ((predicateRangeRestrictionEquiv (fun v => b v = false) f hf) a))

theorem finite_circular_cut_strictMono_image {k l : ℕ}
    (f : Fin l → Fin k) (hf : StrictMono f) (i j v : Fin l) :
    finiteCircularCut (f i) (f j) (f v) ↔ finiteCircularCut i j v := by
  simp only [finiteCircularCut, hf.lt_iff_lt, hf.le_iff_le]

theorem gaussian_word_restriction_eq_of_image {α β : Type*} (b : α → Bool)
    (e : GaussianWordPairing b) (f : β → α) (hf : Function.Injective f)
    (hClosed : ∀ a : GaussianDirectPositions b, a.val ∈ Set.range f ↔ (e a).val ∈ Set.range f)
    (eSmall : GaussianWordPairing (b ∘ f))
    (hImage : ∀ a : GaussianDirectPositions (b ∘ f),
      (e ⟨f a.val, a.property⟩).val = f (eSmall a).val) :
    gaussianWordRestriction b e f hf hClosed = eSmall := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  apply hf
  exact (gaussian_word_restriction_image b e f hf hClosed a).trans (hImage a)

theorem gaussian_word_restriction_noncrossing {k l : ℕ} (b : Fin k → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e)
    (f : Fin l → Fin k) (hf : StrictMono f)
    (hClosed : ∀ a : GaussianDirectPositions b, a.val ∈ Set.range f ↔ (e a).val ∈ Set.range f) :
    GaussianWordNoncrossing (b ∘ f) (gaussianWordRestriction b e f hf.injective hClosed) := by
  intro a c hca
  have hMainNe : (⟨f c.val, c.property⟩ : GaussianDirectPositions b) ≠ ⟨f a.val, a.property⟩ := by
    intro h
    exact hca (Subtype.ext (hf.injective (congrArg Subtype.val h)))
  have h := hNC ⟨f a.val, a.property⟩ ⟨f c.val, c.property⟩ hMainNe
  change (finiteCircularCut (f a.val) (e ⟨f a.val, a.property⟩).val (f c.val) ↔
    finiteCircularCut (f a.val) (e ⟨f a.val, a.property⟩).val (e ⟨f c.val, c.property⟩).val) at h
  rw [← gaussian_word_restriction_image b e f hf.injective hClosed a,
    ← gaussian_word_restriction_image b e f hf.injective hClosed c] at h
  simpa only [finite_circular_cut_strictMono_image f hf] using h

end CircularLaw
