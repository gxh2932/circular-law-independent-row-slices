import CircularLaw.CanonicalPartition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Ordered profiles and the logarithmic part count

The enumeration places every spread part first, in increasing level
order, then every regular part in increasing order. Its actual height
bound and eventual `3 log n` part-count bound discharge the deterministic
profile hypotheses used by the row estimator.
-/

noncomputable section

namespace CircularLaw

theorem canonicalOrder_lt_log_bound {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (q : CanonicalLabel y δ) : q.val.2.val < Nat.log 2 n + 2 := by
  have hValues := (levelPart_nonempty_iff y q.val.2.val _
    (taggedValues_subset y δ q.val)).mp q.property
  obtain ⟨z, hz⟩ := hValues
  have hRep := taggedValues_subset y δ q.val hz
  by_contra h
  rw [representedValues_empty_of_log_bound y (by omega)] at hRep
  simp only [Finset.notMem_empty] at hRep

theorem canonicalLabel_card_le {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    Fintype.card (CanonicalLabel y δ) ≤ 2 * (Nat.log 2 n + 2) := by
  let f : CanonicalLabel y δ → Bool × Fin (Nat.log 2 n + 2) :=
    fun q => (q.val.1, ⟨q.val.2.val, canonicalOrder_lt_log_bound y δ q⟩)
  have hf : Function.Injective f := by
    intro q p h
    apply Subtype.ext
    apply Prod.ext
    · simpa only [f] using congrArg Prod.fst h
    · apply Fin.ext
      exact congrArg (fun a => a.2.val) h
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

theorem canonicalLabel_card_eventually :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ y : Fin n → ℂ, ∀ δ : ℝ,
      (Fintype.card (CanonicalLabel y δ) : ℝ) ≤ 3 * Real.log (n : ℝ) := by
  have hTwo : (2 / 3 : ℝ) < Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
    norm_num at h
    exact h
  have hLogPos : 0 < Real.log 2 := lt_trans (by norm_num) hTwo
  have hGap : 0 < 3 - 2 / Real.log 2 := by
    have hRatio : 2 / Real.log 2 < 3 := (div_lt_iff₀ hLogPos).mpr (by linarith)
    linarith
  have hlim := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)
  filter_upwards [hlim.eventually_ge_atTop (4 / (3 - 2 / Real.log 2))] with n hn
  intro y δ
  have hCount : (Fintype.card (CanonicalLabel y δ) : ℝ) ≤
      2 * ((Nat.log 2 n : ℝ) + 2) := by exact_mod_cast canonicalLabel_card_le y δ
  have hLog : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb n 2
  have hLarge : 4 ≤ (3 - 2 / Real.log 2) * Real.log (n : ℝ) := by
    simpa only [Function.comp_apply, mul_comm] using (div_le_iff₀ hGap).mp hn
  calc
    _ ≤ 2 * (Real.log (n : ℝ) / Real.log 2 + 2) := hCount.trans (by linarith)
    _ ≤ _ := by rw [div_eq_mul_inv] at hLarge ⊢; nlinarith only [hLarge]

def taggedOrderKey {n : ℕ} (q : Bool × Fin (n + 2)) : ℕ :=
  if q.1 then q.2.val else n + 2 + q.2.val

theorem taggedOrderKey_injective {n : ℕ} :
    Function.Injective (taggedOrderKey (n := n)) := by
  rintro ⟨b, j⟩ ⟨c, l⟩ h
  cases b <;> cases c
  · have hJL : j = l := by
      apply Fin.ext
      simp only [taggedOrderKey, Bool.false_eq_true, ↓reduceIte] at h
      omega
    exact congrArg (fun a => (false, a)) hJL
  · simp only [taggedOrderKey, Bool.false_eq_true, ↓reduceIte] at h
    have := l.isLt
    omega
  · simp only [taggedOrderKey, Bool.false_eq_true, ↓reduceIte] at h
    have := j.isLt
    omega
  · have hJL : j = l := by
      apply Fin.ext
      simpa only [taggedOrderKey, ↓reduceIte] using h
    exact congrArg (fun a => (true, a)) hJL

def canonicalLabelOrder {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) : LinearOrder (CanonicalLabel y δ) :=
  LinearOrder.lift' (fun q => taggedOrderKey q.val)
    (fun _ _ h => Subtype.ext (taggedOrderKey_injective h))

def canonicalEnumeration {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    Fin (Fintype.card (CanonicalLabel y δ)) ≃ CanonicalLabel y δ := by
  letI := canonicalLabelOrder y δ
  exact (Fintype.orderIsoFinOfCardEq (CanonicalLabel y δ) rfl).toEquiv

theorem canonicalEnumeration_key_strictMono {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    StrictMono (fun q => taggedOrderKey (canonicalEnumeration y δ q).val) := by
  letI := canonicalLabelOrder y δ
  intro a b hab
  exact (@OrderIso.lt_iff_lt (Fin (Fintype.card (CanonicalLabel y δ)))
    (CanonicalLabel y δ) Fin.instPartialOrder.toPreorder
    (canonicalLabelOrder y δ).toPartialOrder.toPreorder
    (Fintype.orderIsoFinOfCardEq (CanonicalLabel y δ) rfl) a b).mpr hab

def orderedCanonicalRowProfile {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    RowProfile (Fin n) (Fin (Fintype.card (CanonicalLabel y δ))) where
  part i := (canonicalEnumeration y δ).symm (canonicalCoordinateLabel y δ i)
  part_surjective := (canonicalEnumeration y δ).symm.surjective.comp
    (canonicalCoordinateLabel_surjective y δ)
  height q := (canonicalRowProfile y δ).height (canonicalEnumeration y δ q)
  height_pos q := (canonicalRowProfile y δ).height_pos (canonicalEnumeration y δ q)
  spread q := (canonicalEnumeration y δ q).val.1

theorem canonicalRowProfile_height_le {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (q : CanonicalLabel y δ) : (canonicalRowProfile y δ).height q ≤ n := by
  have hLow := (canonicalPart_size_height y δ q).1
  rw [canonicalPart_card] at hLow
  have hPow : 1 ≤ (2 : ℕ) ^ (q.val.2.val - 1) :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hHeight : (canonicalRowProfile y δ).height q ≤ (taggedPart y δ q.val).card := by
    have hMul := Nat.mul_le_mul_right ((canonicalRowProfile y δ).height q) hPow
    simp only [one_mul] at hMul
    exact hMul.trans hLow
  exact hHeight.trans ((Finset.card_le_card (Finset.subset_univ _)).trans_eq
    (by simp only [Finset.card_univ, Fintype.card_fin]))

theorem orderedCanonicalRowProfile_height_le {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (q : Fin (Fintype.card (CanonicalLabel y δ))) :
    (orderedCanonicalRowProfile y δ).height q ≤ n :=
  canonicalRowProfile_height_le y δ (canonicalEnumeration y δ q)

end CircularLaw
