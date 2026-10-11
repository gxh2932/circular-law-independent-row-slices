import CircularLaw.ProfileEstimator
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Planar packing and balanced-level atoms

The conditional row argument first bounds a single level atom by
`4/(h+3)`, then counts separated level values inside a disk. Both steps
are proved here from finite counting and the area of complex disks.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem balanced_level_atom_bound {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (level : α → β)
    (hbalance : ∀ a b, Nat.card {x // level x = a} ≤ 4 * Nat.card {x // level x = b})
    (a : β) :
    uniformProbability (fun x => level x = a) ≤ 4 / ((Fintype.card β : ℝ) + 3) := by
  classical
  let p := fun b => uniformProbability (fun x => level x = b)
  have hsum : (∑ b, p b) = 1 := by
    have h := finiteMean_part_function level (fun _ : β => (1 : ℝ))
    simpa only [finiteMean_const, mul_one, partMass, p] using h.symm
  have hp (b : β) : p a ≤ 4 * p b := by
    have h : (Nat.card {x // level x = a} : ℝ) ≤ 4 * Nat.card {x // level x = b} :=
      by exact_mod_cast hbalance a b
    have hdiv := div_le_div_of_nonneg_right h (Nat.cast_nonneg (Nat.card α))
    simpa only [p, uniformProbability, mul_div_assoc] using hdiv
  have hpoint (b : β) : p a + (if a = b then 3 * p a else 0) ≤ 4 * p b := by
    by_cases h : a = b
    · subst b
      simp
      linarith
    · simp only [if_neg h, add_zero]
      exact hp b
  have h := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum, hsum, mul_one] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (Fintype.card β : ℝ) + 3)).mpr
  dsimp only [p] at h
  nlinarith

theorem complex_ball_area {z : ℂ} {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.ball z r) = r ^ 2 * Real.pi := by
  rw [measureReal_def, Complex.volume_ball]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.coe_toReal, NNReal.coe_real_pi]

theorem balanced_complex_atom_bound {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (level : α → β) (value : β → ℂ) (hinj : Function.Injective value)
    (hbalance : ∀ a b, Nat.card {x // level x = a} ≤ 4 * Nat.card {x // level x = b})
    (z : ℂ) :
    uniformProbability (fun a => value (level a) = z) ≤ 4 / ((Fintype.card β : ℝ) + 3) := by
  classical
  by_cases h : z ∈ Set.range value
  · rcases h with ⟨b, rfl⟩
    simpa only [hinj.eq_iff] using balanced_level_atom_bound level hbalance b
  · haveI : IsEmpty {a : α // value (level a) = z} := ⟨fun a =>
      h ⟨level a.val, a.property⟩⟩
    simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_eq_zero,
      Nat.cast_zero, zero_div]
    positivity

/-- Disjoint disks of radius `delta/2` fit inside the containing disk
enlarged by `delta/2`. -/
theorem separated_complex_card_sharp {T : Finset ℂ} {z : ℂ} {r δ : ℝ}
    (hr : 0 ≤ r) (hδ : 0 < δ)
    (hsep : (T : Set ℂ).Pairwise (fun a b => δ ≤ dist a b))
    (hcenter : ∀ a ∈ T, dist a z ≤ r) :
    (T.card : ℝ) ≤ (1 + 2 * r / δ) ^ 2 := by
  classical
  have hdisj : (T : Set ℂ).PairwiseDisjoint (fun a => Metric.ball a (δ / 2)) := by
    intro a ha b hb hab
    apply Metric.ball_disjoint_ball
    have h := hsep ha hb hab
    linarith
  have hsubset : (⋃ a ∈ T, Metric.ball a (δ / 2)) ⊆ Metric.ball z (r + δ / 2) := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨a, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨ha, hx⟩
    exact Metric.ball_subset_ball' (by linarith [hcenter a ha]) hx
  have hmono := measureReal_mono (μ := volume) hsubset (by
    rw [Complex.volume_ball]
    finiteness)
  rw [measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_ball)
    (fun a _ => by rw [Complex.volume_ball]; finiteness)] at hmono
  simp only [complex_ball_area (by positivity : 0 ≤ δ / 2), Finset.sum_const,
    nsmul_eq_mul, complex_ball_area (by positivity : 0 ≤ r + δ / 2)] at hmono
  have harea : (T.card : ℝ) * (δ / 2) ^ 2 ≤ (r + δ / 2) ^ 2 := by
    nlinarith [Real.pi_pos]
  calc
    _ ≤ 4 * (r + δ / 2) ^ 2 / δ ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
      nlinarith
    _ = _ := by field_simp; ring

theorem planar_packing_relaxation {r δ : ℝ} :
    (1 + 2 * r / δ) ^ 2 ≤ 2 + 8 * r ^ 2 / δ ^ 2 := by
  calc
    _ ≤ 2 + 2 * (2 * r / δ) ^ 2 := by nlinarith [sq_nonneg (1 - 2 * r / δ)]
    _ = _ := by rw [div_pow, mul_pow]; ring

theorem separated_complex_card_le {T : Finset ℂ} {z : ℂ} {r δ : ℝ}
    (hr : 0 ≤ r) (hδ : 0 < δ)
    (hsep : (T : Set ℂ).Pairwise (fun a b => δ ≤ dist a b))
    (hcenter : ∀ a ∈ T, dist a z ≤ r) :
    (T.card : ℝ) ≤ 2 + 8 * r ^ 2 / δ ^ 2 :=
  (separated_complex_card_sharp hr hδ hsep hcenter).trans planar_packing_relaxation

/-- A finite law with maximum atom `A` and separated values has the
paper's one-variable planar concentration bound. -/
theorem separated_atom_small_ball_sharp {α : Type*} [Fintype α] (Y : α → ℂ)
    {r δ A : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (hA : 0 ≤ A)
    (hsep : ∀ a b, Y a ≠ Y b → δ ≤ dist (Y a) (Y b))
    (hatom : ∀ w : ℂ, uniformProbability (fun a => Y a = w) ≤ A) (z : ℂ) :
    uniformProbability (fun a => ‖Y a - z‖ ≤ r) ≤ (1 + 2 * r / δ) ^ 2 * A := by
  classical
  let T := (Finset.univ.image Y).filter (fun w => dist w z ≤ r)
  have he : (fun a => ‖Y a - z‖ ≤ r) = (fun a => ∃ w ∈ T, Y a = w) := by
    funext a
    apply propext
    constructor
    · intro ha
      exact ⟨Y a, Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, by simpa only [dist_eq_norm] using ha⟩, rfl⟩
    · rintro ⟨w, hw, haw⟩
      have h := (Finset.mem_filter.mp hw).2
      simpa only [← haw, dist_eq_norm] using h
  have hc : (T.card : ℝ) ≤ (1 + 2 * r / δ) ^ 2 := by
    apply separated_complex_card_sharp hr hδ
    · intro w hw v hv hwv
      rcases Finset.mem_image.mp (Finset.mem_filter.mp hw).1 with ⟨a, _, rfl⟩
      rcases Finset.mem_image.mp (Finset.mem_filter.mp hv).1 with ⟨b, _, rfl⟩
      exact hsep a b hwv
    · intro w hw
      exact (Finset.mem_filter.mp hw).2
  rw [he]
  calc
    _ ≤ ∑ w ∈ T, uniformProbability (fun a => Y a = w) := uniformProbability_finset_exists_le T _
    _ ≤ ∑ _w ∈ T, A := Finset.sum_le_sum (fun w _ => hatom w)
    _ = (T.card : ℝ) * A := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hA

theorem separated_atom_small_ball {α : Type*} [Fintype α] (Y : α → ℂ)
    {r δ A : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (hA : 0 ≤ A)
    (hsep : ∀ a b, Y a ≠ Y b → δ ≤ dist (Y a) (Y b))
    (hatom : ∀ w : ℂ, uniformProbability (fun a => Y a = w) ≤ A) (z : ℂ) :
    uniformProbability (fun a => ‖Y a - z‖ ≤ r) ≤ (2 + 8 * r ^ 2 / δ ^ 2) * A :=
  (separated_atom_small_ball_sharp Y hr hδ hA hsep hatom z).trans
    (mul_le_mul_of_nonneg_right planar_packing_relaxation hA)

/-- The one-variable spread-part estimate at the exact radius used to
verify the atom hypothesis in the paper's Miroshnikov branch. -/
theorem spread_atom_source_scale {α : Type*} [Fintype α] (Y : α → ℂ)
    {d k : ℕ} {h τ : ℝ} (hd : 0 < d) (hk : 0 < k) (hh : 0 < h) (hτ : 0 ≤ τ)
    (hsep : ∀ a b, Y a ≠ Y b → (d : ℝ) / k ≤ dist (Y a) (Y b))
    (hatom : ∀ w : ℂ, uniformProbability (fun a => Y a = w) ≤ 4 / h) (z : ℂ) :
    uniformProbability (fun a => ‖Y a - z‖ ≤ τ * Real.sqrt (2 * (d : ℝ)) / k) ≤
      (8 + 64 * τ ^ 2 / d) / h := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hp := separated_atom_small_ball Y (r := τ * Real.sqrt (2 * (d : ℝ)) / k) (by positivity)
    (div_pos hd' hk') (by positivity : 0 ≤ 4 / h) hsep hatom z
  apply hp.trans_eq
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (d : ℝ)), div_pow]
  field_simp
  ring

/-- A uniform absolute large-degree threshold verifies the strict atom
condition needed in the high-height spread branch. -/
theorem spread_atom_le_half {α : Type*} [Fintype α] (Y : α → ℂ)
    {d k Q : ℕ} {h τ : ℝ} (hd : 65536 ≤ d) (hk : 0 < k) (hh : 32 < h) (hτ : 0 ≤ τ)
    (hQ : Q ≤ d) (hsmall : τ ^ 2 ≤ h * Real.sqrt Q)
    (hsep : ∀ a b, Y a ≠ Y b → (d : ℝ) / k ≤ dist (Y a) (Y b))
    (hatom : ∀ w : ℂ, uniformProbability (fun a => Y a = w) ≤ 4 / h) (z : ℂ) :
    uniformProbability (fun a => ‖Y a - z‖ ≤ τ * Real.sqrt (2 * (d : ℝ)) / k) ≤ 1 / 2 := by
  have hdpos : 0 < d := by omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hhpos : 0 < h := by linarith
  have hsqrt : (256 : ℝ) ≤ Real.sqrt d := by
    apply (Real.le_sqrt (by norm_num) hd'.le).mpr
    exact_mod_cast hd
  have hsqQ := Real.sqrt_le_sqrt (show (Q : ℝ) ≤ d by exact_mod_cast hQ)
  have hτsq : τ ^ 2 ≤ h * Real.sqrt d :=
    hsmall.trans (mul_le_mul_of_nonneg_left hsqQ hhpos.le)
  have hsqrt_sq := Real.sq_sqrt hd'.le
  have hbound : (8 + 64 * τ ^ 2 / d) / h ≤ 1 / 2 := by
    apply (div_le_iff₀ hhpos).mpr
    have hτd : τ ^ 2 / (d : ℝ) ≤ h / Real.sqrt d := by
      apply (div_le_div_iff₀ hd' (Real.sqrt_pos.mpr hd')).mpr
      have hm := mul_le_mul_of_nonneg_right hτsq (Real.sqrt_nonneg (d : ℝ))
      nlinarith
    have hsmallterm : h / Real.sqrt d ≤ h / 256 :=
      div_le_div_of_nonneg_left hhpos.le (by norm_num) hsqrt
    rw [mul_div_assoc]
    have hscaled := mul_le_mul_of_nonneg_left (hτd.trans hsmallterm) (by norm_num : (0 : ℝ) ≤ 64)
    linarith
  exact (spread_atom_source_scale Y hdpos hk hhpos hτ hsep hatom z).trans hbound

/-- The Esseen branch's single-summand hypothesis, including the essential
height lower bound two and an explicit large-degree threshold. -/
theorem spread_atom_le_five_sixths {α : Type*} [Fintype α] (Y : α → ℂ)
    {d k : ℕ} {h : ℝ} (hd : 65536 ≤ d) (hk : 0 < k) (hh : 2 ≤ h)
    (hsep : ∀ a b, Y a ≠ Y b → (d : ℝ) / k ≤ dist (Y a) (Y b))
    (hatom : ∀ w : ℂ, uniformProbability (fun a => Y a = w) ≤ 4 / (h + 3)) (z : ℂ) :
    uniformProbability (fun a => ‖Y a - z‖ ≤ Real.sqrt d / k) ≤ 5 / 6 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsqrtpos := Real.sqrt_pos.mpr hdpos
  have hsqrt : (256 : ℝ) ≤ Real.sqrt d :=
    (Real.le_sqrt (by norm_num) hdpos.le).mpr (by exact_mod_cast hd)
  have hprob := separated_atom_small_ball_sharp Y (r := Real.sqrt d / k)
    (by positivity) (div_pos hdpos hkpos) (by positivity : 0 ≤ 4 / (h + 3)) hsep hatom z
  have hratio : (Real.sqrt d / (k : ℝ)) / ((d : ℝ) / k) = 1 / Real.sqrt d := by
    field_simp
    nlinarith [Real.sq_sqrt hdpos.le]
  have hrad : 1 + 2 * (Real.sqrt d / (k : ℝ)) / ((d : ℝ) / k) ≤ 129 / 128 := by
    rw [mul_div_assoc, hratio]
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num) hsqrt
    linarith
  have hrad0 : 0 ≤ 1 + 2 * (Real.sqrt d / (k : ℝ)) / ((d : ℝ) / k) := by positivity
  have hmass : 4 / (h + 3) ≤ (4 / 5 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  apply hprob.trans
  calc
    _ ≤ (129 / 128 : ℝ) ^ 2 * (4 / 5) :=
      mul_le_mul (pow_le_pow_left₀ hrad0 hrad 2) hmass (by positivity) (by positivity)
    _ ≤ _ := by norm_num

end CircularLaw
