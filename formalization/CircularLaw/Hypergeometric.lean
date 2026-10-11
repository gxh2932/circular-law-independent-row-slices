import CircularLaw.DoubleCounting
import CircularLaw.FiniteMean

/-!
# Concentration on exact slices

Sampling without replacement is treated by counting supersets of a fixed
set. In particular, coordinate indicators are never assumed independent.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

/-- Factorial moments of sampling without replacement are bounded by the
corresponding independent-sampling moments. -/
theorem choose_ratio_power_bound {m n : ℕ} (hmn : m ≤ n) (q : ℕ) :
    (n : ℝ) ^ q * m.choose q ≤ (m : ℝ) ^ q * n.choose q := by
  induction q with
  | zero => simp
  | succ q ih =>
    by_cases hq : q + 1 ≤ m
    · have hqm : q ≤ m := by omega
      have hqn : q ≤ n := le_trans hqm hmn
      have hmrec : (m.choose (q + 1) : ℝ) * (q + 1) = m.choose q * ((m : ℝ) - q) := by
        exact_mod_cast (Nat.choose_succ_right_eq m q)
      have hnrec : (n.choose (q + 1) : ℝ) * (q + 1) = n.choose q * ((n : ℝ) - q) := by
        exact_mod_cast (Nat.choose_succ_right_eq n q)
      have hfactor : (n : ℝ) * (m - (q : ℝ)) ≤ m * ((n : ℝ) - q) := by
        have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
        nlinarith [Nat.cast_nonneg (α := ℝ) q]
      have hnonneg : 0 ≤ (n : ℝ) * (m - (q : ℝ)) := by
        apply mul_nonneg (by positivity)
        exact sub_nonneg.mpr (by exact_mod_cast hqm)
      have hstep := le_trans (mul_le_mul_of_nonneg_right ih hnonneg)
        (mul_le_mul_of_nonneg_left hfactor (by positivity :
          0 ≤ (m : ℝ) ^ q * n.choose q))
      apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < q + 1)).mp
      calc
        _ = ((n : ℝ) ^ q * m.choose q) * (n * (m - (q : ℝ))) := by
          rw [pow_succ]
          linear_combination (n : ℝ) ^ q * n * hmrec
        _ ≤ ((m : ℝ) ^ q * n.choose q) * (m * (n - (q : ℝ))) := hstep
        _ = _ := by
          rw [pow_succ]
          linear_combination -(m : ℝ) ^ q * m * hnrec
    · rw [Nat.choose_eq_zero_of_lt (by omega : m < q + 1)]
      simp only [Nat.cast_zero, mul_zero]
      positivity

theorem card_slices_containing_set {n d : ℕ} {T : Finset (Fin n)} (hq : T.card ≤ d) :
    Nat.card {s : RowSlice n d // T ⊆ s.val} =
      (n - T.card).choose (d - T.card) := by
  classical
  let A := (Finset.univ.powersetCard d).filter (fun s => T ⊆ s)
  let B := (Finset.univ \ T).powersetCard (d - T.card)
  have hcard : A.card = B.card := by
    refine Finset.card_bij' (fun s _ => s \ T) (fun u _ => u ∪ T) ?_ ?_ ?_ ?_
    · intro s hs
      rcases Finset.mem_filter.mp hs with ⟨hsd, hTs⟩
      rcases Finset.mem_powersetCard.mp hsd with ⟨_, hsd⟩
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
        exact hx.2
      · rw [Finset.card_sdiff_of_subset hTs, hsd]
    · intro u hu
      rcases Finset.mem_powersetCard.mp hu with ⟨huT, hud⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        refine ⟨Finset.subset_univ _, ?_⟩
        have hdis : Disjoint u T := by
          apply Finset.disjoint_left.mpr
          intro x hx hxT
          exact (Finset.mem_sdiff.mp (huT hx)).2 hxT
        rw [Finset.card_union_of_disjoint hdis, hud]
        omega
      · exact Finset.subset_union_right
    · intro s hs
      have hTs := (Finset.mem_filter.mp hs).2
      exact Finset.sdiff_union_of_subset hTs
    · intro u hu
      have huT := (Finset.mem_powersetCard.mp hu).1
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro h
        exact h.1.resolve_right h.2
      · intro hx
        exact ⟨Or.inl hx, (Finset.mem_sdiff.mp (huT hx)).2⟩
  let e : {s : RowSlice n d // T ⊆ s.val} ≃ {s // s ∈ A} :=
    { toFun := fun s => ⟨s.val.val, Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.val.property⟩, s.property⟩⟩
      invFun := fun s => ⟨⟨s.val, (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp s.property).1).2⟩, (Finset.mem_filter.mp s.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, hcard]
  simp only [B, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ T),
    Finset.card_univ, Fintype.card_fin]

theorem slice_containment_probability_le {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (T : Finset (Fin n)) :
    uniformProbability (fun s : RowSlice n d => T ⊆ s.val) ≤
      ((d : ℝ) / n) ^ T.card := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : T.card ≤ n := by simpa using Finset.card_le_univ T
  have hcnd : (0 : ℝ) < n.choose d := by exact_mod_cast Nat.choose_pos hd
  have hcnq : (0 : ℝ) < n.choose T.card := by exact_mod_cast Nat.choose_pos hq
  by_cases hqd : T.card ≤ d
  · have hidentity : (n.choose d : ℝ) * d.choose T.card =
        n.choose T.card * (n - T.card).choose (d - T.card) := by
      exact_mod_cast (Nat.choose_mul (n := n) hqd)
    have hratio : ((n - T.card).choose (d - T.card) : ℝ) / n.choose d =
        (d.choose T.card : ℝ) / n.choose T.card := by
      apply (div_eq_div_iff hcnd.ne' hcnq.ne').mpr
      nlinarith [hidentity]
    simp only [uniformProbability, card_slices_containing_set hqd,
      Nat.card_eq_fintype_card, card_rowSlice, hratio]
    rw [div_pow]
    apply (div_le_div_iff₀ hcnq (pow_pos hn' _)).mpr
    simpa only [mul_comm] using choose_ratio_power_bound hd T.card
  · have hempty : IsEmpty {s : RowSlice n d // T ⊆ s.val} := by
      constructor
      intro s
      have hc := Finset.card_le_card s.property
      rw [s.val.property] at hc
      exact hqd hc
    haveI := hempty
    simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_of_isEmpty,
      Nat.cast_zero, zero_div]
    positivity

theorem finiteMean_indicator {α : Type*} [Fintype α] (event : α → Prop) [DecidablePred event] :
    finiteMean (fun x => if event x then (1 : ℝ) else 0) = uniformProbability event := by
  classical
  simp only [finiteMean, uniformProbability, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  simp

theorem finiteMean_finset_sum {α β : Type*} [Fintype α] (s : Finset β) (f : β → α → ℝ) :
    finiteMean (fun a => ∑ b ∈ s, f b a) = ∑ b ∈ s, finiteMean (f b) := by
  unfold finiteMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteMean_slice_mgf_le {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (M : Finset (Fin n)) {x : ℝ} (hx : 0 ≤ x) :
    finiteMean (fun s : RowSlice n d => (1 + x) ^ (s.val ∩ M).card) ≤
      (1 + x * ((d : ℝ) / n)) ^ M.card := by
  classical
  have hexpand (s : RowSlice n d) : (1 + x) ^ (s.val ∩ M).card =
      ∑ T ∈ M.powerset, if T ⊆ s.val then x ^ T.card else 0 := by
    have hprod := Finset.prod_one_add (f := fun _ : Fin n => x) (s.val ∩ M)
    simp only [Finset.prod_const] at hprod
    rw [hprod]
    rw [← Finset.sum_filter]
    congr 1
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact Finset.subset_inter_iff.trans and_comm
  simp_rw [hexpand]
  rw [finiteMean_finset_sum]
  calc
    _ = ∑ T ∈ M.powerset, x ^ T.card * uniformProbability
        (fun s : RowSlice n d => T ⊆ s.val) := by
      apply Finset.sum_congr rfl
      intro T _
      rw [← finiteMean_indicator, ← finiteMean_const_mul]
      congr 1
      funext s
      split_ifs <;> simp
    _ ≤ ∑ T ∈ M.powerset, (x * ((d : ℝ) / n)) ^ T.card := by
      apply Finset.sum_le_sum
      intro T _
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (slice_containment_probability_le hn hd T)
        (pow_nonneg hx _)
    _ = _ := by
      have hprod := Finset.prod_one_add (f := fun _ : Fin n => x * ((d : ℝ) / n)) M
      simpa only [Finset.prod_const] using hprod.symm

theorem finite_uniform_markov {α : Type*} [Fintype α] (event : α → Prop)
    (f : α → ℝ) {a : ℝ} (ha : 0 < a) (hf : ∀ x, 0 ≤ f x)
    (hthreshold : ∀ x, event x → a ≤ f x) :
    uniformProbability event ≤ finiteMean f / a := by
  classical
  apply (le_div_iff₀ ha).mpr
  have hpoint (x : α) : a * (if event x then (1 : ℝ) else 0) ≤ f x := by
    split_ifs with h
    · simpa using hthreshold x h
    · simpa using hf x
  have h := finiteMean_mono hpoint
  rw [finiteMean_const_mul, finiteMean_indicator] at h
  simpa only [mul_comm] using h

def sliceTailRate : ℝ := 3 * Real.log (3 / 2) / 4 - 1 / 4

theorem sliceTailRate_pos : 0 < sliceTailRate := by
  have h := Real.log_lt_sub_one_of_pos (x := (3 / 2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  rw [Real.log_inv] at h
  norm_num at h
  dsimp [sliceTailRate]
  linarith

theorem finiteMean_slice_mgf_half_le {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (M : Finset (Fin n)) (hM : (M.card : ℝ) ≤ (n : ℝ) / 2) :
    finiteMean (fun s : RowSlice n d => (3 / 2 : ℝ) ^ (s.val ∩ M).card) ≤
      Real.exp ((d : ℝ) / 4) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmgf := finiteMean_slice_mgf_le hn hd M (by norm_num : (0 : ℝ) ≤ 1 / 2)
  norm_num only [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] at hmgf
  have hfactor : (M.card : ℝ) * (1 / 2 * ((d : ℝ) / n)) ≤ (d : ℝ) / 4 := by
    have hh := mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ (d : ℝ) / (2 * n))
    have heq : ((d : ℝ) / (2 * n)) * ((n : ℝ) / 2) = (d : ℝ) / 4 := by field_simp; ring
    rw [heq] at hh
    convert hh using 1
    ring
  calc
    _ ≤ (1 + 1 / 2 * ((d : ℝ) / n)) ^ M.card := hmgf
    _ ≤ (Real.exp (1 / 2 * ((d : ℝ) / n))) ^ M.card :=
      pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / 2 * ((d : ℝ) / n))]) _
    _ = Real.exp ((M.card : ℝ) * (1 / 2 * ((d : ℝ) / n))) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hfactor

/-- Exponential lower tail for the number of sampled coordinates in a set
of size at least half the population. This follows from exact factorial
moments, without an independence assumption on slice coordinates. -/
theorem slice_occupancy_lower_tail {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (K : Finset (Fin n)) (hK : (n : ℝ) / 2 ≤ K.card) :
    uniformProbability (fun s : RowSlice n d => ((s.val ∩ K).card : ℝ) < (d : ℝ) / 4) ≤
      Real.exp (-sliceTailRate * d) := by
  classical
  let M := Finset.univ \ K
  let f := fun s : RowSlice n d => (3 / 2 : ℝ) ^ (s.val ∩ M).card
  let a := Real.exp (3 * Real.log (3 / 2) * d / 4)
  have hM : (M.card : ℝ) ≤ (n : ℝ) / 2 := by
    have hc : M.card + K.card = n := by
      simpa only [M, Finset.card_univ, Fintype.card_fin] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ K)
    have hc' : (M.card : ℝ) + K.card = n := by exact_mod_cast hc
    linarith
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hthreshold (s : RowSlice n d) (hs : ((s.val ∩ K).card : ℝ) < (d : ℝ) / 4) : a ≤ f s := by
    have heq : s.val ∩ M = s.val \ K := by ext x; simp [M]
    have hc : (s.val ∩ M).card + (s.val ∩ K).card = d := by
      rw [heq]
      simpa only [s.property] using Finset.card_sdiff_add_card_inter s.val K
    have hc' : ((s.val ∩ M).card : ℝ) + (s.val ∩ K).card = d := by exact_mod_cast hc
    have hmiss : 3 * (d : ℝ) / 4 ≤ (s.val ∩ M).card := by linarith
    dsimp [a, f]
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2), ← Real.exp_nat_mul]
    rw [Real.log_exp]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hmiss hlog.le
    nlinarith
  have hmarkov := finite_uniform_markov
    (fun s : RowSlice n d => ((s.val ∩ K).card : ℝ) < (d : ℝ) / 4)
    f (Real.exp_pos _) (fun _ => pow_nonneg (by norm_num) _) hthreshold
  calc
    _ ≤ finiteMean f / a := hmarkov
    _ ≤ Real.exp ((d : ℝ) / 4) / a := div_le_div_of_nonneg_right
      (finiteMean_slice_mgf_half_le hn hd M hM) (Real.exp_pos _).le
    _ = _ := by
      dsimp [a, sliceTailRate]
      rw [← Real.exp_sub]
      congr 1
      ring

/-- Connect the support counting law to the finite uniform probability. -/
theorem uniform_rowSlice_probability {n d : ℕ} (P : Finset (Fin n) → Prop)
    [DecidablePred P] :
    uniformProbability (fun s : RowSlice n d => P s.val) =
      (((Finset.univ.powersetCard d).filter P).card : ℝ) / n.choose d := by
  classical
  let A := (Finset.univ.powersetCard d).filter P
  let e : {s : RowSlice n d // P s.val} ≃ {s // s ∈ A} :=
    { toFun := fun s => ⟨s.val.val, Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.val.property⟩, s.property⟩⟩
      invFun := fun s => ⟨⟨s.val, (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp s.property).1).2⟩, (Finset.mem_filter.mp s.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [uniformProbability, Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, card_rowSlice]
  congr 3

/-- The complete pointwise concentration bound in manuscript
`lem:slice-double-count`, with an absolute exponential rate. -/
theorem slice_small_ball_exponential {n d m : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (K : Finset (Fin n)) (hK : (n : ℝ) / 2 ≤ K.card) (y : Fin n → ℂ) (ρ : ℝ)
    (hcluster : ∀ z : ℂ, (K.filter fun j => ‖y j - z‖ ≤ ρ).card ≤ m)
    (center : ℂ) :
    uniformProbability (fun s : RowSlice n d => ‖(∑ j ∈ s.val, y j) - center‖ ≤ ρ) ≤
      4 * (m : ℝ) / (n - d + 1 : ℕ) + Real.exp (-sliceTailRate * d) := by
  classical
  have hsmall := small_ball_probability_le_occupancy_tail hd hdn K y center ρ hcluster
  have htail := slice_occupancy_lower_tail (lt_of_lt_of_le hd hdn) hdn K hK
  rw [uniform_rowSlice_probability (fun S => ((S ∩ K).card : ℝ) < (d : ℝ) / 4)] at htail
  rw [uniform_rowSlice_probability (fun S => ‖(∑ j ∈ S, y j) - center‖ ≤ ρ)]
  unfold smallBallFamily at hsmall
  exact le_trans hsmall (add_le_add le_rfl htail)

/-- Allow the real-valued anti-clustering bound used in the manuscript.
Rounding downward is valid because every cluster cardinality is integral;
it preserves the exact coefficient `4*m/(n-d+1)`. -/
theorem slice_small_ball_exponential_real {n d : ℕ} {m : ℝ} (hd : 0 < d) (hdn : d ≤ n)
    (hm : 0 ≤ m) (K : Finset (Fin n)) (hK : (n : ℝ) / 2 ≤ K.card)
    (y : Fin n → ℂ) (ρ : ℝ)
    (hcluster : ∀ z : ℂ, ((K.filter fun j => ‖y j - z‖ ≤ ρ).card : ℝ) ≤ m)
    (center : ℂ) :
    uniformProbability (fun s : RowSlice n d => ‖(∑ j ∈ s.val, y j) - center‖ ≤ ρ) ≤
      4 * m / (n - d + 1 : ℕ) + Real.exp (-sliceTailRate * d) := by
  have hfloor (z : ℂ) : (K.filter fun j => ‖y j - z‖ ≤ ρ).card ≤ ⌊m⌋₊ :=
    (Nat.le_floor_iff hm).mpr (hcluster z)
  have h := slice_small_ball_exponential hd hdn K hK y ρ hfloor center
  apply le_trans h
  gcongr
  exact Nat.floor_le hm

/-- The manuscript's supremum over centers, with its degree and coordinate
anti-clustering hypotheses. Degree zero is included by the trivial bound
of one. The positive-degree proof above in fact allows every `d <= n`. -/
def SliceDoubleCountLemma : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n d : ℕ) (m : ℝ), 2 * d ≤ n → 1 ≤ m →
    ∀ (K : Finset (Fin n)), (n : ℝ) / 2 ≤ K.card →
    ∀ (y : Fin n → ℂ) (ρ : ℝ), 0 < ρ →
      (∀ z : ℂ, ((K.filter fun j => ‖y j - z‖ ≤ ρ).card : ℝ) ≤ m) →
      ⨆ center : ℂ,
        ENNReal.ofReal (uniformProbability (fun s : RowSlice n d =>
          ‖(∑ j ∈ s.val, y j) - center‖ ≤ ρ)) ≤
        ENNReal.ofReal (4 * m / (n - d + 1 : ℕ) + Real.exp (-c * d))

theorem slice_double_count_lemma : SliceDoubleCountLemma := by
  refine ⟨sliceTailRate, sliceTailRate_pos, ?_⟩
  intro n d m hdn hm K hK y ρ _hρ hcluster
  apply iSup_le
  intro center
  apply ENNReal.ofReal_le_ofReal
  by_cases hd : 0 < d
  · exact slice_small_ball_exponential_real hd (by omega) (by linarith) K hK y ρ hcluster center
  · have hdz : d = 0 := by omega
    subst d
    apply le_trans (uniformProbability_le_one _)
    simp only [Nat.sub_zero, Nat.cast_zero, mul_zero, Real.exp_zero]
    have hnonneg : 0 ≤ 4 * (m : ℝ) / (n + 1 : ℕ) := by positivity
    linarith

end CircularLaw
