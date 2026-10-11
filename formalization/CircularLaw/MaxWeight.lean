import CircularLaw.FiniteMean

/-!
# The max-weight estimate: finite-coordinate model

Section 3 applies the estimate to the dyadic weight of a uniform coordinate.
This file develops that exact law without assuming the max-weight lemma.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def pairDispersion {α : Type*} [Fintype α] (b : α → ℝ) : ℝ :=
  finiteMean (fun p : α × α => |b p.1 - b p.2|)

theorem pairDispersion_nonneg {α : Type*} [Fintype α] (b : α → ℝ) :
    0 ≤ pairDispersion b :=
  finiteMean_nonneg fun _ => abs_nonneg _

/-- The expected pair maximum gains half the mean pairwise dispersion. -/
theorem finiteMean_pair_max {α : Type*} [Fintype α] [Nonempty α] (b : α → ℝ) :
    finiteMean (fun p : α × α => max (b p.1) (b p.2)) =
      finiteMean b + pairDispersion b / 2 := by
  have hmax (x y : ℝ) : max x y = (x + y + |x - y|) / 2 := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  simp_rw [hmax, div_eq_mul_inv, finiteMean_mul_const, finiteMean_add,
    finiteMean_fst, finiteMean_snd]
  dsimp [pairDispersion]
  ring

/-- The independent-pair square identity, used to avoid an assumed
Efron--Stein inequality in this finite model. -/
theorem finiteMean_pair_sq_diff {α : Type*} [Fintype α] [Nonempty α] (b : α → ℝ) :
    finiteMean (fun p : α × α => (b p.1 - b p.2) ^ 2) =
      2 * (finiteMean (fun a => (b a) ^ 2) - (finiteMean b) ^ 2) := by
  have hexpand (p : α × α) : (b p.1 - b p.2) ^ 2 =
      (b p.1) ^ 2 + (b p.2) ^ 2 - 2 * (b p.1 * b p.2) := by ring
  simp_rw [hexpand, finiteMean_sub, finiteMean_add, finiteMean_const_mul]
  rw [finiteMean_fst (fun a => (b a) ^ 2), finiteMean_snd (fun a => (b a) ^ 2),
    finiteMean_prod]
  ring

theorem finiteMean_centered_sq {α : Type*} [Fintype α] [Nonempty α] (b : α → ℝ) :
    finiteMean (fun a => (b a - finiteMean b) ^ 2) =
      finiteMean (fun a => (b a) ^ 2) - (finiteMean b) ^ 2 := by
  have hexpand (a : α) : (b a - finiteMean b) ^ 2 =
      (b a) ^ 2 - 2 * finiteMean b * b a + (finiteMean b) ^ 2 := by ring
  simp_rw [hexpand, finiteMean_add, finiteMean_sub, finiteMean_const_mul,
    finiteMean_const]
  ring

/-- The squared deviation of a pair maximum from the original mean is
controlled by the squared difference of two independent copies. -/
theorem finiteMean_max_centered_sq_le {α : Type*} [Fintype α] [Nonempty α]
    (b : α → ℝ) :
    finiteMean (fun p : α × α => (max (b p.1) (b p.2) - finiteMean b) ^ 2) ≤
      finiteMean (fun p : α × α => (b p.1 - b p.2) ^ 2) := by
  calc
    _ ≤ finiteMean (fun p : α × α =>
        (b p.1 - finiteMean b) ^ 2 + (b p.2 - finiteMean b) ^ 2) := by
      apply finiteMean_mono
      intro p
      rcases le_total (b p.1) (b p.2) with h | h
      · rw [max_eq_right h]
        nlinarith [sq_nonneg (b p.1 - finiteMean b)]
      · rw [max_eq_left h]
        nlinarith [sq_nonneg (b p.2 - finiteMean b)]
    _ = _ := by
      rw [finiteMean_add,
        finiteMean_fst (fun a => (b a - finiteMean b) ^ 2),
        finiteMean_snd (fun a => (b a - finiteMean b) ^ 2),
        finiteMean_centered_sq, finiteMean_pair_sq_diff]
      ring

theorem finiteMean_pair_sq_le_range_dispersion {α : Type*} [Fintype α]
    (b : α → ℝ) {R : ℝ} (hrange : ∀ a a', |b a - b a'| ≤ R) :
    finiteMean (fun p : α × α => (b p.1 - b p.2) ^ 2) ≤ R * pairDispersion b := by
  rw [pairDispersion, ← finiteMean_const_mul]
  apply finiteMean_mono
  intro p
  have h := mul_le_mul_of_nonneg_right (hrange p.1 p.2) (abs_nonneg (b p.1 - b p.2))
  simpa [sq_abs, ← sq] using h

/-- Every coordinate lies within the support diameter of its mean. -/
theorem abs_sub_finiteMean_le_range {α : Type*} [Fintype α] [Nonempty α]
    (b : α → ℝ) {R : ℝ} (hrange : ∀ a a', |b a - b a'| ≤ R) (a : α) :
    |b a - finiteMean b| ≤ R := by
  have hid : finiteMean (fun a' => b a - b a') = b a - finiteMean b := by
    rw [finiteMean_sub, finiteMean_const]
  rw [← hid]
  calc
    _ ≤ finiteMean (fun a' => |b a - b a'|) := abs_finiteMean_le _
    _ ≤ finiteMean (fun _ : α => R) := finiteMean_mono (hrange a)
    _ = R := finiteMean_const R

/-- Quadratic control of the exponential with its linear term retained. -/
theorem finiteMean_exp_le_quadratic {α : Type*} [Fintype α] [Nonempty α]
    (x : α → ℝ) (hx : ∀ a, |x a| ≤ 1) :
    finiteMean (fun a => Real.exp (x a)) ≤
      1 + finiteMean x + finiteMean (fun a => (x a) ^ 2) := by
  calc
    _ ≤ finiteMean (fun a => 1 + x a + (x a) ^ 2) := by
      apply finiteMean_mono
      intro a
      have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hx a))).2
      linarith
    _ = _ := by rw [finiteMean_add, finiteMean_add, finiteMean_const]

/-- The finite-coordinate pair maximum has an exponential-moment gain
proportional to its pairwise dispersion. This proves the analytic estimate
used in the max-weight argument, with an explicit smallness constant. -/
theorem pair_max_mgf_le {α : Type*} [Fintype α] [Nonempty α] (b : α → ℝ)
    {R θ : ℝ} (hrange : ∀ a a', |b a - b a'| ≤ R)
    (hθ : 0 ≤ θ) (hsmall : θ * R ≤ 1 / 4) :
    finiteMean (fun p : α × α => Real.exp (-θ * max (b p.1) (b p.2))) ≤
      Real.exp (-θ * finiteMean b - θ * pairDispersion b / 4) := by
  let μ := finiteMean b
  let D := pairDispersion b
  let Z := fun p : α × α => max (b p.1) (b p.2)
  have hD : 0 ≤ D := pairDispersion_nonneg b
  have hbound (p : α × α) : |Z p - μ| ≤ R := by
    dsimp [Z, μ]
    rcases le_total (b p.1) (b p.2) with h | h
    · rw [max_eq_right h]
      exact abs_sub_finiteMean_le_range b hrange p.2
    · rw [max_eq_left h]
      exact abs_sub_finiteMean_le_range b hrange p.1
  have hnorm (p : α × α) : |-θ * (Z p - μ)| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hθ]
    have := mul_le_mul_of_nonneg_left (hbound p) hθ
    linarith
  have hmean : finiteMean (fun p => -θ * (Z p - μ)) = -θ * D / 2 := by
    rw [finiteMean_const_mul, finiteMean_sub, finiteMean_const]
    dsimp [Z, μ, D]
    rw [finiteMean_pair_max]
    ring
  have hsq : finiteMean (fun p => (-θ * (Z p - μ)) ^ 2) ≤ θ ^ 2 * (R * D) := by
    have hidentity (p : α × α) : (-θ * (Z p - μ)) ^ 2 = θ ^ 2 * (Z p - μ) ^ 2 := by ring
    simp_rw [hidentity, finiteMean_const_mul]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg θ)
    exact le_trans (finiteMean_max_centered_sq_le b)
      (finiteMean_pair_sq_le_range_dispersion b hrange)
  have hgain : finiteMean (fun p => Real.exp (-θ * (Z p - μ))) ≤ Real.exp (-θ * D / 4) := by
    have hquad := finiteMean_exp_le_quadratic (fun p => -θ * (Z p - μ)) hnorm
    rw [hmean] at hquad
    have habsorb : θ ^ 2 * (R * D) ≤ θ * D / 4 := by
      have := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hθ hD)
      nlinarith
    have hexp := Real.add_one_le_exp (-θ * D / 4)
    linarith
  have hexp (p : α × α) : Real.exp (-θ * Z p) =
      Real.exp (-θ * μ) * Real.exp (-θ * (Z p - μ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change finiteMean (fun p => Real.exp (-θ * Z p)) ≤ _
  simp_rw [hexp, finiteMean_const_mul]
  calc
    _ ≤ Real.exp (-θ * μ) * Real.exp (-θ * D / 4) :=
      mul_le_mul_of_nonneg_left hgain (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      dsimp [μ, D]
      congr 1
      ring

/-- Tensorize the pair-moment estimate. The observable `W` can be any upper
bound for every pair maximum; it need not equal the maximum itself. -/
theorem paired_max_weight {α : Type*} [Fintype α] [Nonempty α]
    (b : α → ℝ) {t : ℕ} (ht : 0 < t) {R a : ℝ}
    (hrange : ∀ x y, |b x - b y| ≤ R) (ha : 0 ≤ a)
    (hsmall : (a / (t : ℝ)) * R ≤ 1 / 4)
    (W : (Fin t → α × α) → ℝ)
    (hW : ∀ samples i, max (b (samples i).1) (b (samples i).2) ≤ W samples) :
    finiteMean (fun samples => Real.exp (-a * W samples)) ≤
      Real.exp (-a * finiteMean b - a * pairDispersion b / 4) := by
  let θ := a / (t : ℝ)
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hθ : 0 ≤ θ := div_nonneg ha ht'.le
  have hθt : θ * t = a := by dsimp [θ]; field_simp
  have hpoint (samples : Fin t → α × α) :
      Real.exp (-a * W samples) ≤
        ∏ i, Real.exp (-θ * max (b (samples i).1) (b (samples i).2)) := by
    have hsum : (∑ i, max (b (samples i).1) (b (samples i).2)) ≤ (t : ℝ) * W samples := by
      calc
        _ ≤ ∑ _i : Fin t, W samples := Finset.sum_le_sum fun i _ => hW samples i
        _ = _ := by simp
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    rw [← Finset.mul_sum]
    have hmul := mul_le_mul_of_nonneg_left hsum hθ
    rw [← mul_assoc, hθt] at hmul
    nlinarith
  have hpair := pair_max_mgf_le b hrange hθ hsmall
  calc
    _ ≤ finiteMean (fun samples : Fin t → α × α =>
        ∏ i, Real.exp (-θ * max (b (samples i).1) (b (samples i).2))) :=
      finiteMean_mono hpoint
    _ = (finiteMean (fun p : α × α => Real.exp (-θ * max (b p.1) (b p.2)))) ^ t := by
      rw [finiteMean_pi_prod (fun (_ : Fin t) (p : α × α) =>
        Real.exp (-θ * max (b p.1) (b p.2)))]
      simp
    _ ≤ (Real.exp (-θ * finiteMean b - θ * pairDispersion b / 4)) ^ t := by
      exact pow_le_pow_left₀ (finiteMean_nonneg fun _ => Real.exp_nonneg _) hpair t
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [θ]
      field_simp

/-- Group coordinates into independent pairs and a remainder by a bijection
of the coordinate index set. Both odd and even sample sizes are supported. -/
def pairSamplesEquiv {α : Type*} {d t r : ℕ}
    (index : (Fin t × Fin 2) ⊕ Fin r ≃ Fin d) :
    (Fin d → α) ≃ (Fin t → α × α) × (Fin r → α) where
  toFun samples :=
    (fun i => (samples (index (Sum.inl (i, 0))), samples (index (Sum.inl (i, 1)))),
      fun j => samples (index (Sum.inr j)))
  invFun samples j := match index.symm j with
    | Sum.inl (i, k) => ![(samples.1 i).1, (samples.1 i).2] k
    | Sum.inr k => samples.2 k
  left_inv samples := by
    funext j
    generalize h : index.symm j = q
    have hj : index q = j := by rw [← h, index.apply_symm_apply]
    cases q with
    | inl p =>
      rcases p with ⟨i, k⟩
      fin_cases k <;> simp_all
    | inr k => simp_all
  right_inv samples := by
    rcases samples with ⟨pairs, rest⟩
    apply Prod.ext
    · funext i
      simp
    · funext i
      simp

/-- The maximum of a nonempty list of sampled coordinate values. -/
def sampleMaximum {α : Type*} (b : α → ℝ) {d : ℕ} (hd : 0 < d)
    (samples : Fin d → α) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun i => b (samples i))

theorem le_sampleMaximum {α : Type*} (b : α → ℝ) {d : ℕ} (hd : 0 < d)
    (samples : Fin d → α) (i : Fin d) : b (samples i) ≤ sampleMaximum b hd samples := by
  unfold sampleMaximum
  exact Finset.le_sup' (fun i => b (samples i)) (Finset.mem_univ i)

/-- The max-weight lemma for the exact finite-coordinate law used in the
paper. The constants are explicit: `ε₀ = 1/12` and `c = log(2)/4`. -/
theorem max_weight_finite {α : Type*} [Fintype α] [Nonempty α] (b : α → ℝ)
    {d : ℕ} (hd : 2 ≤ d)
    (hrange : ∀ x y, |b x - b y| ≤ (d : ℝ) / 12) :
    finiteMean (fun samples : Fin d → α =>
      Real.exp (-Real.log 2 * sampleMaximum b (by omega) samples)) ≤
      Real.exp (-Real.log 2 * finiteMean b - (Real.log 2 / 4) * pairDispersion b) := by
  classical
  let t := d / 2
  let r := d % 2
  have ht : 0 < t := by dsimp [t]; omega
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hsplit : t * 2 + r = d := by dsimp [t, r]; omega
  let index : (Fin t × Fin 2) ⊕ Fin r ≃ Fin d :=
    ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin r))).trans finSumFinEquiv).trans
      (finCongr hsplit)
  let e : (Fin d → α) ≃ (Fin t → α × α) × (Fin r → α) := pairSamplesEquiv index
  have hlog : (0 : ℝ) ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogle : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hd3 : (d : ℝ) ≤ 3 * t := by exact_mod_cast (show d ≤ 3 * t by dsimp [t]; omega)
  have hsmall : (Real.log 2 / (t : ℝ)) * ((d : ℝ) / 12) ≤ 1 / 4 := by
    have hratio : ((d : ℝ) / 12) / t ≤ 1 / 4 := by
      apply (div_le_iff₀ ht').mpr
      linarith
    have := mul_le_mul hlogle hratio (by positivity : (0 : ℝ) ≤ ((d : ℝ) / 12) / t)
      (by norm_num : (0 : ℝ) ≤ 1)
    calc
      _ = Real.log 2 * ((d : ℝ) / 12 / t) := by ring
      _ ≤ 1 / 4 := by simpa only [one_mul] using this
  have hconditional (rest : Fin r → α) :
      finiteMean (fun pairs : Fin t → α × α =>
        Real.exp (-Real.log 2 * sampleMaximum b (by omega) (e.symm (pairs, rest)))) ≤
        Real.exp (-Real.log 2 * finiteMean b - Real.log 2 * pairDispersion b / 4) := by
    apply paired_max_weight b ht hrange hlog hsmall
    intro pairs i
    apply max_le
    · have h := le_sampleMaximum b (by omega) (e.symm (pairs, rest)) (index (Sum.inl (i, 0)))
      simpa [e, pairSamplesEquiv] using h
    · have h := le_sampleMaximum b (by omega) (e.symm (pairs, rest)) (index (Sum.inl (i, 1)))
      simpa [e, pairSamplesEquiv] using h
  rw [← finiteMean_reindex e.symm, finiteMean_prod_fubini]
  calc
    _ ≤ finiteMean (fun _rest : Fin r → α =>
        Real.exp (-Real.log 2 * finiteMean b - Real.log 2 * pairDispersion b / 4)) :=
      finiteMean_mono hconditional
    _ = _ := by rw [finiteMean_const]; congr 1; ring

end CircularLaw
