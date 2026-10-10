import CircularLaw.MultinomialEntropy

/-!
# Entropy and factorial compression for four geometric families

An injective family/age code with four family labels and exponentially
decreasing masses has bounded entropy. The reference weights and all sums
are finite comparisons with the checked integer-lattice exponential series.
-/

noncomputable section
open Classical
open scoped BigOperators Nat

namespace CircularLaw

theorem four_family_exponential_sum {ι : Type*} (S : Finset ι)
    (family : ι → Bool × Bool) (age : ι → ℕ)
    (hCode : Set.InjOn (fun i => (family i, (age i : ℤ))) (S : Set ι))
    {α : ℝ} (hα : 0 < α) (hαOne : α ≤ 1) :
    (∑ i ∈ S, Real.exp (-α * (age i : ℝ))) ≤ 16 / α := by
  let A : Finset ℤ := S.image (fun i => (age i : ℤ))
  let K := S.image (fun i => (family i, (age i : ℤ)))
  have hSubset : K ⊆ (Finset.univ : Finset (Bool × Bool)) ×ˢ A := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  have hKernel : ∀ i : ι,
      Real.exp (-α * (age i : ℝ)) = integerGibbsKernel α 0 (age i : ℤ) := by
    intro i
    simp only [integerGibbsKernel, Int.cast_natCast, Int.cast_zero, sub_zero,
      abs_of_nonneg (Nat.cast_nonneg (age i) : (0 : ℝ) ≤ age i)]
  have hPartial := (integerGibbsKernel_summable hα 0).sum_le_tsum A
    (fun j _ => (integerGibbsKernel_pos α 0 j).le)
  have hBound := hPartial.trans (integerGibbsKernel_tsum_le hα hαOne 0)
  calc
    (∑ i ∈ S, Real.exp (-α * (age i : ℝ))) =
        ∑ z ∈ K, integerGibbsKernel α 0 z.2 := by
      rw [Finset.sum_image hCode]
      exact Finset.sum_congr rfl (fun i _ => hKernel i)
    _ ≤ ∑ z ∈ (Finset.univ : Finset (Bool × Bool)) ×ˢ A,
        integerGibbsKernel α 0 z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset
        (fun z _ _ => (integerGibbsKernel_pos α 0 z.2).le)
    _ = 4 * ∑ j ∈ A, integerGibbsKernel α 0 j := by
      simp only [Finset.sum_product, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ 4 * (4 / α) := mul_le_mul_of_nonneg_left hBound (by norm_num)
    _ = 16 / α := by ring

theorem age_exponential_half_bound (a : ℕ) :
    (a : ℝ) * Real.exp (-(a : ℝ) / 4) ≤ 8 * Real.exp (-(a : ℝ) / 8) := by
  have h := Real.add_one_le_exp ((a : ℝ) / 8)
  have hAge : (a : ℝ) ≤ 8 * Real.exp ((a : ℝ) / 8) := by linarith
  calc
    _ ≤ (8 * Real.exp ((a : ℝ) / 8)) * Real.exp (-(a : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hAge (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem four_family_weighted_age {ι : Type*} (S : Finset ι)
    (family : ι → Bool × Bool) (age : ι → ℕ)
    (hCode : Set.InjOn (fun i => (family i, (age i : ℤ))) (S : Set ι))
    (p : ι → ℝ) (hTail : ∀ i ∈ S, p i ≤ 8 * Real.exp (-(age i : ℝ) / 4)) :
    (∑ i ∈ S, p i * (age i : ℝ)) ≤ 8192 := by
  have hPoint : ∀ i ∈ S, p i * (age i : ℝ) ≤ 64 * Real.exp (-(age i : ℝ) / 8) := by
    intro i hi
    have h := mul_le_mul_of_nonneg_right (hTail i hi) (Nat.cast_nonneg (age i) : (0 : ℝ) ≤ age i)
    have hAge := mul_le_mul_of_nonneg_left (age_exponential_half_bound (age i)) (by norm_num : (0 : ℝ) ≤ 8)
    nlinarith only [h, hAge]
  have hSum := Finset.sum_le_sum hPoint
  rw [← Finset.mul_sum] at hSum
  have hExp := four_family_exponential_sum S family age hCode
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hExpForm : (∑ i ∈ S, Real.exp (-(age i : ℝ) / 8)) ≤ 128 := by
    norm_num at hExp
    convert hExp using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  linarith

theorem four_family_entropy_bound {ι : Type*} (S : Finset ι)
    (family : ι → Bool × Bool) (age : ι → ℕ)
    (hCode : Set.InjOn (fun i => (family i, (age i : ℤ))) (S : Set ι))
    (p : ι → ℝ) (hp : ∀ i ∈ S, 0 ≤ p i) (hMass : (∑ i ∈ S, p i) = 1)
    (hTail : ∀ i ∈ S, p i ≤ 8 * Real.exp (-(age i : ℝ) / 4)) :
    (∑ i ∈ S, -p i * Real.log (p i)) ≤ 4096 := by
  have hReference : (∑ i ∈ S, (1 / 64 : ℝ) * Real.exp (-(age i : ℝ) / 4)) ≤ 1 := by
    rw [← Finset.mul_sum]
    have h := four_family_exponential_sum S family age hCode
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hForm : (∑ i ∈ S, Real.exp (-(age i : ℝ) / 4)) ≤ 64 := by
      norm_num at h
      convert h using 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring
    linarith
  have hMoment := four_family_weighted_age S family age hCode p hTail
  have hPoint : ∀ i ∈ S, -p i * Real.log (p i) ≤
      (1 / 64 : ℝ) * Real.exp (-(age i : ℝ) / 4) + Real.log 64 * p i +
        (1 / 4 : ℝ) * (p i * (age i : ℝ)) := by
    intro i hi
    have h := entropy_atom_le_reference (hp i hi)
      (q := (1 / 64 : ℝ) * Real.exp (-(age i : ℝ) / 4)) (by positivity)
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
      show Real.log (1 / 64 : ℝ) = -Real.log 64 by rw [one_div, Real.log_inv]] at h
    nlinarith only [h]
  have hSum := Finset.sum_le_sum hPoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hMass, mul_one] at hSum
  have hLog : Real.log 64 ≤ 63 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 64)
    norm_num at h
    exact h
  rw [← Finset.mul_sum] at hReference
  linarith

theorem multinomialEntropyExponent_congr {ι : Type*} (S : Finset ι) {m f : ι → ℕ}
    (h : ∀ i ∈ S, m i = f i) :
    multinomialEntropyExponent S m = multinomialEntropyExponent S f := by
  unfold multinomialEntropyExponent
  rw [Finset.sum_congr rfl h]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => by rw [h i hi])

theorem factorial_ratio_le_entropy_finset {ι : Type*} (S : Finset ι) (m : ι → ℕ) :
    ((∑ i ∈ S, m i)! : ℝ) / (∏ i ∈ S, ((m i)! : ℝ)) ≤
      Real.exp (multinomialEntropyExponent S m) := by
  let f := fun i => if i ∈ S then m i else 0
  have hEq : ∀ i ∈ S, f i = m i := fun i hi => if_pos hi
  have h := factorial_ratio_le_entropy S f (fun i hi => by
    by_contra hnot
    exact hi (if_neg hnot))
  rw [Finset.sum_congr rfl hEq,
    Finset.prod_congr rfl (fun i hi => by rw [hEq i hi]),
    multinomialEntropyExponent_congr S hEq] at h
  exact h

theorem four_family_count_entropy {ι : Type*} (S : Finset ι)
    (family : ι → Bool × Bool) (age : ι → ℕ)
    (hCode : Set.InjOn (fun i => (family i, (age i : ℤ))) (S : Set ι))
    (m : ι → ℕ) (hN : 0 < ∑ i ∈ S, m i)
    (hTail : ∀ i ∈ S, (m i : ℝ) ≤
      8 * (∑ j ∈ S, m j : ℕ) * Real.exp (-(age i : ℝ) / 4)) :
    multinomialEntropyExponent S m ≤ 4096 * (∑ i ∈ S, m i : ℕ) := by
  let N : ℝ := (∑ i ∈ S, m i : ℕ)
  have hNR : 0 < N := by dsimp [N]; exact_mod_cast hN
  let p := fun i => (m i : ℝ) / N
  have hMass : (∑ i ∈ S, p i) = 1 := by
    dsimp [p, N]
    rw [← Finset.sum_div, ← Nat.cast_sum, div_self hNR.ne']
  have hEntropy := four_family_entropy_bound S family age hCode p
    (fun i _ => div_nonneg (Nat.cast_nonneg _) hNR.le) hMass
    (fun i hi => (div_le_iff₀ hNR).mpr (by
      have h := hTail i hi
      dsimp [N]
      nlinarith only [h]))
  have hEq : multinomialEntropyExponent S m = N * ∑ i ∈ S, -p i * Real.log (p i) := by
    rw [multinomialEntropyExponent, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [p, N]
    field_simp
  rw [hEq]
  have h := mul_le_mul_of_nonneg_left hEntropy hNR.le
  nlinarith only [h]

theorem four_family_factorial_compression {ι : Type*} (S : Finset ι)
    (family : ι → Bool × Bool) (age : ι → ℕ)
    (hCode : Set.InjOn (fun i => (family i, (age i : ℤ))) (S : Set ι))
    (m : ι → ℕ) (hN : 0 < ∑ i ∈ S, m i)
    (hTail : ∀ i ∈ S, (m i : ℝ) ≤
      8 * (∑ j ∈ S, m j : ℕ) * Real.exp (-(age i : ℝ) / 4)) :
    ((∑ i ∈ S, m i)! : ℝ) * Real.exp (-4096 * (∑ i ∈ S, m i : ℕ)) ≤
      ∏ i ∈ S, ((m i)! : ℝ) := by
  have hRatio := (factorial_ratio_le_entropy_finset S m).trans
    (Real.exp_le_exp.mpr (four_family_count_entropy S family age hCode m hN hTail))
  have hProd : (0 : ℝ) < ∏ i ∈ S, ((m i)! : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos (m i))
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hProd).mp hRatio)
    (Real.exp_nonneg (-4096 * (∑ i ∈ S, m i : ℕ)))
  have hCancel : Real.exp (4096 * (∑ i ∈ S, m i : ℕ)) *
      Real.exp (-4096 * (∑ i ∈ S, m i : ℕ)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    _ ≤ (Real.exp (4096 * (∑ i ∈ S, m i : ℕ)) *
        (∏ i ∈ S, ((m i)! : ℝ))) * Real.exp (-4096 * (∑ i ∈ S, m i : ℕ)) := h
    _ = _ := by rw [mul_right_comm, hCancel, one_mul]

end CircularLaw
