import CircularLaw.RowSlice

/-!
# Exact-slice incidence counting

This formalizes the combinatorial step of `lem:slice-double-count` in
`sections/06_normals.tex`. The correspondence is `(S,t) ↔ (S.erase t,t)`.
The concentration estimate for the exceptional low-occupancy event is
proved separately in `CircularLaw.Hypergeometric`.
-/

open scoped BigOperators

namespace CircularLaw

/-- Count each admissible slice once for each selected coordinate in `K`.
Deleting the selected coordinate gives the equivalent extension count. -/
theorem slice_incidence_identity {n d : ℕ} (A : Finset (Finset (Fin n)))
    (K : Finset (Fin n)) (hA : ∀ S ∈ A, S.card = d) :
    (∑ S ∈ A, (S ∩ K).card) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (d - 1),
        (K.filter fun t => t ∉ T ∧ insert t T ∈ A).card := by
  classical
  let left := A.sigma fun S => S ∩ K
  let right := ((Finset.univ : Finset (Fin n)).powersetCard (d - 1)).sigma
    fun T => K.filter fun t => t ∉ T ∧ insert t T ∈ A
  have hcard : left.card = right.card := by
    refine Finset.card_bij' (fun p _ => ⟨p.1.erase p.2, p.2⟩)
      (fun p _ => ⟨insert p.2 p.1, p.2⟩) ?_ ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_sigma.mp hp with ⟨hS, ht⟩
      rcases Finset.mem_inter.mp ht with ⟨htS, htK⟩
      apply Finset.mem_sigma.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        exact ⟨Finset.subset_univ _, by rw [Finset.card_erase_of_mem htS, hA _ hS]⟩
      · apply Finset.mem_filter.mpr
        exact ⟨htK, Finset.notMem_erase _ _, by simpa [Finset.insert_erase htS] using hS⟩
    · intro p hp
      rcases Finset.mem_sigma.mp hp with ⟨_, ht⟩
      rcases Finset.mem_filter.mp ht with ⟨htK, _, hS⟩
      exact Finset.mem_sigma.mpr ⟨hS, Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, htK⟩⟩
    · intro p hp
      rcases Finset.mem_sigma.mp hp with ⟨_, ht⟩
      have htS := (Finset.mem_inter.mp ht).1
      simp [Finset.insert_erase htS]
    · intro p hp
      rcases Finset.mem_sigma.mp hp with ⟨_, ht⟩
      have htT := (Finset.mem_filter.mp ht).2.1
      simp [Finset.erase_insert htT]
  simpa only [left, right, Finset.card_sigma] using hcard

/-- A bound on every extension fiber controls the total incidence count. -/
theorem slice_incidence_bound {n d m : ℕ} (A : Finset (Finset (Fin n)))
    (K : Finset (Fin n)) (hA : ∀ S ∈ A, S.card = d)
    (hfiber : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (d - 1),
      (K.filter fun t => t ∉ T ∧ insert t T ∈ A).card ≤ m) :
    (∑ S ∈ A, (S ∩ K).card) ≤ m * n.choose (d - 1) := by
  rw [slice_incidence_identity A K hA]
  calc
    _ ≤ ∑ _T ∈ (Finset.univ : Finset (Fin n)).powersetCard (d - 1), m :=
      Finset.sum_le_sum hfiber
    _ = m * n.choose (d - 1) := by
      simp [Finset.card_powersetCard, Nat.mul_comm]

/-- If each slice has at least `h` selected coordinates in `K`, the number
of slices is bounded by the extension count divided by that occupancy. -/
theorem slice_card_mul_le {n d m h : ℕ} (A : Finset (Finset (Fin n)))
    (K : Finset (Fin n)) (hA : ∀ S ∈ A, S.card = d)
    (hoccupancy : ∀ S ∈ A, h ≤ (S ∩ K).card)
    (hfiber : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (d - 1),
      (K.filter fun t => t ∉ T ∧ insert t T ∈ A).card ≤ m) :
    h * A.card ≤ m * n.choose (d - 1) := by
  calc
    h * A.card = ∑ _S ∈ A, h := by simp [Nat.mul_comm]
    _ ≤ ∑ S ∈ A, (S ∩ K).card := Finset.sum_le_sum hoccupancy
    _ ≤ m * n.choose (d - 1) := slice_incidence_bound A K hA hfiber

/-- Coordinate anti-clustering bounds every extension fiber of a small-ball
family. The center depends on the retained support `T`. -/
theorem small_ball_fiber_bound {n d m : ℕ} (K : Finset (Fin n))
    (y : Fin n → ℂ) (ρ : ℝ)
    (hcluster : ∀ c : ℂ, (K.filter fun t => ‖y t - c‖ ≤ ρ).card ≤ m)
    (center : ℂ) (T : Finset (Fin n)) :
    (K.filter fun t => t ∉ T ∧
      insert t T ∈ ((Finset.univ : Finset (Fin n)).powersetCard d).filter
        (fun S => ‖(∑ j ∈ S, y j) - center‖ ≤ ρ)).card ≤ m := by
  classical
  apply le_trans (Finset.card_le_card ?_) (hcluster (center - ∑ j ∈ T, y j))
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨htK, htT, hsmall⟩
  have hnorm := (Finset.mem_filter.mp hsmall).2
  rw [Finset.sum_insert htT] at hnorm
  apply Finset.mem_filter.mpr
  refine ⟨htK, ?_⟩
  convert hnorm using 2
  ring

/-- The real-valued occupancy version permits the exact threshold `d/4`. -/
theorem slice_card_mul_le_real {n d m : ℕ} (h : ℝ) (A : Finset (Finset (Fin n)))
    (K : Finset (Fin n)) (hA : ∀ S ∈ A, S.card = d)
    (hoccupancy : ∀ S ∈ A, h ≤ ((S ∩ K).card : ℝ))
    (hfiber : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (d - 1),
      (K.filter fun t => t ∉ T ∧ insert t T ∈ A).card ≤ m) :
    h * A.card ≤ (m : ℝ) * n.choose (d - 1) := by
  calc
    h * A.card = ∑ _S ∈ A, h := by simp [mul_comm]
    _ ≤ ∑ S ∈ A, ((S ∩ K).card : ℝ) := Finset.sum_le_sum hoccupancy
    _ ≤ (m : ℝ) * n.choose (d - 1) := by
      exact_mod_cast slice_incidence_bound A K hA hfiber

/-- Adjacent slice sizes give the binomial ratio used in the manuscript. -/
theorem adjacent_choose_ratio {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    (n.choose (d - 1) : ℝ) / n.choose d = (d : ℝ) / (n - d + 1 : ℕ) := by
  have hchoose := Nat.choose_succ_right_eq n (d - 1)
  have hpred : d - 1 + 1 = d := by omega
  have hsub : n - (d - 1) = n - d + 1 := by omega
  rw [hpred, hsub] at hchoose
  have hchoose' : (n.choose d : ℝ) * d =
      (n.choose (d - 1) : ℝ) * (n - d + 1 : ℕ) := by exact_mod_cast hchoose
  have hden : (n.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdn).ne'
  have hdim : ((n - d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  apply (div_eq_div_iff hden hdim).mpr
  nlinarith [hchoose']

/-- The small-ball family of exact supports. -/
noncomputable def smallBallFamily (n d : ℕ) (y : Fin n → ℂ) (center : ℂ) (ρ : ℝ) :
    Finset (Finset (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).powersetCard d).filter
    fun S => ‖(∑ j ∈ S, y j) - center‖ ≤ ρ

/-- The complete double-counting probability bound, with the low-occupancy
probability left explicit. `slice_small_ball_exponential` combines this
bound with the proved hypergeometric lower tail. -/
theorem small_ball_probability_le_occupancy_tail {n d m : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) (K : Finset (Fin n))
    (y : Fin n → ℂ) (center : ℂ) (ρ : ℝ)
    (hcluster : ∀ c : ℂ, (K.filter fun t => ‖y t - c‖ ≤ ρ).card ≤ m) :
    ((smallBallFamily n d y center ρ).card : ℝ) / n.choose d ≤
      4 * (m : ℝ) / (n - d + 1 : ℕ) +
        ((((Finset.univ : Finset (Fin n)).powersetCard d).filter
          fun S => ((S ∩ K).card : ℝ) < (d : ℝ) / 4).card : ℝ) / n.choose d := by
  classical
  let A := smallBallFamily n d y center ρ
  let good := A.filter fun S => (d : ℝ) / 4 ≤ ((S ∩ K).card : ℝ)
  let bad := ((Finset.univ : Finset (Fin n)).powersetCard d).filter
    fun S => ((S ∩ K).card : ℝ) < (d : ℝ) / 4
  have hA : ∀ S ∈ A, S.card = d := by
    intro S hS
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
  have hgood : ∀ S ∈ good, S.card = d :=
    fun S hS => hA S (Finset.mem_filter.mp hS).1
  have hoccupancy : ∀ S ∈ good, (d : ℝ) / 4 ≤ ((S ∩ K).card : ℝ) :=
    fun _ hS => (Finset.mem_filter.mp hS).2
  have hfiber : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (d - 1),
      (K.filter fun t => t ∉ T ∧ insert t T ∈ good).card ≤ m := by
    intro T _
    apply le_trans (Finset.card_le_card ?_)
      (small_ball_fiber_bound (d := d) K y ρ hcluster center T)
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨htK, htT, hS⟩
    exact Finset.mem_filter.mpr ⟨htK, htT, (Finset.mem_filter.mp hS).1⟩
  have hinc := slice_card_mul_le_real ((d : ℝ) / 4) good K hgood hoccupancy hfiber
  have hbad : (A.filter fun S => ¬((d : ℝ) / 4 ≤ ((S ∩ K).card : ℝ))).card ≤ bad.card := by
    apply Finset.card_le_card
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSA, hSbad⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hSA).1, lt_of_not_ge hSbad⟩
  have hsplit : A.card ≤ good.card + bad.card := by
    have := Finset.card_filter_add_card_filter_not (s := A)
      (fun S => (d : ℝ) / 4 ≤ ((S ∩ K).card : ℝ))
    dsimp [good]
    omega
  have htotal : (0 : ℝ) < n.choose d := by exact_mod_cast Nat.choose_pos hdn
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdim : (0 : ℝ) < (n - d + 1 : ℕ) := by positivity
  have hratio := adjacent_choose_ratio hd hdn
  have hgoodbound : (good.card : ℝ) / n.choose d ≤ 4 * (m : ℝ) / (n - d + 1 : ℕ) := by
    have hbound : (good.card : ℝ) ≤ (4 * (m : ℝ) * n.choose (d - 1)) / d := by
      apply (le_div_iff₀ hdreal).mpr
      nlinarith [hinc]
    calc
      _ ≤ ((4 * (m : ℝ) * n.choose (d - 1)) / d) / n.choose d :=
        div_le_div_of_nonneg_right hbound htotal.le
      _ = (4 * (m : ℝ) / d) * ((n.choose (d - 1) : ℝ) / n.choose d) := by ring
      _ = 4 * (m : ℝ) / (n - d + 1 : ℕ) := by
        rw [hratio]
        field_simp
  change (A.card : ℝ) / n.choose d ≤ _ + (bad.card : ℝ) / n.choose d
  calc
    _ ≤ ((good.card : ℝ) + bad.card) / n.choose d := by
      apply div_le_div_of_nonneg_right _ htotal.le
      exact_mod_cast hsplit
    _ = (good.card : ℝ) / n.choose d + (bad.card : ℝ) / n.choose d := add_div _ _ _
    _ ≤ _ := add_le_add hgoodbound le_rfl

end CircularLaw
