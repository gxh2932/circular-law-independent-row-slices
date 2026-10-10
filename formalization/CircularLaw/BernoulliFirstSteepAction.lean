import CircularLaw.BernoulliFirstWitnessProbability
import CircularLaw.BernoulliRowDegreeUpper
import CircularLaw.BernoulliLLYRowAction

/-!
# First-steep action on the actual retained Bernoulli matrix

A unique coordinate and the actual support-cardinality bound 2d suffice
for the same six-degree jump. All witnesses contribute simultaneously.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem bernoulli_unique_witness_action_half_six_degree {n d : ℕ}
    (sample : BernoulliSquareSample n) (hDegree : BernoulliRowDegreeUpperBound (2 * (d : ℝ)) sample)
    (J : Finset (Fin n)) (j i : Fin n)
    (hUnique : bernoulliSupport (fun k => sample (i, k)) ∩ J = {j}) (hiJ : i ∉ J)
    (x : EuclideanSpace ℂ (Fin n)) (ζ : ℂ) {a b : ℝ} (hb : 0 ≤ b)
    (hTail : ∀ k : Fin n, k ∉ J → ‖x k‖ ≤ b) (hTop : a ≤ ‖x j‖)
    (hJump : 6 * (d : ℝ) * b < a) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) :
    a / 2 ≤ ‖(fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x i‖ := by
  let S := bernoulliSupport (fun k => sample (i, k))
  have hCard : (S.card : ℝ) ≤ 2 * (d : ℝ) := by
    have h := hDegree i
    rw [← bernoulli_row_load_eq_subset_count, bernoulliRowLoad, Finset.inter_univ] at h
    exact h
  have hLower := unique_witness_action_lower (⟨S, rfl⟩ : RowSlice n S.card)
    J j i hUnique hiJ (fun k => x k) 0 ζ hTail
  simp only [norm_zero, mul_zero, add_zero] at hLower
  have hCost : ((S.card : ℝ) - 1 + ‖ζ‖) * b ≤ 3 * d * b := by
    have h := mul_le_mul_of_nonneg_right hSpectral hb
    have h' := mul_le_mul_of_nonneg_right hCard hb
    nlinarith
  have hAction : shiftedRowAction (⟨S, rfl⟩ : RowSlice n S.card) (fun k => x k) 0 ζ i =
      (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x i := by
    rw [shifted_bernoulli_apply_eq_support_sum, shiftedRowAction, rowLinearForm_eq_support_sum]
    simp only [add_zero]
    rfl
  rw [hAction] at hLower
  nlinarith

theorem bernoulli_lly_unique_witness_jump_norm {n d s t : ℕ} (hd : 0 < d)
    (hs : 0 < s) (hst : s ≤ t) (htn : t ≤ n) (I : Finset (Fin n))
    (sample : BernoulliSquareSample n)
    (hDegree : BernoulliRowDegreeUpperBound (2 * (d : ℝ)) sample)
    (hWitness : BernoulliUniformUniqueWitness d I s t sample)
    (x : EuclideanSpace ℂ (Fin n)) (ζ : ℂ)
    (hJump : 6 * (d : ℝ) * orderedNormAt (fun j => x j) t <
      orderedNormAt (fun j => x j) s) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) :
    Real.sqrt d / 4 * orderedNormAt (fun j => x j) s ≤
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ := by
  let L := orderedPrefix (fun j => x j) s
  let J := orderedPrefix (fun j => x j) t
  let R := J \ L
  have hSub : L ⊆ J := orderedPrefix_subset _ hst
  have hUnion : L ∪ R = J := Finset.union_sdiff_of_subset hSub
  have hCount := hWitness L R Finset.disjoint_sdiff
    (orderedPrefix_card _ (by omega : s ≤ n)) (by rw [hUnion]; exact orderedPrefix_card _ htn)
  rw [hUnion, bernoulli_retained_event_count_eq_coordinates] at hCount
  let W : Finset ↥(I \ J) := Finset.univ.filter
    (fun i => bernoulliUniqueRowWitness L J (fun k => sample (i.val, k)))
  let emb : ↥(I \ J) ↪ I :=
    ⟨fun i => ⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩,
      by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun q : I => q.val) h⟩
  let G := W.map emb
  have hCard : (d : ℝ) * s / 2 ≤ G.card := by
    rw [Finset.card_map]
    exact hCount
  let T := orderedNormAt (fun j => x j) s
  have hT : 0 ≤ T := orderedNormAt_nonneg _ _
  have hLarge : ∀ i ∈ G, T / 2 ≤ ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x i‖ := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨j, hjL, hSingle⟩ := (Finset.mem_filter.mp hq).2
    have hUnique := (bernoulli_row_single_iff_support_inter J j (hSub hjL)
      (fun k => sample (q.val, k))).mp hSingle
    have hAction := bernoulli_unique_witness_action_half_six_degree sample hDegree J j q.val hUnique
      (Finset.mem_sdiff.mp q.property).2 x ζ (orderedNormAt_nonneg _ _)
      (fun j hj => norm_le_orderedNormAt_notMem_prefix _ (by omega : 0 < t) htn j hj)
      (orderedNormAt_le_norm_mem_prefix _ hs (by omega : s ≤ n) j hjL) hJump hSpectral
    rw [retained_shifted_bernoulli_apply_eq_full]
    exact hAction
  have hEnergy := euclidean_subset_coordinates_energy_lower G
    ((retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x) (by positivity : 0 ≤ T / 2) hLarge
  have hCountEnergy := mul_le_mul_of_nonneg_right hCard (sq_nonneg (T / 2))
  have hCoeff : (d : ℝ) / 16 ≤ (d : ℝ) * s / 8 := by
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have h := mul_le_mul_of_nonneg_left hsR (Nat.cast_nonneg (α := ℝ) d)
    nlinarith
  apply (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt d / 4 * T) (norm_nonneg _)).mp
  calc
    _ = (d : ℝ) / 16 * T ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      ring
    _ ≤ (d : ℝ) * s / 8 * T ^ 2 := mul_le_mul_of_nonneg_right hCoeff (sq_nonneg T)
    _ = ((d : ℝ) * s / 2) * (T / 2) ^ 2 := by ring
    _ ≤ _ := hCountEnergy.trans hEnergy

theorem bernoulli_lly_first_steep_retained_norm {n d ℓ r k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (sample : BernoulliSquareSample n)
    (hDegree : BernoulliRowDegreeUpperBound (2 * (d : ℝ)) sample)
    (hWitness : BernoulliLLYFirstWitness d I ℓ r k sample)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) (x : EuclideanSpace ℂ (Fin n))
    (hUnit : ‖x‖ = 1) (hx : (fun j => x j) ∈ llyFirstSteep d ℓ r k) :
    Real.sqrt d / (4 * llyFirstSteepNormConstant n d r) ≤
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ := by
  obtain ⟨i, hi, hJump, hNorm⟩ := lly_first_jump_norm_bound hn hd hk x hx
  have hB := lly_first_steep_norm_constant_pos (r := r) hn hd
  rw [hUnit] at hNorm
  have hTop : 1 / llyFirstSteepNormConstant n d r ≤
      orderedNormAt (fun j => x j) (llyFirstRank ℓ k i) :=
    (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hNorm)
  have hAction := bernoulli_lly_unique_witness_jump_norm hd (lly_first_rank_pos hℓ hk i)
    (lly_first_rank_mono hℓ (by omega : i ≤ i + 1))
    ((lly_first_rank_le ℓ k (i + 1)).trans hkn) I sample hDegree (hWitness i hi) x ζ hJump hSpectral
  calc
    _ = Real.sqrt d / 4 * (1 / llyFirstSteepNormConstant n d r) := by ring
    _ ≤ Real.sqrt d / 4 * orderedNormAt (fun j => x j) (llyFirstRank ℓ k i) :=
      mul_le_mul_of_nonneg_left hTop (by positivity)
    _ ≤ _ := hAction

theorem bernoulli_lly_first_steep_retained_kernel_exclusion {n d ℓ r k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (sample : BernoulliSquareSample n)
    (hDegree : BernoulliRowDegreeUpperBound (2 * (d : ℝ)) sample)
    (hWitness : BernoulliLLYFirstWitness d I ℓ r k sample)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) (x : EuclideanSpace ℂ (Fin n))
    (hUnit : ‖x‖ = 1) (hx : (fun j => x j) ∈ llyFirstSteep d ℓ r k) :
    (retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x ≠ 0 := by
  intro hZero
  have hLower := bernoulli_lly_first_steep_retained_norm hn hd hℓ hk hkn
    I sample hDegree hWitness ζ hSpectral x hUnit hx
  rw [hZero, norm_zero] at hLower
  have hB := lly_first_steep_norm_constant_pos (r := r) hn hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPos : 0 < Real.sqrt d / (4 * llyFirstSteepNormConstant n d r) := by positivity
  linarith

end CircularLaw
