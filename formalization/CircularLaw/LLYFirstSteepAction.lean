import CircularLaw.LLYFirstSteepGeometry
import CircularLaw.UniqueWitnessFailure
import CircularLaw.UniqueWitnessAction
import CircularLaw.LLYGradualAdjoint

/-!
# Quantitative first-steep action on the actual retained matrix

A six-degree jump permits every spectral shift of modulus at most the
degree. All eligible unique witnesses contribute to the Euclidean norm,
so this is a simultaneous vector estimate on the uniform witness event.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem unique_witness_action_half_six_degree {n d : ℕ} (S : RowSlice n d)
    (J : Finset (Fin n)) (j i : Fin n) (hUnique : S.val ∩ J = {j}) (hiJ : i ∉ J)
    (x : Fin n → ℂ) (ζ : ℂ) {a b : ℝ} (hb : 0 ≤ b)
    (hTail : ∀ k : Fin n, k ∉ J → ‖x k‖ ≤ b) (hTop : a ≤ ‖x j‖)
    (hJump : 6 * (d : ℝ) * b < a) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) :
    a / 2 ≤ ‖shiftedRowAction S x 0 ζ i‖ := by
  have hLower := unique_witness_action_lower S J j i hUnique hiJ x 0 ζ hTail
  simp only [norm_zero, mul_zero, add_zero] at hLower
  have hCost : ((d : ℝ) - 1 + ‖ζ‖) * b ≤ 2 * d * b := by
    have h := mul_le_mul_of_nonneg_right hSpectral hb
    nlinarith
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_nonneg hdR hb]

theorem lly_unique_witness_jump_norm {n d s t : ℕ} (hd : 0 < d)
    (hs : 0 < s) (hst : s ≤ t) (htn : t ≤ n) (I : Finset (Fin n))
    (rows : RowSliceMatrix n d) (hWitness : UniformUniqueWitness I s t rows)
    (x : EuclideanSpace ℂ (Fin n)) (ζ : ℂ)
    (hJump : 6 * (d : ℝ) * orderedNormAt (fun j => x j) t <
      orderedNormAt (fun j => x j) s) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) :
    Real.sqrt d / 4 * orderedNormAt (fun j => x j) s ≤
      ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin x‖ := by
  let L := orderedPrefix (fun j => x j) s
  let J := orderedPrefix (fun j => x j) t
  let R := J \ L
  have hSub : L ⊆ J := orderedPrefix_subset _ hst
  have hUnion : L ∪ R = J := Finset.union_sdiff_of_subset hSub
  have hCount := hWitness L R Finset.disjoint_sdiff
    (orderedPrefix_card _ (by omega : s ≤ n)) (by rw [hUnion]; exact orderedPrefix_card _ htn)
  rw [hUnion] at hCount
  let W := uniqueWitnessRows L J (fun i : ↥(I \ J) => rows i.val)
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
  have hLarge : ∀ i ∈ G, T / 2 ≤ ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin x i‖ := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨j, hjL, hUnique⟩ := (Finset.mem_filter.mp hq).2
    have hAction := unique_witness_action_half_six_degree (rows q.val) J j q.val hUnique
      (Finset.mem_sdiff.mp q.property).2 (fun j => x j) ζ (orderedNormAt_nonneg _ _)
      (fun j hj => norm_le_orderedNormAt_notMem_prefix _ (by omega : 0 < t) htn j hj)
      (orderedNormAt_le_norm_mem_prefix _ hs (by omega : s ≤ n) j hjL) hJump hSpectral
    change T / 2 ≤ ‖(retainedShiftedMatrix I ζ rows).mulVec (fun j => x j) (emb q)‖
    rw [retainedShiftedMatrix_mulVec]
    simpa only [shiftedRowAction, add_zero] using hAction
  have hEnergy := euclidean_subset_coordinates_energy_lower G
    ((retainedShiftedMatrix I ζ rows).toEuclideanLin x) (by positivity : 0 ≤ T / 2) hLarge
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

def LLYFirstWitness {n d : ℕ} (I : Finset (Fin n)) (ℓ r k : ℕ)
    (rows : RowSliceMatrix n d) : Prop :=
  ∀ i ∈ Finset.range (r + 1),
    UniformUniqueWitness I (llyFirstRank ℓ k i) (llyFirstRank ℓ k (i + 1)) rows

theorem lly_first_steep_retained_norm {n d ℓ r k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (hWitness : LLYFirstWitness I ℓ r k rows)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) (x : EuclideanSpace ℂ (Fin n))
    (hUnit : ‖x‖ = 1) (hx : (fun j => x j) ∈ llyFirstSteep d ℓ r k) :
    Real.sqrt d / (4 * llyFirstSteepNormConstant n d r) ≤
      ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin x‖ := by
  obtain ⟨i, hi, hJump, hNorm⟩ := lly_first_jump_norm_bound hn hd hk x hx
  have hB := lly_first_steep_norm_constant_pos (r := r) hn hd
  rw [hUnit] at hNorm
  have hTop : 1 / llyFirstSteepNormConstant n d r ≤
      orderedNormAt (fun j => x j) (llyFirstRank ℓ k i) :=
    (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hNorm)
  have hAction := lly_unique_witness_jump_norm hd (lly_first_rank_pos hℓ hk i)
    (lly_first_rank_mono hℓ (by omega : i ≤ i + 1))
    ((lly_first_rank_le ℓ k (i + 1)).trans hkn) I rows (hWitness i hi) x ζ hJump hSpectral
  calc
    _ = Real.sqrt d / 4 * (1 / llyFirstSteepNormConstant n d r) := by ring
    _ ≤ Real.sqrt d / 4 * orderedNormAt (fun j => x j) (llyFirstRank ℓ k i) :=
      mul_le_mul_of_nonneg_left hTop (by positivity)
    _ ≤ _ := hAction

theorem lly_first_steep_retained_kernel_exclusion {n d ℓ r k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (hWitness : LLYFirstWitness I ℓ r k rows)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) (x : EuclideanSpace ℂ (Fin n))
    (hUnit : ‖x‖ = 1) (hx : (fun j => x j) ∈ llyFirstSteep d ℓ r k) :
    (retainedShiftedMatrix I ζ rows).toEuclideanLin x ≠ 0 := by
  intro hZero
  have hLower := lly_first_steep_retained_norm hn hd hℓ hk hkn I rows hWitness ζ hSpectral x hUnit hx
  rw [hZero, norm_zero] at hLower
  have hB := lly_first_steep_norm_constant_pos (r := r) hn hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPos : 0 < Real.sqrt d / (4 * llyFirstSteepNormConstant n d r) := by positivity
  linarith

end CircularLaw
