import CircularLaw.GaussianAntiClusteringTheorem
import CircularLaw.StructuralKernelTheorem
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The actual least-coordinate enlargement of retained row spans

At each stage the least index with nonzero orthogonal projected coordinate
is selected, its projection is normalized, and its line is adjoined. The
iteration contains the original subspace and has exactly the prescribed
dimension. On the finite row-slice sample space its Gaussian normal is
jointly measurable, including rank-deficient row spans. The structural
alternatives pass to the enlargement by orthogonal-complement inclusion.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped BigOperators InnerProductSpace Topology

namespace CircularLaw

def enlargementEligibleCoordinates {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Fᗮ.starProjection (EuclideanSpace.single j 1) ≠ 0)

theorem enlargementEligibleCoordinates_nonempty {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hF : Module.finrank ℂ F < n) :
    (enlargementEligibleCoordinates F).Nonempty := by
  by_contra hEmpty
  have hCoordinates : ∀ j : Fin n, EuclideanSpace.single j 1 ∈ F := by
    intro j
    have hZero : Fᗮ.starProjection (EuclideanSpace.single j 1) = 0 := by
      by_contra hNonzero
      exact hEmpty ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hNonzero⟩⟩
    have hMem := (Submodule.starProjection_apply_eq_zero_iff (K := Fᗮ)).mp hZero
    simpa only [Submodule.orthogonal_orthogonal] using hMem
  have hSpan : Submodule.span ℂ (Set.range (EuclideanSpace.basisFun (Fin n) ℂ)) ≤ F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    simpa only [EuclideanSpace.basisFun_apply] using hCoordinates j
  have hTop : F = ⊤ := by
    apply top_unique
    have hBasisSpan := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq
    rw [OrthonormalBasis.coe_toBasis] at hBasisSpan
    rw [hBasisSpan] at hSpan
    exact hSpan
  have hRank : Module.finrank ℂ F = n := by
    rw [hTop, finrank_top]
    simp
  omega

def enlargementNextIndex {n : ℕ} (F : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (h : (enlargementEligibleCoordinates F).Nonempty) : Fin n :=
  (enlargementEligibleCoordinates F).min' h

theorem enlargementNextIndex_eligible {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (h : (enlargementEligibleCoordinates F).Nonempty) :
    Fᗮ.starProjection (EuclideanSpace.single (enlargementNextIndex F h) 1) ≠ 0 :=
  (Finset.mem_filter.mp (Finset.min'_mem _ h)).2

theorem enlargementNextIndex_le {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (h : (enlargementEligibleCoordinates F).Nonempty) (j : Fin n)
    (hj : Fᗮ.starProjection (EuclideanSpace.single j 1) ≠ 0) :
    enlargementNextIndex F h ≤ j :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

def enlargementUnitVector {n : ℕ} (F : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (h : (enlargementEligibleCoordinates F).Nonempty) : EuclideanSpace ℂ (Fin n) :=
  let v := Fᗮ.starProjection (EuclideanSpace.single (enlargementNextIndex F h) 1)
  (‖v‖⁻¹ : ℂ) • v

theorem enlargementUnitVector_norm {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (h : (enlargementEligibleCoordinates F).Nonempty) : ‖enlargementUnitVector F h‖ = 1 :=
  norm_smul_inv_norm (enlargementNextIndex_eligible F h)

theorem enlargementUnitVector_mem_orthogonal {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (h : (enlargementEligibleCoordinates F).Nonempty) : enlargementUnitVector F h ∈ Fᗮ :=
  Fᗮ.smul_mem _ (Fᗮ.starProjection_apply_mem _)

def coordinateEnlargementStep {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  if h : (enlargementEligibleCoordinates F).Nonempty then F ⊔ ℂ ∙ enlargementUnitVector F h else F

theorem le_coordinateEnlargementStep {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : F ≤ coordinateEnlargementStep F := by
  unfold coordinateEnlargementStep
  split_ifs
  · exact le_sup_left
  · exact le_rfl

theorem coordinateEnlargementStep_finrank {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hF : Module.finrank ℂ F < n) :
    Module.finrank ℂ (coordinateEnlargementStep F) = Module.finrank ℂ F + 1 := by
  have h := enlargementEligibleCoordinates_nonempty F hF
  rw [coordinateEnlargementStep, dif_pos h]
  have hv : enlargementUnitVector F h ≠ 0 := by
    intro hv
    have hNorm := enlargementUnitVector_norm F h
    rw [hv, norm_zero] at hNorm
    norm_num at hNorm
  have hSpan : ℂ ∙ enlargementUnitVector F h ≤ Fᗮ := by
    apply Submodule.span_le.mpr
    intro v hv
    have hEq : v = enlargementUnitVector F h := Set.mem_singleton_iff.mp hv
    rw [hEq]
    exact enlargementUnitVector_mem_orthogonal F h
  have hDisjoint : Disjoint F (ℂ ∙ enlargementUnitVector F h) :=
    (Submodule.orthogonal_disjoint F).mono_right hSpan
  have hAdd := Submodule.finrank_sup_add_finrank_inf_eq F (ℂ ∙ enlargementUnitVector F h)
  rw [hDisjoint.eq_bot, finrank_bot, add_zero, finrank_span_singleton hv] at hAdd
  exact hAdd

def coordinateEnlargementStages {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin n))
  | 0 => F
  | k + 1 => coordinateEnlargementStep (coordinateEnlargementStages F k)

theorem le_coordinateEnlargementStages {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (k : ℕ) : F ≤ coordinateEnlargementStages F k := by
  induction k with
  | zero => exact le_rfl
  | succ k hk => exact hk.trans (le_coordinateEnlargementStep _)

theorem coordinateEnlargementStages_finrank {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (k : ℕ)
    (hk : Module.finrank ℂ F + k ≤ n) :
    Module.finrank ℂ (coordinateEnlargementStages F k) = Module.finrank ℂ F + k := by
  induction k with
  | zero => simp only [coordinateEnlargementStages, add_zero]
  | succ k ih =>
    have hPrev := ih (by omega)
    change Module.finrank ℂ (coordinateEnlargementStep (coordinateEnlargementStages F k)) = _
    rw [coordinateEnlargementStep_finrank _ (by omega), hPrev]
    omega

def coordinateEnlargement {n : ℕ} (F : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (r : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  coordinateEnlargementStages F (r - Module.finrank ℂ F)

theorem le_coordinateEnlargement {n : ℕ} (F : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (r : ℕ) : F ≤ coordinateEnlargement F r := le_coordinateEnlargementStages F _

theorem coordinateEnlargement_finrank {n r : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hF : Module.finrank ℂ F ≤ r) (hr : r ≤ n) :
    Module.finrank ℂ (coordinateEnlargement F r) = r := by
  unfold coordinateEnlargement
  rw [coordinateEnlargementStages_finrank F _ (by omega)]
  omega

theorem coordinateEnlargement_eq_self {n : ℕ}
    (F : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    coordinateEnlargement F (Module.finrank ℂ F) = F := by
  simp only [coordinateEnlargement, Nat.sub_self, coordinateEnlargementStages]

theorem fixedSubspaceStructural_mono {n L q : ℕ}
    {F E : Submodule ℂ (EuclideanSpace ℂ (Fin n))} (hFE : F ≤ E)
    (h : FixedSubspaceStructural F L q) : FixedSubspaceStructural E L q :=
  fun v hv hOrth => h v hv (Submodule.orthogonal_le hFE hOrth)

theorem fixedSubspaceStructural_rowSpan_iff {n d L : ℕ} (a : ℝ)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) :
    FixedSubspaceStructural (retainedRowSpan I ζ rows) L (sourceNormalRank a L) ↔
      SourceStructuralRowSpan L a I ζ rows := by
  constructor
  · intro h v hv hOrth
    have hNonzero : (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n)) ≠ 0 := by simpa using hv
    simpa only [PiLp.toLp_apply, mul_comm] using h (WithLp.toLp 2 v) hNonzero hOrth
  · intro h v hv hOrth
    have hNonzero : (fun j => v j) ≠ 0 := by
      intro hZero
      apply hv
      ext j
      exact congrFun hZero j
    simpa only [mul_comm] using h (fun j => v j) hNonzero hOrth

theorem retainedRowSpan_finrank_le {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) : Module.finrank ℂ (retainedRowSpan I ζ rows) ≤ I.card := by
  simpa only [retainedRowSpan, Set.finrank, Fintype.card_coe] using
    (finrank_range_le_card (R := ℂ) (retainedConjugateRow I ζ rows))

def enlargedRetainedRowSpan {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  coordinateEnlargement (retainedRowSpan I ζ rows) I.card

theorem retainedRowSpan_le_enlarged {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) : retainedRowSpan I ζ rows ≤ enlargedRetainedRowSpan I ζ rows :=
  le_coordinateEnlargement _ _

theorem enlargedRetainedRowSpan_finrank {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) : Module.finrank ℂ (enlargedRetainedRowSpan I ζ rows) = I.card :=
  coordinateEnlargement_finrank _ (retainedRowSpan_finrank_le I ζ rows)
    (by simpa only [Fintype.card_fin] using Finset.card_le_univ I)

theorem enlargedRetainedRowSpan_structural {n d L : ℕ} (a : ℝ)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (h : SourceStructuralRowSpan L a I ζ rows) :
    FixedSubspaceStructural (enlargedRetainedRowSpan I ζ rows) L (sourceNormalRank a L) :=
  fixedSubspaceStructural_mono (retainedRowSpan_le_enlarged I ζ rows)
    ((fixedSubspaceStructural_rowSpan_iff a I ζ rows).mpr h)

theorem enlargedRetainedRowSpan_depends_on_retained_rows {n d : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows rows' : RowSliceMatrix n d)
    (hRows : ∀ i ∈ I, rows i = rows' i) :
    enlargedRetainedRowSpan I ζ rows = enlargedRetainedRowSpan I ζ rows' := by
  have hGenerators : retainedConjugateRow I ζ rows = retainedConjugateRow I ζ rows' := by
    funext i
    unfold retainedConjugateRow
    congr 1
    funext j
    simp only [retainedShiftedMatrix, hRows i.val i.property]
  unfold enlargedRetainedRowSpan retainedRowSpan
  rw [hGenerators]

theorem enlargedRetainedRowSpan_measurable {n d : ℕ}
    [MeasurableSpace (Submodule ℂ (EuclideanSpace ℂ (Fin n)))]
    (I : Finset (Fin n)) (ζ : ℂ) : Measurable (enlargedRetainedRowSpan (d := d) I ζ) :=
  measurable_of_finite _

theorem enlargedRetainedGaussian_measurable {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ) :
    Measurable (fun p : RowSliceMatrix n d × (Fin n → ℂ) =>
      projectedComplexGaussian (enlargedRetainedRowSpan I ζ p.1) p.2) :=
  measurable_from_prod_countable_right (fun rows =>
    (projectedComplexGaussian_continuous (enlargedRetainedRowSpan I ζ rows)).measurable)

theorem projectedEnlargedRetainedGaussian_mem_kernel {n d : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) (z : Fin n → ℂ) :
    (retainedShiftedMatrix I ζ rows).mulVec
      (fun j => projectedComplexGaussian (enlargedRetainedRowSpan I ζ rows) z j) = 0 := by
  apply (retainedRowSpan_orthogonal_iff_kernel I ζ rows _).mp
  exact Submodule.orthogonal_le (retainedRowSpan_le_enlarged I ζ rows)
    (projectedComplexGaussian_mem_orthogonal _ _)

theorem orthogonalProjection_norm_mono {n : ℕ}
    {F E : Submodule ℂ (EuclideanSpace ℂ (Fin n))} (hFE : F ≤ E)
    (v : EuclideanSpace ℂ (Fin n)) : ‖Eᗮ.starProjection v‖ ≤ ‖Fᗮ.starProjection v‖ := by
  have hComp := Submodule.starProjection_comp_starProjection_of_le (Submodule.orthogonal_le hFE)
  have hEq : Eᗮ.starProjection (Fᗮ.starProjection v) = Eᗮ.starProjection v :=
    congrArg (fun f : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) => f v) hComp
  rw [← hEq]
  exact Submodule.norm_starProjection_apply_le Eᗮ _

theorem row_slice_structural_theorem_with_normal_rank :
    ∃ Cstar : ℝ, 0 < Cstar ∧
      ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ C : ℝ, Cstar ≤ C →
        ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
            ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
              ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
                1 - 5 / (n : ℝ) ≤
                  uniformProbability (SourceStructuralRowSpan (d := d) L a I ζ) := by
  obtain ⟨aLoad, haLoad, _, hEntropy⟩ := source_row_load_small_constant
  let a₃ : ℝ := min aLoad (min (1 / 65536) (equalBlockRateConstant (1 / 4) / 33600))
  have ha₃ : 0 < a₃ := lt_min haLoad (lt_min (by norm_num)
    (div_pos (equalBlockRateConstant_pos (by norm_num)) (by norm_num)))
  have haLoadBound : a₃ ≤ aLoad := min_le_left _ _
  have haSmall : a₃ ≤ 1 / 65536 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have haRate : a₃ ≤ equalBlockRateConstant (1 / 4) / 33600 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have haNet : 7 * a₃ ≤ equalBlockRateConstant (1 / 4) / 4800 := by linarith only [haRate]
  let Cstar : ℝ := max sourceKernelLowerConstant 96
  have hCstar : 0 < Cstar := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 96) (le_max_right _ _)
  refine ⟨Cstar, hCstar, ?_⟩
  intro a ha haOne C hC σ Z₀ _ hσ
  have hKernel : sourceKernelLowerConstant ≤ C := (le_max_left _ _).trans hC
  have hNorm : 96 ≤ C := (le_max_right _ _).trans hC
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_source_structural_kernel_good_uniform hKernel hNorm ha₃ haSmall
      (hEntropy a₃ ha₃ haLoadBound) haNet ha haOne hσ.le Z₀)
  refine ⟨N, ?_⟩
  intro n hn d hBand L hL I hI ζ hShift
  apply (hN n hn d hBand L hL I hI ζ hShift).trans
  exact uniformProbability_mono (fun rows hGood =>
    (sourceStructuralRowSpan_iff_kernel L a I ζ rows).mpr hGood)

end CircularLaw
