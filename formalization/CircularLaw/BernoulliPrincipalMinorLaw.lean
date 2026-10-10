import CircularLaw.ParameterBernoulliWordMeans
import CircularLaw.RoundedMinorLogReview

/-!
# The actual law and normalization of a Bernoulli principal minor

Restricting independent coordinates retains exactly the ambient entry
probability. The source minor retains the ambient square-root-degree
normalization, while its own effective degree is m*p.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem bernoulli_cube_law_restrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0) (hp : p ≤ 1) (f : ι ↪ κ) :
    (bernoulliCubeLaw κ p hp).map (fun x i => x (f i)) = bernoulliCubeLaw ι p hp := by
  have hInd : iIndepFun (fun i : ι => fun x : κ → Bool => x (f i))
      (bernoulliCubeLaw κ p hp) :=
    iIndepFun.precomp f.injective (iIndepFun_pi (fun _ => measurable_id.aemeasurable))
  rw [(iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (f i)).aemeasurable)).mp hInd]
  unfold bernoulliCubeLaw
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : κ => bernoulliCoordinateLaw p hp) (f i)).map_eq

def bernoulliPrincipalMinorSample {m n : ℕ} (hmn : m ≤ n)
    (x : BernoulliSquareSample n) : BernoulliSquareSample m :=
  fun ij => x (Fin.castLE hmn ij.1, Fin.castLE hmn ij.2)

theorem bernoulli_principal_minor_sample_law {m n : ℕ} (hmn : m ≤ n)
    (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliSquareMatrixLaw n p hp).map (bernoulliPrincipalMinorSample hmn) =
      bernoulliSquareMatrixLaw m p hp := by
  let f : (Fin m × Fin m) ↪ (Fin n × Fin n) :=
    ⟨fun ij => (Fin.castLE hmn ij.1, Fin.castLE hmn ij.2), by
      intro a b h
      exact Prod.ext ((Fin.castLE_injective hmn) (congrArg Prod.fst h))
        ((Fin.castLE_injective hmn) (congrArg Prod.snd h))⟩
  exact bernoulli_cube_law_restrict p hp f

theorem bernoulli_sparse_principal_minor_sample_law {m n d : ℕ} (hmn : m ≤ n) :
    (sparseBernoulliMatrixLaw n d).map (bernoulliPrincipalMinorSample hmn) =
      bernoulliSquareMatrixLaw m (min (rowBernoulliParameter n d) 1) (min_le_right _ _) :=
  bernoulli_principal_minor_sample_law hmn _ _

theorem bernoulli_principal_minor_matrix_eq {m n : ℕ} (hmn : m ≤ n)
    (x : BernoulliSquareSample n) :
    squarePrincipalMinor (bernoulliSquareMatrix x) hmn =
      bernoulliSquareMatrix (bernoulliPrincipalMinorSample hmn x) := rfl

theorem bernoulli_shifted_principal_minor_matrix_eq {m n : ℕ} (hmn : m ≤ n)
    (d : ℕ) (z : ℂ) (x : BernoulliSquareSample n) :
    squarePrincipalMinor (normalizedShiftedBernoulliMatrix d z x) hmn =
      (Real.sqrt (d : ℝ) : ℂ)⁻¹ • bernoulliSquareMatrix (bernoulliPrincipalMinorSample hmn x) -
        z • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  ext i j
  simp only [squarePrincipalMinor, normalizedShiftedBernoulliMatrix, Matrix.submatrix_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    (Fin.castLE_injective hmn).eq_iff, bernoulliPrincipalMinorSample, bernoulliSquareMatrix]

theorem bernoulli_principal_minor_effective_degree {m n d : ℕ} :
    bernoulliEffectiveDegree m (rowBernoulliParameter n d) = (m : ℝ) / n * d := by
  rw [bernoulliEffectiveDegree, rowBernoulliParameter_coe]
  ring

theorem bernoulli_minor_effective_degree_tendsto (q d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) {theta : ℝ} (hTheta : 0 < theta)
    (hRatio : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 theta)) :
    Tendsto (fun n => bernoulliEffectiveDegree (q n) (rowBernoulliParameter n (d n)))
      atTop atTop := by
  have h := hRatio.pos_mul_atTop hTheta (tendsto_natCast_atTop_atTop.comp hDegree)
  simpa only [bernoulli_principal_minor_effective_degree] using h

end CircularLaw
