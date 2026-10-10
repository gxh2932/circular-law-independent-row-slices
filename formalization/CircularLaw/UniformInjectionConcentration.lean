import CircularLaw.InjectionExposureMean
import CircularLaw.FiniteFiberHoeffding
import CircularLaw.Hypergeometric

/-!
# Exponential concentration for the actual uniform injection law

Exact prefix means and fibrewise Hoeffding bounds give the exposure mgf.
A uniform bound K on codomain transpositions supplies one-step bounds K,
so m exposed coordinates have sub-Gaussian parameter m*K^2. No conditional
concentration or martingale increment bound is left as an assumed input.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory

namespace CircularLaw

theorem injection_exposure_exp_step {m n k : ℕ} (hk : k < m)
    (f : (Fin m ↪ Fin n) → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hSwap : ∀ e : Fin m ↪ Fin n, ∀ a b : Fin n,
      |f e - f (e.trans (Equiv.swap a b).toEmbedding)| ≤ K) (t : ℝ) :
    finiteMean (fun e => Real.exp (t * (injectionExposureMean f (k + 1) e - finiteMean f))) ≤
      Real.exp (K ^ 2 * t ^ 2 / 2) *
        finiteMean (fun e => Real.exp (t * (injectionExposureMean f k e - finiteMean f))) := by
  let X := fun e => injectionExposureMean f (k + 1) e - injectionExposureMean f k e
  let w := fun p : Fin m → Option (Fin n) =>
    Real.exp (t * (finiteFiberMean (injectionPrefix k) f p - finiteMean f))
  have hBound (e : Fin m ↪ Fin n) : X e ∈ Set.Icc (-K) K :=
    abs_le.mp (injection_exposure_increment_swap_bound ⟨k, hk⟩ f hSwap e)
  have h := finiteMean_weighted_exp_bound (injectionPrefix k) X w hK
    (fun _ => Real.exp_nonneg _) hBound (injection_exposure_increment_fiber_mean_zero f) t
  have hFun : (fun e : Fin m ↪ Fin n => w (injectionPrefix k e) * Real.exp (t * X e)) =
      (fun e => Real.exp (t * (injectionExposureMean f (k + 1) e - finiteMean f))) := by
    funext e
    dsimp only [w, X]
    rw [← Real.exp_add]
    congr 1
    unfold injectionExposureMean
    ring
  rw [hFun] at h
  exact h

theorem injection_exposure_exp_bound {m n k : ℕ} (hSize : m ≤ n)
    (f : (Fin m ↪ Fin n) → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hSwap : ∀ e : Fin m ↪ Fin n, ∀ a b : Fin n,
      |f e - f (e.trans (Equiv.swap a b).toEmbedding)| ≤ K) (hk : k ≤ m) (t : ℝ) :
    finiteMean (fun e => Real.exp (t * (injectionExposureMean f k e - finiteMean f))) ≤
      Real.exp ((k : ℝ) * K ^ 2 * t ^ 2 / 2) := by
  haveI : Nonempty (Fin m ↪ Fin n) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin] using hSize)
  revert hk
  induction k with
  | zero =>
    intro _
    simp only [injection_exposure_mean_zero, sub_self, mul_zero, Real.exp_zero,
      finiteMean_const, Nat.cast_zero, zero_mul, zero_div, le_refl]
  | succ k ih =>
    intro hk
    calc
      _ ≤ Real.exp (K ^ 2 * t ^ 2 / 2) *
          finiteMean (fun e => Real.exp (t * (injectionExposureMean f k e - finiteMean f))) :=
        injection_exposure_exp_step (by omega) f hK hSwap t
      _ ≤ Real.exp (K ^ 2 * t ^ 2 / 2) * Real.exp ((k : ℝ) * K ^ 2 * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (ih (by omega)) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

theorem uniform_injection_lower_tail {m n : ℕ} (hSize : m ≤ n)
    (f : (Fin m ↪ Fin n) → ℝ) {K ε : ℝ} (hK : 0 ≤ K)
    (hSwap : ∀ e : Fin m ↪ Fin n, ∀ a b : Fin n,
      |f e - f (e.trans (Equiv.swap a b).toEmbedding)| ≤ K) (hε : 0 ≤ ε) :
    uniformProbability (fun e : Fin m ↪ Fin n => ε ≤ finiteMean f - f e) ≤
      Real.exp (-ε ^ 2 / (2 * (m : ℝ) * K ^ 2)) := by
  letI : MeasurableSpace (Fin m ↪ Fin n) := ⊤
  haveI : MeasurableSingletonClass (Fin m ↪ Fin n) := ⟨fun _ => trivial⟩
  let μ := finiteUniformMeasure (Fin m ↪ Fin n)
  have hSG : HasSubgaussianMGF (fun e => finiteMean f - f e)
      ⟨(m : ℝ) * K ^ 2, by positivity⟩ μ := by
    constructor
    · intro _
      exact Integrable.of_finite
    · intro t
      rw [mgf, integral_finiteUniformMeasure]
      have h := injection_exposure_exp_bound hSize f hK hSwap (k := m) le_rfl (-t)
      simp only [injection_exposure_mean_full, neg_sq] at h
      have hFun : (fun e : Fin m ↪ Fin n => Real.exp (t * (finiteMean f - f e))) =
          (fun e => Real.exp (-t * (f e - finiteMean f))) := by funext e; congr 1; ring
      rw [hFun]
      exact h
  have h := hSG.measure_ge_le hε
  rw [finiteUniformMeasure_real] at h
  simpa only [mul_assoc] using h

end CircularLaw
