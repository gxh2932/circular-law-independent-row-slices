import CircularLaw.InjectionPrefixCoupling
import CircularLaw.FiniteFiberTower

/-!
# Actual Doob means for uniform injection exposure

The process starts at the literal uniform mean and ends at the sampled
value. Its fibrewise tower and zero-mean increments are pointwise.
The swap coupling bounds each increment whenever the sampled statistic
has a uniform codomain-transposition bound.
-/

noncomputable section
open Classical

namespace CircularLaw

def injectionPrefixMask {m n : ℕ} (k : ℕ) (p : Fin m → Option (Fin n)) :
    Fin m → Option (Fin n) := fun j => if j.val < k then p j else none

theorem injection_prefix_mask {m n k l : ℕ} (hkl : k ≤ l) (e : Fin m ↪ Fin n) :
    injectionPrefixMask k (injectionPrefix l e) = injectionPrefix k e := by
  funext j
  by_cases hj : j.val < k
  · simp only [injectionPrefixMask, injectionPrefix, if_pos hj, if_pos (hj.trans_le hkl)]
  · simp only [injectionPrefixMask, injectionPrefix, if_neg hj]

def injectionExposureMean {m n : ℕ} (f : (Fin m ↪ Fin n) → ℝ) (k : ℕ)
    (e : Fin m ↪ Fin n) : ℝ := finiteFiberMean (injectionPrefix k) f (injectionPrefix k e)

theorem injection_exposure_mean_congr {m n k : ℕ} (f : (Fin m ↪ Fin n) → ℝ)
    {a b : Fin m ↪ Fin n} (h : injectionPrefix k a = injectionPrefix k b) :
    injectionExposureMean f k a = injectionExposureMean f k b := by
  unfold injectionExposureMean
  rw [h]

theorem injection_exposure_mean_zero {m n : ℕ} (f : (Fin m ↪ Fin n) → ℝ)
    (e : Fin m ↪ Fin n) : injectionExposureMean f 0 e = finiteMean f := by
  classical
  haveI : Nonempty (Fin m ↪ Fin n) := ⟨e⟩
  have hMean := finiteMean_fiberMean (injectionPrefix (m := m) (n := n) 0) f
  have hConst : (fun a : Fin m ↪ Fin n =>
      finiteFiberMean (injectionPrefix 0) f (injectionPrefix 0 a)) =
      (fun _ => injectionExposureMean f 0 e) := by
    funext a
    unfold injectionExposureMean
    rw [injection_prefix_zero a, injection_prefix_zero e]
  rw [hConst, finiteMean_const] at hMean
  exact hMean

theorem injection_exposure_mean_full {m n : ℕ} (f : (Fin m ↪ Fin n) → ℝ)
    (e : Fin m ↪ Fin n) : injectionExposureMean f m e = f e :=
  finiteFiberMean_constant_on_reference (injectionPrefix m) f e
    (fun _ h => congrArg f (injection_prefix_full_injective h))

theorem injection_exposure_mean_tower {m n k : ℕ} (f : (Fin m ↪ Fin n) → ℝ)
    (e : Fin m ↪ Fin n) :
    finiteFiberMean (injectionPrefix k) (injectionExposureMean f (k + 1)) (injectionPrefix k e) =
      injectionExposureMean f k e := by
  classical
  haveI : Nonempty (Fin m ↪ Fin n) := ⟨e⟩
  letI : MeasurableSpace (Fin m ↪ Fin n) := ⊤
  haveI : MeasurableSingletonClass (Fin m ↪ Fin n) := ⟨fun _ => trivial⟩
  letI : MeasurableSpace (Fin m → Option (Fin n)) := ⊤
  haveI : MeasurableSingletonClass (Fin m → Option (Fin n)) := ⟨fun _ => trivial⟩
  have hMask : (fun a : Fin m ↪ Fin n => injectionPrefixMask k (injectionPrefix (k + 1) a)) =
      injectionPrefix k := funext (fun a => injection_prefix_mask (by omega) a)
  have hTower := finiteFiberMean_tower (injectionPrefix (m := m) (n := n) (k + 1))
    (injectionPrefixMask k) f e
  simpa only [hMask, injectionExposureMean, injection_prefix_mask (by omega : k ≤ k + 1)]
    using hTower

theorem injection_exposure_increment_fiber_mean_zero {m n k : ℕ}
    (f : (Fin m ↪ Fin n) → ℝ) (e : Fin m ↪ Fin n) :
    finiteFiberMean (injectionPrefix k)
      (fun a => injectionExposureMean f (k + 1) a - injectionExposureMean f k a)
      (injectionPrefix k e) = 0 := by
  rw [finiteFiberMean_sub, injection_exposure_mean_tower,
    finiteFiberMean_constant_on_reference _ _ e
      (fun a h => injection_exposure_mean_congr f h), sub_self]

theorem injection_exposure_increment_swap_bound {m n : ℕ} (i : Fin m)
    (f : (Fin m ↪ Fin n) → ℝ) {K : ℝ}
    (hSwap : ∀ e : Fin m ↪ Fin n, ∀ a b : Fin n,
      |f e - f (e.trans (Equiv.swap a b).toEmbedding)| ≤ K)
    (e : Fin m ↪ Fin n) :
    |injectionExposureMean f (i.val + 1) e - injectionExposureMean f i.val e| ≤ K := by
  have hRange : ∀ a : Fin m ↪ Fin n, injectionPrefix i.val a = injectionPrefix i.val e →
      injectionExposureMean f (i.val + 1) a ∈
        Set.Icc (injectionExposureMean f (i.val + 1) e - K)
          (injectionExposureMean f (i.val + 1) e + K) := by
    intro a h
    have hBound := injection_next_fiber_mean_swap_bound i a e h f (fun v => hSwap v (a i) (e i))
    have hAbs := abs_le.mp hBound
    constructor <;> dsimp only [injectionExposureMean] <;> linarith
  have hMean := finiteFiberMean_range_bound (injectionPrefix i.val)
    (injectionExposureMean f (i.val + 1)) e hRange
  rw [injection_exposure_mean_tower] at hMean
  exact abs_le.mpr (by constructor <;> linarith [hMean.1, hMean.2])

end CircularLaw
