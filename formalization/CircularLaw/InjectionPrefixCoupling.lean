import CircularLaw.FiniteFiberMean
import CircularLaw.UniformEmbeddingMarginal

/-!
# Coupling uniform injection fibres by a codomain transposition

Two choices for the next exposed coordinate, with the same past, are
coupled by swapping their values throughout the injection. This is an
exact bijection of the two next-prefix fibres. It supplies the bounded
conditional-mean increments needed for injection concentration.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical

namespace CircularLaw

def injectionPrefix {m n : ℕ} (k : ℕ) (e : Fin m ↪ Fin n) : Fin m → Option (Fin n) :=
  fun j => if j.val < k then some (e j) else none

theorem injection_prefix_eq_iff {m n k : ℕ} (a b : Fin m ↪ Fin n) :
    injectionPrefix k a = injectionPrefix k b ↔ ∀ j : Fin m, j.val < k → a j = b j := by
  constructor
  · intro h j hj
    have hCoord := congrFun h j
    simp only [injectionPrefix, if_pos hj] at hCoord
    exact Option.some.inj hCoord
  · intro h
    funext j
    by_cases hj : j.val < k
    · simp only [injectionPrefix, if_pos hj, h j hj]
    · simp only [injectionPrefix, if_neg hj]

theorem injection_prefix_zero {m n : ℕ} (e : Fin m ↪ Fin n) :
    injectionPrefix 0 e = fun _ => none := by
  ext j
  simp [injectionPrefix]

theorem injection_prefix_full_injective {m n : ℕ} :
    Function.Injective (injectionPrefix (m := m) (n := n) m) := by
  intro a b h
  apply DFunLike.ext
  intro j
  exact (injection_prefix_eq_iff a b).mp h j j.isLt

theorem injection_prefix_refinement {m n k l : ℕ} (hkl : k ≤ l)
    {a b : Fin m ↪ Fin n} (h : injectionPrefix l a = injectionPrefix l b) :
    injectionPrefix k a = injectionPrefix k b := by
  apply (injection_prefix_eq_iff a b).mpr
  intro j hj
  exact (injection_prefix_eq_iff a b).mp h j (hj.trans_le hkl)

theorem injection_next_prefix_swap {m n : ℕ} (i : Fin m) (a b e : Fin m ↪ Fin n)
    (hPast : injectionPrefix i.val a = injectionPrefix i.val b)
    (hNext : injectionPrefix (i.val + 1) e = injectionPrefix (i.val + 1) a) :
    injectionPrefix (i.val + 1) (e.trans (Equiv.swap (a i) (b i)).toEmbedding) =
      injectionPrefix (i.val + 1) b := by
  apply (injection_prefix_eq_iff _ _).mpr
  intro j hj
  have hValue := (injection_prefix_eq_iff e a).mp hNext j hj
  by_cases hji : j = i
  · subst j
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, hValue,
      Equiv.swap_apply_left]
  · have hBelow : j.val < i.val := by
      have hNe : j.val ≠ i.val := fun h => hji (Fin.ext h)
      omega
    have hSame := (injection_prefix_eq_iff a b).mp hPast j hBelow
    have hNeA : a j ≠ a i := fun h => hji (a.injective h)
    have hNeB : a j ≠ b i := by rw [hSame]; exact fun h => hji (b.injective h)
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
    rw [hValue, Equiv.swap_apply_of_ne_of_ne hNeA hNeB, hSame]

def injectionNextPrefixSwapEquiv {m n : ℕ} (i : Fin m) (a b : Fin m ↪ Fin n)
    (hPast : injectionPrefix i.val a = injectionPrefix i.val b) :
    {e : Fin m ↪ Fin n // injectionPrefix (i.val + 1) e = injectionPrefix (i.val + 1) a} ≃
      {e : Fin m ↪ Fin n // injectionPrefix (i.val + 1) e = injectionPrefix (i.val + 1) b} where
  toFun e := ⟨e.val.trans (Equiv.swap (a i) (b i)).toEmbedding,
    injection_next_prefix_swap i a b e.val hPast e.property⟩
  invFun e := ⟨e.val.trans (Equiv.swap (b i) (a i)).toEmbedding,
    injection_next_prefix_swap i b a e.val hPast.symm e.property⟩
  left_inv e := by
    apply Subtype.ext
    ext j
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.swap_comm,
      Equiv.swap_apply_self]
  right_inv e := by
    apply Subtype.ext
    ext j
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.swap_comm,
      Equiv.swap_apply_self]

theorem injection_next_fiber_mean_swap_bound {m n : ℕ} (i : Fin m) (a b : Fin m ↪ Fin n)
    (hPast : injectionPrefix i.val a = injectionPrefix i.val b) (f : (Fin m ↪ Fin n) → ℝ)
    {K : ℝ} (hSwap : ∀ e : Fin m ↪ Fin n,
      |f e - f (e.trans (Equiv.swap (a i) (b i)).toEmbedding)| ≤ K) :
    |finiteFiberMean (injectionPrefix (i.val + 1)) f (injectionPrefix (i.val + 1) a) -
      finiteFiberMean (injectionPrefix (i.val + 1)) f (injectionPrefix (i.val + 1) b)| ≤ K := by
  classical
  letI : Fintype {e : Fin m ↪ Fin n //
      injectionPrefix (i.val + 1) e = injectionPrefix (i.val + 1) a} :=
    @Subtype.fintype _ _ (fun _ => Classical.propDecidable _) inferInstance
  letI : Fintype {e : Fin m ↪ Fin n //
      injectionPrefix (i.val + 1) e = injectionPrefix (i.val + 1) b} :=
    @Subtype.fintype _ _ (fun _ => Classical.propDecidable _) inferInstance
  haveI := finiteFiberMean_reference_nonempty (injectionPrefix (i.val + 1)) a
  unfold finiteFiberMean
  apply abs_finiteMean_sub_of_equiv (injectionNextPrefixSwapEquiv i a b hPast)
    (fun e => f e.val) (fun e => f e.val)
  intro e
  exact hSwap e.val

end CircularLaw
