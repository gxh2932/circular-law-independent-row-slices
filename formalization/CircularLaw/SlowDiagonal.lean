import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Monotone.Basic

/-!
# A monotone slow diagonal for eventual estimates

Every fixed stage has a finite threshold. Increasing thresholds let the
stage grow to infinity slowly enough that its own estimate holds at the
current dimension. The selected stage is monotone.
-/

noncomputable section
open Classical Filter

namespace CircularLaw

def diagonalThreshold (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => b 0
  | k + 1 => max (b (k + 1)) (diagonalThreshold b k + 1)

theorem diagonalThreshold_ge (b : ℕ → ℕ) (k : ℕ) : b k ≤ diagonalThreshold b k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_left _ _

theorem diagonalThreshold_strictMono (b : ℕ → ℕ) : StrictMono (diagonalThreshold b) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)

theorem diagonalThreshold_ge_index (b : ℕ → ℕ) (k : ℕ) : k ≤ diagonalThreshold b k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k hk =>
    exact (Nat.succ_le_succ hk).trans (le_max_right _ _)

def slowDiagonalStage (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => diagonalThreshold b k ≤ n) n

theorem slowDiagonalStage_monotone (b : ℕ → ℕ) : Monotone (slowDiagonalStage b) := by
  intro m n hmn
  exact Nat.findGreatest_mono (fun _ h => h.trans hmn) hmn

theorem slowDiagonalStage_tendsto (b : ℕ → ℕ) :
    Tendsto (slowDiagonalStage b) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (diagonalThreshold b k)] with n hn
  exact Nat.le_findGreatest ((diagonalThreshold_ge_index b k).trans hn) hn

theorem slowDiagonalStage_threshold (b : ℕ → ℕ) :
    ∀ᶠ n in atTop, diagonalThreshold b (slowDiagonalStage b n) ≤ n := by
  filter_upwards [eventually_ge_atTop (diagonalThreshold b 0)] with n hn
  exact Nat.findGreatest_spec (P := fun k => diagonalThreshold b k ≤ n) (Nat.zero_le n) hn

theorem exists_monotone_slow_diagonal (P : ℕ → ℕ → Prop)
    (hP : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ q : ℕ → ℕ, Monotone q ∧ Tendsto q atTop atTop ∧ ∀ᶠ n in atTop, P (q n) n := by
  choose b hb using fun k => eventually_atTop.mp (hP k)
  refine ⟨slowDiagonalStage b, slowDiagonalStage_monotone b, slowDiagonalStage_tendsto b, ?_⟩
  filter_upwards [slowDiagonalStage_threshold b] with n hn
  exact hb _ n ((diagonalThreshold_ge b _).trans hn)

end CircularLaw
