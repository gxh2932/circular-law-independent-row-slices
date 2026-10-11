import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Prod.Lex
import Mathlib.Order.PiLex

/-!
# Deterministic greedy star clusters

An admissible nonempty cluster has a representative related to every member.
The tie-break first compares cardinalities and then the indicator vectors in
lexicographic order, exactly as in the manuscript. Removing maximal stars
until the first small star leaves a set with bounded relation degree.
-/

noncomputable section
open Classical

namespace CircularLaw

def correlationStarAdmissible {n : ℕ} (R : Fin n → Fin n → Prop)
    (U : Finset (Fin n)) : Prop :=
  U = ∅ ∨ ∃ i ∈ U, ∀ j ∈ U, R i j

def correlationStarCandidates {n : ℕ} (R : Fin n → Fin n → Prop)
    (K : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  K.powerset.filter (correlationStarAdmissible R)

def correlationClusterRank {n : ℕ} (U : Finset (Fin n)) : ℕ ×ₗ Lex (Fin n → Bool) :=
  toLex (U.card, toLex (fun i => decide (i ∈ U)))

theorem correlationClusterRank_injective {n : ℕ} :
    Function.Injective (correlationClusterRank (n := n)) := by
  intro U V h
  have hIndicator : (fun i => decide (i ∈ U)) = (fun i => decide (i ∈ V)) :=
    congrArg (fun r : ℕ ×ₗ Lex (Fin n → Bool) => ofLex ((ofLex r).2)) h
  ext i
  simpa only [decide_eq_decide] using congrFun hIndicator i

theorem correlationStarCandidates_nonempty {n : ℕ} (R : Fin n → Fin n → Prop)
    (K : Finset (Fin n)) : (correlationStarCandidates R K).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [correlationStarCandidates, correlationStarAdmissible]

def greedyCorrelationCluster {n : ℕ} (R : Fin n → Fin n → Prop)
    (K : Finset (Fin n)) : Finset (Fin n) :=
  Classical.choose (Finset.exists_max_image (correlationStarCandidates R K)
    correlationClusterRank (correlationStarCandidates_nonempty R K))

theorem greedyCorrelationCluster_spec {n : ℕ} (R : Fin n → Fin n → Prop)
    (K : Finset (Fin n)) :
    greedyCorrelationCluster R K ∈ correlationStarCandidates R K ∧
      ∀ U ∈ correlationStarCandidates R K,
        correlationClusterRank U ≤ correlationClusterRank (greedyCorrelationCluster R K) :=
  Classical.choose_spec (Finset.exists_max_image (correlationStarCandidates R K)
    correlationClusterRank (correlationStarCandidates_nonempty R K))

theorem greedyCorrelationCluster_subset {n : ℕ} (R : Fin n → Fin n → Prop)
    (K : Finset (Fin n)) : greedyCorrelationCluster R K ⊆ K := by
  have h := (greedyCorrelationCluster_spec R K).1
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp h).1

theorem greedyCorrelationCluster_admissible {n : ℕ} (R : Fin n → Fin n → Prop)
    (K : Finset (Fin n)) : correlationStarAdmissible R (greedyCorrelationCluster R K) :=
  (Finset.mem_filter.mp (greedyCorrelationCluster_spec R K).1).2

theorem greedyCorrelationCluster_card_max {n : ℕ} (R : Fin n → Fin n → Prop)
    (K U : Finset (Fin n)) (hUK : U ⊆ K) (hU : correlationStarAdmissible R U) :
    U.card ≤ (greedyCorrelationCluster R K).card := by
  have hMem : U ∈ correlationStarCandidates R K :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUK, hU⟩
  exact Prod.Lex.monotone_fst _ _ ((greedyCorrelationCluster_spec R K).2 U hMem)

theorem greedyCorrelationCluster_neighbors {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (K : Finset (Fin n)) {i : Fin n} (hi : i ∈ K) :
    (K.filter (R i)).card ≤ (greedyCorrelationCluster R K).card := by
  apply greedyCorrelationCluster_card_max R K _ (Finset.filter_subset _ _)
  exact Or.inr ⟨i, Finset.mem_filter.mpr ⟨hi, hR i⟩,
    fun j hj => (Finset.mem_filter.mp hj).2⟩

theorem greedyCorrelationCluster_nonempty {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (K : Finset (Fin n)) (hK : K.Nonempty) :
    (greedyCorrelationCluster R K).Nonempty := by
  obtain ⟨i, hi⟩ := hK
  have h := greedyCorrelationCluster_neighbors R hR K hi
  have hPos : 0 < (K.filter (R i)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hR i⟩⟩
  exact Finset.card_pos.mp (hPos.trans_le h)

theorem greedyCorrelationCluster_empty {n : ℕ} (R : Fin n → Fin n → Prop) :
    greedyCorrelationCluster R ∅ = ∅ :=
  Finset.subset_empty.mp (greedyCorrelationCluster_subset R ∅)

theorem greedyCorrelationCluster_card_mono {n : ℕ} (R : Fin n → Fin n → Prop)
    {K H : Finset (Fin n)} (hKH : K ⊆ H) :
    (greedyCorrelationCluster R K).card ≤ (greedyCorrelationCluster R H).card :=
  greedyCorrelationCluster_card_max R H _
    ((greedyCorrelationCluster_subset R K).trans hKH)
    (greedyCorrelationCluster_admissible R K)

def greedyCorrelationRemaining {n : ℕ} (R : Fin n → Fin n → Prop) : ℕ → Finset (Fin n)
  | 0 => Finset.univ
  | k + 1 => greedyCorrelationRemaining R k \ greedyCorrelationCluster R
      (greedyCorrelationRemaining R k)

def greedyCorrelationStage {n : ℕ} (R : Fin n → Fin n → Prop) (k : ℕ) : Finset (Fin n) :=
  greedyCorrelationCluster R (greedyCorrelationRemaining R k)

theorem greedyCorrelationStage_subset {n : ℕ} (R : Fin n → Fin n → Prop) (k : ℕ) :
    greedyCorrelationStage R k ⊆ greedyCorrelationRemaining R k :=
  greedyCorrelationCluster_subset R _

theorem greedyCorrelationStage_representative {n : ℕ} (R : Fin n → Fin n → Prop)
    (k : ℕ) (hU : (greedyCorrelationStage R k).Nonempty) :
    ∃ i ∈ greedyCorrelationStage R k, ∀ j ∈ greedyCorrelationStage R k, R i j := by
  rcases greedyCorrelationCluster_admissible R (greedyCorrelationRemaining R k) with h | h
  · exact False.elim (hU.ne_empty h)
  · exact h

theorem greedyCorrelationRemaining_succ {n : ℕ} (R : Fin n → Fin n → Prop) (k : ℕ) :
    greedyCorrelationRemaining R (k + 1) =
      greedyCorrelationRemaining R k \ greedyCorrelationStage R k := rfl

theorem greedyCorrelationRemaining_antitone {n : ℕ} (R : Fin n → Fin n → Prop) :
    Antitone (greedyCorrelationRemaining R) := by
  apply antitone_nat_of_succ_le
  intro k
  exact Finset.sdiff_subset

theorem greedyCorrelationStage_card_antitone {n : ℕ} (R : Fin n → Fin n → Prop) :
    Antitone (fun k => (greedyCorrelationStage R k).card) := by
  intro k l hkl
  exact greedyCorrelationCluster_card_mono R (greedyCorrelationRemaining_antitone R hkl)

theorem greedyCorrelationRemaining_card_step {n : ℕ} (R : Fin n → Fin n → Prop) (k : ℕ) :
    (greedyCorrelationRemaining R (k + 1)).card + (greedyCorrelationStage R k).card =
      (greedyCorrelationRemaining R k).card :=
  Finset.card_sdiff_add_card_eq_card (greedyCorrelationStage_subset R k)

theorem greedyCorrelationRemaining_card_le {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (k : ℕ) : (greedyCorrelationRemaining R k).card ≤ n - k := by
  induction k with
  | zero => simp [greedyCorrelationRemaining]
  | succ k ih =>
    by_cases hK : (greedyCorrelationRemaining R k).Nonempty
    · have hPos := Finset.card_pos.mpr (greedyCorrelationCluster_nonempty R hR _ hK)
      have hStep := greedyCorrelationRemaining_card_step R k
      change 0 < (greedyCorrelationStage R k).card at hPos
      omega
    · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hK
      simp [greedyCorrelationRemaining_succ, hEmpty]

theorem greedyCorrelationRemaining_terminal {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) : greedyCorrelationRemaining R n = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := greedyCorrelationRemaining_card_le R hR n
  omega

theorem greedyCorrelationStage_terminal {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) : greedyCorrelationStage R n = ∅ := by
  rw [greedyCorrelationStage, greedyCorrelationRemaining_terminal R hR,
    greedyCorrelationCluster_empty]

theorem greedyCorrelationStage_pairwise_disjoint {n : ℕ}
    (R : Fin n → Fin n → Prop) {k l : ℕ} (hkl : k < l) :
    Disjoint (greedyCorrelationStage R k) (greedyCorrelationStage R l) := by
  apply Finset.disjoint_left.mpr
  intro i hik hil
  have hiRem := greedyCorrelationStage_subset R l hil
  have hiNext := greedyCorrelationRemaining_antitone R (Nat.succ_le_of_lt hkl) hiRem
  exact (Finset.mem_sdiff.mp hiNext).2 hik

theorem greedyCorrelationRemaining_card_sum {n : ℕ}
    (R : Fin n → Fin n → Prop) (k : ℕ) :
    (greedyCorrelationRemaining R k).card +
      ∑ l ∈ Finset.range k, (greedyCorrelationStage R l).card = n := by
  induction k with
  | zero => simp [greedyCorrelationRemaining]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hStep := greedyCorrelationRemaining_card_step R k
    omega

def greedyCorrelationDiscarded {n : ℕ} (R : Fin n → Fin n → Prop)
    (k : ℕ) : Finset (Fin n) := Finset.univ \ greedyCorrelationRemaining R k

theorem greedyCorrelationDiscarded_eq_union {n : ℕ}
    (R : Fin n → Fin n → Prop) (k : ℕ) :
    greedyCorrelationDiscarded R k =
      (Finset.range k).biUnion (greedyCorrelationStage R) := by
  induction k with
  | zero => simp [greedyCorrelationDiscarded, greedyCorrelationRemaining]
  | succ k ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, ← ih]
    ext i
    simp only [greedyCorrelationDiscarded, greedyCorrelationRemaining_succ,
      Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    tauto

theorem greedyCorrelationDiscarded_card {n : ℕ}
    (R : Fin n → Fin n → Prop) (k : ℕ) :
    (greedyCorrelationDiscarded R k).card =
      ∑ l ∈ Finset.range k, (greedyCorrelationStage R l).card := by
  have h := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (greedyCorrelationRemaining R k))
  have hSum := greedyCorrelationRemaining_card_sum R k
  change (greedyCorrelationDiscarded R k).card +
    (greedyCorrelationRemaining R k).card = Finset.univ.card at h
  rw [Finset.card_univ, Fintype.card_fin] at h
  omega

theorem greedyCorrelationStage_small_exists {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) : ∃ k, (greedyCorrelationStage R k).card ≤ b := by
  refine ⟨n, ?_⟩
  simp [greedyCorrelationStage_terminal R hR]

def greedyCorrelationStop {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) : ℕ :=
  Nat.find (greedyCorrelationStage_small_exists R hR b)

theorem greedyCorrelationStop_small {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) :
    (greedyCorrelationStage R (greedyCorrelationStop R hR b)).card ≤ b :=
  Nat.find_spec (greedyCorrelationStage_small_exists R hR b)

theorem greedyCorrelationStop_before_large {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) {k : ℕ} (hk : k < greedyCorrelationStop R hR b) :
    b < (greedyCorrelationStage R k).card :=
  lt_of_not_ge (Nat.find_min (greedyCorrelationStage_small_exists R hR b) hk)

theorem greedyCorrelationStop_before_nonempty {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) {k : ℕ} (hk : k < greedyCorrelationStop R hR b) :
    (greedyCorrelationStage R k).Nonempty :=
  Finset.card_pos.mp ((Nat.zero_le b).trans_lt (greedyCorrelationStop_before_large R hR b hk))

def greedyCorrelationRepresentative {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) (k : Fin (greedyCorrelationStop R hR b)) : Fin n :=
  Classical.choose (greedyCorrelationStage_representative R k.val
    (greedyCorrelationStop_before_nonempty R hR b k.isLt))

theorem greedyCorrelationRepresentative_spec {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) (k : Fin (greedyCorrelationStop R hR b)) :
    greedyCorrelationRepresentative R hR b k ∈ greedyCorrelationStage R k.val ∧
      ∀ j ∈ greedyCorrelationStage R k.val, R (greedyCorrelationRepresentative R hR b k) j :=
  Classical.choose_spec (greedyCorrelationStage_representative R k.val
    (greedyCorrelationStop_before_nonempty R hR b k.isLt))

theorem greedyCorrelationStop_le_dimension {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) : greedyCorrelationStop R hR b ≤ n := by
  apply Nat.find_min' (greedyCorrelationStage_small_exists R hR b)
  simp [greedyCorrelationStage_terminal R hR]

def greedyCorrelationExceptional {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) : Finset (Fin n) :=
  greedyCorrelationDiscarded R (greedyCorrelationStop R hR b)

theorem greedyCorrelationExceptional_eq_union {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) :
    greedyCorrelationExceptional R hR b =
      (Finset.range (greedyCorrelationStop R hR b)).biUnion (greedyCorrelationStage R) :=
  greedyCorrelationDiscarded_eq_union R _

theorem greedyCorrelationExceptional_complement {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) :
    Finset.univ \ greedyCorrelationExceptional R hR b =
      greedyCorrelationRemaining R (greedyCorrelationStop R hR b) := by
  ext i
  simp [greedyCorrelationExceptional, greedyCorrelationDiscarded]

theorem greedyCorrelationExceptional_neighbors {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) {i : Fin n}
    (hi : i ∈ Finset.univ \ greedyCorrelationExceptional R hR b) :
    ((Finset.univ \ greedyCorrelationExceptional R hR b).filter (R i)).card ≤ b := by
  rw [greedyCorrelationExceptional_complement] at hi ⊢
  exact (greedyCorrelationCluster_neighbors R hR _ hi).trans
    (greedyCorrelationStop_small R hR b)

theorem greedyCorrelationStop_mul_bound {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) :
    greedyCorrelationStop R hR b * (b + 1) ≤
      (greedyCorrelationExceptional R hR b).card := by
  rw [greedyCorrelationExceptional, greedyCorrelationDiscarded_card]
  calc
    _ = ∑ _l ∈ Finset.range (greedyCorrelationStop R hR b), (b + 1) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro l hl
      exact greedyCorrelationStop_before_large R hR b (Finset.mem_range.mp hl)

theorem greedyCorrelationStop_mul_le_dimension {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) : greedyCorrelationStop R hR b * (b + 1) ≤ n := by
  have hCard : (greedyCorrelationExceptional R hR b).card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (greedyCorrelationExceptional R hR b)
  exact (greedyCorrelationStop_mul_bound R hR b).trans hCard

end CircularLaw
