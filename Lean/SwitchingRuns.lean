import Part2.Intervals
import Mathlib.Order.Interval.Finset.Nat

noncomputable section

namespace Part2.SwitchingRuns

open Finset
open scoped BigOperators

variable {Arm : Type*} [DecidableEq Arm]

def runIndex (path : ℕ → Arm) : ℕ → ℕ
  | 0 => 0
  | n + 1 => runIndex path n + if path (n + 1) = path n then 0 else 1

theorem runIndex_step (path : ℕ → Arm) (n : ℕ) :
    runIndex path n ≤ runIndex path (n + 1) := by
  simp only [runIndex]
  omega

theorem runIndex_monotone (path : ℕ → Arm) : Monotone (runIndex path) := by
  exact monotone_nat_of_le_succ (runIndex_step path)

theorem equal_index_equal_path_of_le (path : ℕ → Arm) {u v : ℕ}
    (huv : u ≤ v) (heq : runIndex path u = runIndex path v) : path u = path v := by
  induction v with
  | zero =>
    have : u = 0 := by omega
    subst u
    rfl
  | succ v ih =>
    by_cases huv' : u ≤ v
    · have heq' : runIndex path u = runIndex path v := by
        have := runIndex_monotone path huv'
        have := runIndex_step path v
        omega
      have hp : path (v + 1) = path v := by
        by_contra hn
        simp only [runIndex, if_neg hn] at heq
        omega
      exact (ih huv' heq').trans hp.symm
    · have : u = v + 1 := by omega
      subst u
      rfl

theorem equal_index_equal_path (path : ℕ → Arm) {u v : ℕ}
    (heq : runIndex path u = runIndex path v) : path u = path v := by
  rcases le_total u v with huv | hvu
  · exact equal_index_equal_path_of_le path huv heq
  · exact (equal_index_equal_path_of_le path hvu heq.symm).symm

theorem image_runIndex_range (path : ℕ → Arm) (n : ℕ) :
    (range (n + 1)).image (runIndex path) = range (runIndex path n + 1) := by
  induction n with
  | zero => simp [runIndex]
  | succ n ih =>
    rw [range_add_one, image_insert, ih]
    by_cases hp : path (n + 1) = path n
    · simp only [runIndex, if_pos hp, Nat.add_zero]
      exact insert_eq_of_mem (mem_range.mpr (by omega))
    · simp only [runIndex, if_neg hp]
      exact (range_add_one (n := runIndex path n + 1)).symm

theorem runIndex_eq_actual_changes (path : ℕ → Arm) (n : ℕ) :
    runIndex path n = ((range n).filter (fun t => path (t + 1) ≠ path t)).card := by
  induction n with
  | zero => simp [runIndex]
  | succ n ih =>
    by_cases hp : path (n + 1) = path n
    · simp [runIndex, range_add_one, Finset.filter_insert, hp, ih]
    · simp [runIndex, range_add_one, Finset.filter_insert, hp, ih, Nat.add_comm]

def partition (path : ℕ → Arm) (T : ℕ) : Part2.Intervals.Partition (range T) where
  labels := (range T).image (runIndex path)
  block := fun j => (range T).filter (fun t => runIndex path t = j)
  disjoint := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro t hti htj
    exact hij ((mem_filter.mp hti).2.symm.trans (mem_filter.mp htj).2)
  covers := by
    ext t
    simp only [mem_biUnion, mem_image, mem_filter]
    constructor
    · rintro ⟨j, _, ht, _⟩
      exact ht
    · intro ht
      exact ⟨runIndex path t, ⟨t, ht, rfl⟩, ht, rfl⟩

theorem partition_card (path : ℕ → Arm) (T : ℕ) :
    (partition path (T + 1)).labels.card = runIndex path T + 1 := by
  change ((range (T + 1)).image (runIndex path)).card = _
  rw [image_runIndex_range, card_range]

theorem block_nonempty (path : ℕ → Arm) (T j : ℕ)
    (hj : j ∈ (partition path T).labels) :
    ((partition path T).block j).Nonempty := by
  obtain ⟨t, ht, hindex⟩ := mem_image.mp hj
  exact ⟨t, mem_filter.mpr ⟨ht, hindex⟩⟩

theorem block_order_convex (path : ℕ → Arm) (T j : ℕ) {u v w : ℕ}
    (hu : u ∈ (partition path T).block j)
    (hw : w ∈ (partition path T).block j) (huv : u ≤ v) (hvw : v ≤ w) :
    v ∈ (partition path T).block j := by
  obtain ⟨huT, hui⟩ := mem_filter.mp hu
  obtain ⟨hwT, hwi⟩ := mem_filter.mp hw
  apply mem_filter.mpr
  constructor
  · exact mem_range.mpr (lt_of_le_of_lt hvw (mem_range.mp hwT))
  · have := runIndex_monotone path huv
    have := runIndex_monotone path hvw
    omega

def label (path : ℕ → Arm) (T j : ℕ) : Arm :=
  if h : ((partition path T).block j).Nonempty then
    path (((partition path T).block j).min' h)
  else path 0

theorem block_constant (path : ℕ → Arm) (T j : ℕ)
    (hj : j ∈ (partition path T).labels) {t : ℕ}
    (ht : t ∈ (partition path T).block j) : path t = label path T j := by
  have hn := block_nonempty path T j hj
  unfold label
  rw [dif_pos hn]
  apply equal_index_equal_path
  exact (mem_filter.mp ht).2.trans
    (mem_filter.mp (Finset.min'_mem _ hn)).2.symm

theorem block_eq_Icc (path : ℕ → Arm) (T j : ℕ)
    (hj : j ∈ (partition path T).labels) :
    (partition path T).block j =
      Icc (((partition path T).block j).min' (block_nonempty path T j hj))
        (((partition path T).block j).max' (block_nonempty path T j hj)) := by
  have hn := block_nonempty path T j hj
  ext t
  constructor
  · intro ht
    exact mem_Icc.mpr ⟨Finset.min'_le _ t ht, Finset.le_max' _ t ht⟩
  · intro ht
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp ht
    exact block_order_convex path T j (Finset.min'_mem _ hn) (Finset.max'_mem _ hn) hlo hhi

theorem all_intervals_to_actual_path (T : ℕ) (path : ℕ → Arm)
    (loss : ℕ → Arm → ℝ) (played w : ℕ → ℝ) (C B : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ a b : ℕ, Icc a b ⊆ range (T + 1) → ∀ k : Arm,
      (∑ t ∈ Icc a b, (played t - loss t k)) ≤
        C * Real.sqrt ((Icc a b).card : ℝ) + ∑ t ∈ Icc a b, w t)
    (hbudget : ∑ t ∈ range (T + 1), w t ≤ B) :
    (∑ t ∈ range (T + 1), (played t - loss t (path t))) ≤
      C * Real.sqrt (((T + 1 : ℕ) : ℝ) *
        (((((range T).filter (fun t => path (t + 1) ≠ path t)).card + 1 : ℕ)) : ℝ)) + B := by
  rw [← runIndex_eq_actual_changes path T]
  apply (partition path (T + 1)).switching_path_of_card (T + 1) (runIndex path T)
    rfl (partition_card path T) loss played path (label path (T + 1)) w C B hC
  · intro j hj t ht
    exact block_constant path (T + 1) j hj ht
  · intro j hj k
    have hsub : (partition path (T + 1)).block j ⊆ range (T + 1) :=
      filter_subset _ _
    rw [block_eq_Icc path (T + 1) j hj] at hsub ⊢
    exact hlocal _ _ hsub k
  · exact hbudget

end Part2.SwitchingRuns
