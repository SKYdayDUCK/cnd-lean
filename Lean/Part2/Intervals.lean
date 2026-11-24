import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Finite partition reduction for interval and switching regret

This file proves a deterministic reduction. The local regret inequalities and
the single global private budget are explicit inputs, not statistical claims.
No dyadic cover or sleeping-expert guarantee is asserted here.
-/

namespace Part2.Intervals

open scoped BigOperators

/-- A finite, disjoint cover; empty blocks are allowed. -/
structure Partition (H : Finset ℕ) where
  labels : Finset ℕ
  block : ℕ → Finset ℕ
  disjoint : (labels : Set ℕ).PairwiseDisjoint block
  covers : labels.biUnion block = H

namespace Partition

variable {H : Finset ℕ} (P : Partition H)

/-- Every per-round quantity is counted exactly once. No sign assumption. -/
theorem sum_blocks (f : ℕ → ℝ) :
    (∑ j ∈ P.labels, ∑ t ∈ P.block j, f t) = ∑ t ∈ H, f t := by
  calc
    _ = ∑ t ∈ P.labels.biUnion P.block, f t := (Finset.sum_biUnion P.disjoint).symm
    _ = _ := congrArg (fun S : Finset ℕ => ∑ t ∈ S, f t) P.covers

theorem sum_lengths :
    (∑ j ∈ P.labels, ((P.block j).card : ℝ)) = (H.card : ℝ) := by
  simpa using P.sum_blocks (fun _ ↦ 1)

/-- Cauchy--Schwarz gives the exact sqrt(number of blocks * total length) cost. -/
theorem sum_sqrt_lengths_le :
    (∑ j ∈ P.labels, Real.sqrt ((P.block j).card : ℝ)) ≤
      Real.sqrt ((H.card : ℝ) * (P.labels.card : ℝ)) := by
  have h := Real.sum_sqrt_mul_sqrt_le P.labels
    (f := fun _ : ℕ ↦ (1 : ℝ))
    (g := fun j : ℕ ↦ ((P.block j).card : ℝ))
    (fun _ ↦ zero_le_one) (fun _ ↦ Nat.cast_nonneg _)
  simp only [Real.sqrt_one, one_mul, Finset.sum_const, nsmul_eq_mul,
    mul_one] at h
  rw [P.sum_lengths] at h
  calc
    _ ≤ Real.sqrt (P.labels.card : ℝ) * Real.sqrt (H.card : ℝ) := h
    _ = Real.sqrt ((H.card : ℝ) * (P.labels.card : ℝ)) := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg P.labels.card), mul_comm]

/-- The sum of local private costs is at most the one global budget.
Nonnegativity is unnecessary for a full partition, because there is equality. -/
theorem private_budget_once (w : ℕ → ℝ) (B : ℝ)
    (hB : ∑ t ∈ H, w t ≤ B) :
    (∑ j ∈ P.labels, ∑ t ∈ P.block j, w t) ≤ B := by
  rw [P.sum_blocks]
  exact hB

/-- Local public costs sum by Cauchy--Schwarz, while the private measure is
charged once. This theorem is valid for every finite disjoint cover. -/
theorem aggregate (r w : ℕ → ℝ) (C B : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ j ∈ P.labels,
      (∑ t ∈ P.block j, r t) ≤
        C * Real.sqrt ((P.block j).card : ℝ) + ∑ t ∈ P.block j, w t)
    (hbudget : ∑ t ∈ H, w t ≤ B) :
    (∑ t ∈ H, r t) ≤
      C * Real.sqrt ((H.card : ℝ) * (P.labels.card : ℝ)) + B := by
  calc
    (∑ t ∈ H, r t) = ∑ j ∈ P.labels, ∑ t ∈ P.block j, r t :=
      (P.sum_blocks r).symm
    _ ≤ ∑ j ∈ P.labels,
        (C * Real.sqrt ((P.block j).card : ℝ) + ∑ t ∈ P.block j, w t) :=
      Finset.sum_le_sum hlocal
    _ = C * (∑ j ∈ P.labels, Real.sqrt ((P.block j).card : ℝ)) +
        ∑ t ∈ H, w t := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, P.sum_blocks]
    _ ≤ C * Real.sqrt ((H.card : ℝ) * (P.labels.card : ℝ)) + B :=
      add_le_add (mul_le_mul_of_nonneg_left P.sum_sqrt_lengths_le hC) hbudget

/-- A comparator may be selected after the local bounds are established.
Only constancy on each block is required; no predictability assumption. -/
theorem switching_path {Arm : Type*} (loss : ℕ → Arm → ℝ)
    (played : ℕ → ℝ) (path : ℕ → Arm) (label : ℕ → Arm)
    (w : ℕ → ℝ) (C B : ℝ) (hC : 0 ≤ C)
    (hconstant : ∀ j ∈ P.labels, ∀ t ∈ P.block j, path t = label j)
    (hlocal : ∀ j ∈ P.labels, ∀ k : Arm,
      (∑ t ∈ P.block j, (played t - loss t k)) ≤
        C * Real.sqrt ((P.block j).card : ℝ) + ∑ t ∈ P.block j, w t)
    (hbudget : ∑ t ∈ H, w t ≤ B) :
    (∑ t ∈ H, (played t - loss t (path t))) ≤
      C * Real.sqrt ((H.card : ℝ) * (P.labels.card : ℝ)) + B := by
  apply P.aggregate (fun t ↦ played t - loss t (path t)) w C B hC _ hbudget
  intro j hj
  calc
    _ = ∑ t ∈ P.block j, (played t - loss t (label j)) := by
      apply Finset.sum_congr rfl
      intro t ht
      change played t - loss t (path t) = played t - loss t (label j)
      rw [hconstant j hj t ht]
    _ ≤ _ := hlocal j hj (label j)

/-- The usual `sqrt(T * (s+1))` form once a decomposition into `s+1`
constant blocks has been supplied. The decomposition is structural input. -/
theorem switching_path_of_card {Arm : Type*} (T s : ℕ)
    (horizon : H = Finset.range T) (hcount : P.labels.card = s + 1)
    (loss : ℕ → Arm → ℝ) (played : ℕ → ℝ) (path : ℕ → Arm)
    (label : ℕ → Arm) (w : ℕ → ℝ) (C B : ℝ) (hC : 0 ≤ C)
    (hconstant : ∀ j ∈ P.labels, ∀ t ∈ P.block j, path t = label j)
    (hlocal : ∀ j ∈ P.labels, ∀ k : Arm,
      (∑ t ∈ P.block j, (played t - loss t k)) ≤
        C * Real.sqrt ((P.block j).card : ℝ) + ∑ t ∈ P.block j, w t)
    (hbudget : ∑ t ∈ H, w t ≤ B) :
    (∑ t ∈ Finset.range T, (played t - loss t (path t))) ≤
      C * Real.sqrt ((T : ℝ) * ((s + 1 : ℕ) : ℝ)) + B := by
  have h := P.switching_path loss played path label w C B hC hconstant hlocal hbudget
  simpa only [horizon, Finset.card_range, hcount] using h

end Partition

/-- A concrete cut of any finite horizon into the times before/after `cut`.
For `H = range T` these are the two adjacent discrete intervals, including
the endpoint cases `cut = 0` and `T ≤ cut`. -/
def splitAt (H : Finset ℕ) (cut : ℕ) : Partition H where
  labels := {0, 1}
  block := fun j ↦ if j = 0 then H.filter (fun t ↦ t < cut)
    else H.filter (fun t ↦ cut ≤ t)
  disjoint := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · apply Finset.disjoint_left.mpr
      intro t ht ht'
      change t ∈ H.filter (fun t => t < cut) at ht
      change t ∈ H.filter (fun t => cut ≤ t) at ht'
      exact (Nat.not_lt_of_ge (Finset.mem_filter.mp ht').2) (Finset.mem_filter.mp ht).2
    · apply Finset.disjoint_left.mpr
      intro t ht ht'
      change t ∈ H.filter (fun t => cut ≤ t) at ht
      change t ∈ H.filter (fun t => t < cut) at ht'
      exact (Nat.not_lt_of_ge (Finset.mem_filter.mp ht).2) (Finset.mem_filter.mp ht').2
    · exact (hij rfl).elim
  covers := by
    ext t
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, (rfl | rfl), ht⟩
      · exact (Finset.mem_filter.mp ht).1
      · exact (Finset.mem_filter.mp ht).1
    · intro ht
      by_cases hcut : t < cut
      · exact ⟨0, Or.inl rfl, Finset.mem_filter.mpr ⟨ht, hcut⟩⟩
      · exact ⟨1, Or.inr rfl, Finset.mem_filter.mpr ⟨ht, Nat.le_of_not_gt hcut⟩⟩

theorem splitAt_card (H : Finset ℕ) (cut : ℕ) :
    (splitAt H cut).labels.card = 2 := by change ({0, 1} : Finset ℕ).card = 2; decide

/-- Nonnegative private mass on any subset is bounded by the global mass. -/
theorem local_private_le_global (H I : Finset ℕ) (w : ℕ → ℝ)
    (hsub : I ⊆ H) (hw : ∀ t ∈ H, 0 ≤ w t) :
    (∑ t ∈ I, w t) ≤ ∑ t ∈ H, w t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t ht _ ↦ hw t ht)

end Part2.Intervals
