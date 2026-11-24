import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Explicit finite mass transport for endogenous remapping

This module constructs the transport part of E2.  It does not assume or assert
that the transport's edge-order premise follows from proximal optimality.
That variational step, and existence of a proximal minimizer, remain separate.
-/

namespace Part2.ConvexRemap

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def excess (q p : ι → ℝ) (i : ι) : ℝ := max (q i - p i) 0
def demand (q p : ι → ℝ) (i : ι) : ℝ := max (p i - q i) 0
def movedMass (q p : ι → ℝ) : ℝ := ∑ i, excess q p i
noncomputable def flow (q p : ι → ℝ) (k j : ι) : ℝ :=
  excess q p k * demand q p j / movedMass q p
noncomputable def plan (q p : ι → ℝ) (k j : ι) : ℝ :=
  (if k = j then min (q k) (p k) else 0) + flow q p k j

/-- Zero source rows use identity, avoiding division by zero. -/
noncomputable def remap (q p : ι → ℝ) (k j : ι) : ℝ :=
  if q k = 0 then (if k = j then 1 else 0) else plan q p k j / q k

theorem excess_nonneg (q p : ι → ℝ) (i : ι) : 0 ≤ excess q p i :=
  le_max_right _ _

theorem demand_nonneg (q p : ι → ℝ) (i : ι) : 0 ≤ demand q p i :=
  le_max_right _ _

theorem excess_sub_demand (q p : ι → ℝ) (i : ι) :
    excess q p i - demand q p i = q i - p i := by
  by_cases h : q i ≤ p i
  · simp [excess, demand, max_eq_right (sub_nonpos.mpr h),
      max_eq_left (sub_nonneg.mpr h)] <;> ring
  · have h' := le_of_lt (lt_of_not_ge h)
    simp [excess, demand, max_eq_left (sub_nonneg.mpr h'),
      max_eq_right (sub_nonpos.mpr h')] <;> ring

theorem retained_add_excess (q p : ι → ℝ) (i : ι) :
    min (q i) (p i) + excess q p i = q i := by
  by_cases h : q i ≤ p i
  · simp [excess, min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
  · have h' := le_of_lt (lt_of_not_ge h)
    simp [excess, min_eq_right h', max_eq_left (sub_nonneg.mpr h')]

theorem retained_add_demand (q p : ι → ℝ) (i : ι) :
    min (q i) (p i) + demand q p i = p i := by
  simpa [min_comm, excess, demand] using retained_add_excess p q i

theorem balanced_mass (q p : ι → ℝ) (hs : ∑ i, q i = ∑ i, p i) :
    (∑ i, demand q p i) = movedMass q p := by
  have h : (∑ i, excess q p i) - (∑ i, demand q p i) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [excess_sub_demand]
    rw [Finset.sum_sub_distrib, hs, sub_self]
  unfold movedMass
  linarith

theorem abs_difference_eq_excess_add_demand (q p : ι → ℝ) (i : ι) :
    |p i - q i| = excess q p i + demand q p i := by
  by_cases h : q i ≤ p i
  · simp [excess, demand, abs_of_nonneg (sub_nonneg.mpr h),
      max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
  · have h' := le_of_lt (lt_of_not_ge h)
    simp [excess, demand, abs_of_nonpos (sub_nonpos.mpr h'),
      max_eq_right (sub_nonpos.mpr h'), max_eq_left (sub_nonneg.mpr h')] <;> ring

/-- The L1 proximal penalty charges exactly the mass transported off a source. -/
theorem half_l1_eq_movedMass (q p : ι → ℝ) (hs : ∑ i, q i = ∑ i, p i) :
    (∑ i, |p i - q i|) / 2 = movedMass q p := by
  simp_rw [abs_difference_eq_excess_add_demand, Finset.sum_add_distrib]
  rw [balanced_mass q p hs]
  change (movedMass q p + movedMass q p) / 2 = movedMass q p
  ring

theorem movedMass_nonneg (q p : ι → ℝ) : 0 ≤ movedMass q p := by
  exact Finset.sum_nonneg (fun i _ => excess_nonneg q p i)

theorem excess_eq_zero_of_mass_zero (q p : ι → ℝ)
    (hz : movedMass q p = 0) (i : ι) : excess q p i = 0 := by
  have hle : excess q p i ≤ movedMass q p := by
    exact Finset.single_le_sum (fun j _ => excess_nonneg q p j) (Finset.mem_univ i)
  have hn := excess_nonneg q p i
  linarith

theorem demand_eq_zero_of_mass_zero (q p : ι → ℝ)
    (hs : ∑ i, q i = ∑ i, p i) (hz : movedMass q p = 0) (i : ι) :
    demand q p i = 0 := by
  have hle : demand q p i ≤ ∑ j, demand q p j := by
    exact Finset.single_le_sum (fun j _ => demand_nonneg q p j) (Finset.mem_univ i)
  rw [balanced_mass q p hs, hz] at hle
  exact le_antisymm hle (demand_nonneg q p i)

theorem flow_nonneg (q p : ι → ℝ) (k j : ι) : 0 ≤ flow q p k j := by
  exact div_nonneg (mul_nonneg (excess_nonneg q p k) (demand_nonneg q p j))
    (movedMass_nonneg q p)

theorem flow_row_sum (q p : ι → ℝ) (hs : ∑ i, q i = ∑ i, p i) (k : ι) :
    (∑ j, flow q p k j) = excess q p k := by
  by_cases hz : movedMass q p = 0
  · simp [flow, hz, excess_eq_zero_of_mass_zero q p hz k]
  · simp only [flow, ← Finset.sum_div, ← Finset.mul_sum]
    rw [balanced_mass q p hs]
    exact mul_div_cancel_right₀ _ hz

theorem flow_column_sum (q p : ι → ℝ) (hs : ∑ i, q i = ∑ i, p i) (j : ι) :
    (∑ k, flow q p k j) = demand q p j := by
  by_cases hz : movedMass q p = 0
  · simp [flow, hz, demand_eq_zero_of_mass_zero q p hs hz j]
  · simp only [flow, ← Finset.sum_div, ← Finset.sum_mul]
    change movedMass q p * demand q p j / movedMass q p = _
    exact mul_div_cancel_left₀ _ hz

theorem plan_nonneg (q p : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hp : ∀ i, 0 ≤ p i) (k j : ι) : 0 ≤ plan q p k j := by
  unfold plan
  apply add_nonneg _ (flow_nonneg q p k j)
  split_ifs
  · exact le_min (hq k) (hp k)
  · exact le_refl 0

theorem plan_row_sum (q p : ι → ℝ) (hs : ∑ i, q i = ∑ i, p i) (k : ι) :
    (∑ j, plan q p k j) = q k := by
  simp only [plan, Finset.sum_add_distrib]
  rw [flow_row_sum q p hs k]
  simpa using retained_add_excess q p k

theorem plan_column_sum (q p : ι → ℝ) (hs : ∑ i, q i = ∑ i, p i) (j : ι) :
    (∑ k, plan q p k j) = p j := by
  simp only [plan, Finset.sum_add_distrib]
  rw [flow_column_sum q p hs j]
  simpa using retained_add_demand q p j

theorem plan_zero_source (q p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (k j : ι) (hz : q k = 0) : plan q p k j = 0 := by
  have he : excess q p k = 0 := by
    simp [excess, hz, max_eq_right (neg_nonpos.mpr (hp k))]
  simp [plan, flow, hz, hp k, he]

theorem remap_nonneg (q p : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hp : ∀ i, 0 ≤ p i) (k j : ι) : 0 ≤ remap q p k j := by
  unfold remap
  split_ifs
  · norm_num
  · norm_num
  · exact div_nonneg (plan_nonneg q p hq hp k j) (hq k)

theorem remap_row_stochastic (q p : ι → ℝ)
    (hs : ∑ i, q i = ∑ i, p i) (k : ι) : (∑ j, remap q p k j) = 1 := by
  by_cases hz : q k = 0
  · simp [remap, hz]
  · simp only [remap, hz, if_false, ← Finset.sum_div]
    rw [plan_row_sum q p hs k, div_self hz]

theorem source_times_remap (q p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (k j : ι) :
    q k * remap q p k j = plan q p k j := by
  by_cases hz : q k = 0
  · rw [plan_zero_source q p hp k j hz]
    simp [hz]
  · simp only [remap, hz, if_false]
    field_simp [hz]

/-- Exact distribution consistency, including zero source and zero moved mass. -/
theorem remap_consistent (q p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, q i = ∑ i, p i) (j : ι) :
    (∑ k, q k * remap q p k j) = p j := by
  simp_rw [source_times_remap q p hp]
  exact plan_column_sum q p hs j

theorem flow_edge (q p : ι → ℝ) (k j : ι) (hf : flow q p k j ≠ 0) :
    p k < q k ∧ q j < p j := by
  constructor
  · by_contra h
    have hz : excess q p k = 0 := by
      exact max_eq_right (sub_nonpos.mpr (le_of_not_gt h))
    exact hf (by simp [flow, hz])
  · by_contra h
    have hz : demand q p j = 0 := by
      exact max_eq_right (sub_nonpos.mpr (le_of_not_gt h))
    exact hf (by simp [flow, hz])

/-- A positive transport edge inherits any donor-to-receiver loss ordering. -/
theorem flow_loss_le (q p L : ι → ℝ)
    (hedge : ∀ k j, p k < q k → q j < p j → L j ≤ L k) (k j : ι) :
    flow q p k j * L j ≤ flow q p k j * L k := by
  by_cases hz : flow q p k j = 0
  · simp [hz]
  · obtain ⟨hk, hj⟩ := flow_edge q p k j hz
    exact mul_le_mul_of_nonneg_left (hedge k j hk hj) (flow_nonneg q p k j)

theorem plan_loss_le (q p L : ι → ℝ)
    (hedge : ∀ k j, p k < q k → q j < p j → L j ≤ L k) (k j : ι) :
    plan q p k j * L j ≤ plan q p k j * L k := by
  by_cases h : k = j
  · subst j; exact le_refl _
  · simpa [plan, h] using flow_loss_le q p L hedge k j

/-- Every source row is dominated, even if that source has no mass. -/
theorem remap_row_dominates (q p L : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hs : ∑ i, q i = ∑ i, p i)
    (hedge : ∀ k j, p k < q k → q j < p j → L j ≤ L k) (k : ι) :
    (∑ j, remap q p k j * L j) ≤ L k := by
  by_cases hz : q k = 0
  · simp [remap, hz, ite_mul]
  · have hpoint (j : ι) : remap q p k j * L j ≤ remap q p k j * L k := by
      simp only [remap, hz, if_false]
      have h := div_le_div_of_nonneg_right (plan_loss_le q p L hedge k j) (hq k)
      simpa only [div_mul_eq_mul_div] using h
    calc
      _ ≤ ∑ j, remap q p k j * L k := Finset.sum_le_sum (fun j _ => hpoint j)
      _ = L k := by rw [← Finset.sum_mul, remap_row_stochastic q p hs k, one_mul]

/-- Public-span robustness of the donor/receiver gradient-gap interface. -/
theorem public_robust_edge_order (q p a b : ι → ℝ) (W : ℝ)
    (hgap : ∀ k j, p k < q k → q j < p j → W ≤ a k - a j)
    (hpublic : ∀ k j, b j - b k ≤ W) :
    ∀ k j, p k < q k → q j < p j → a j + b j ≤ a k + b k := by
  intro k j hk hj
  have hg := hgap k j hk hj
  have hb := hpublic k j
  linarith

/-- Constructive transport interface for E2; the gradient-gap premise is explicit.
The matrix is fixed before the universally quantified public vector is supplied.
This does not prove that a proximal minimizer has the required gradient gap. -/
theorem exists_robust_remap (q p a : ι → ℝ) (W : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, q i = ∑ i, p i)
    (hgap : ∀ k j, p k < q k → q j < p j → W ≤ a k - a j) :
    ∃ M : ι → ι → ℝ,
      (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j = 1) ∧
      (∀ j, ∑ k, q k * M k j = p j) ∧
      (∀ b : ι → ℝ, (∀ k j, b j - b k ≤ W) →
        ∀ k, (∑ j, M k j * (a j + b j)) ≤ a k + b k) := by
  refine ⟨remap q p, remap_nonneg q p hq hp, remap_row_stochastic q p hs,
    remap_consistent q p hp hs, ?_⟩
  intro b hb k
  exact remap_row_dominates q p (fun i => a i + b i) hq hs
    (public_robust_edge_order q p a b W hgap hb) k

end Part2.ConvexRemap
