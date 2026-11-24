import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Finite weighted maximum principle for an actual killed symmetric graph operator.
No inverse-matrix, PSD, stochastic, or full C3 conclusion is asserted.
-/
namespace Part2.WeightedGraphMaximum

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def graphOperator (lam : ℝ) (mass : ι → ℝ) (g : ι → ι → ℝ)
    (w : ι → ℝ) (i : ι) : ℝ :=
  lam * mass i * w i + ∑ j, g i j * (w i - w j)

def dipole (a b i : ι) : ℝ := (if i = a then 1 else 0) - (if i = b then 1 else 0)

theorem symmetric_flow_sum_zero (g : ι → ι → ℝ) (w : ι → ℝ)
    (hsym : ∀ i j, g i j = g j i) :
    (∑ i, ∑ j, g i j * (w i - w j)) = 0 := by
  have hs : (∑ i, ∑ j, g i j * (w i - w j)) =
      -(∑ i, ∑ j, g i j * (w i - w j)) := by
    calc
      _ = ∑ j, ∑ i, g i j * (w i - w j) := sum_comm
      _ = ∑ i, ∑ j, -(g i j * (w i - w j)) := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        rw [hsym j i]
        ring
      _ = _ := by simp only [sum_neg_distrib]
  linarith

theorem graphOperator_sum (lam : ℝ) (mass : ι → ℝ) (g : ι → ι → ℝ)
    (w : ι → ℝ) (hsym : ∀ i j, g i j = g j i) :
    (∑ i, graphOperator lam mass g w i) = lam * (∑ i, mass i * w i) := by
  calc
    _ = (∑ i, lam * (mass i * w i)) + ∑ i, ∑ j, g i j * (w i - w j) := by
      simp only [graphOperator, sum_add_distrib, mul_assoc]
    _ = _ := by rw [symmetric_flow_sum_zero g w hsym, add_zero, ← Finset.mul_sum]

theorem dipole_sum_zero (a b : ι) : (∑ i, dipole a b i) = 0 := by
  simp [dipole, sum_sub_distrib, Finset.sum_ite_eq']

theorem dipole_weighted_mean_zero (lam : ℝ) (mass : ι → ℝ) (g : ι → ι → ℝ)
    (w : ι → ℝ) (a b : ι) (hlam : 0 < lam) (hsym : ∀ i j, g i j = g j i)
    (heq : ∀ i, graphOperator lam mass g w i = dipole a b i) :
    (∑ i, mass i * w i) = 0 := by
  have hs : lam * (∑ i, mass i * w i) = 0 := by
    rw [← graphOperator_sum lam mass g w hsym]
    calc
      _ = ∑ i, dipole a b i := sum_congr rfl (fun i _ => heq i)
      _ = 0 := dipole_sum_zero a b
  exact (mul_eq_zero.mp hs).resolve_left hlam.ne'

theorem dipole_solution_nonzero (lam : ℝ) (mass : ι → ℝ) (g : ι → ι → ℝ)
    (w : ι → ℝ) (a b : ι) (hab : a ≠ b)
    (heq : ∀ i, graphOperator lam mass g w i = dipole a b i) :
    ∃ i, w i ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  have ha := heq a
  simp [graphOperator, hzero, dipole, hab] at ha

theorem weighted_zero_has_both_signs (mass w : ι → ℝ) (hmass : ∀ i, 0 < mass i)
    (hmean : (∑ i, mass i * w i) = 0) (hnonzero : ∃ i, w i ≠ 0) :
    (∃ i, 0 < w i) ∧ (∃ i, w i < 0) := by
  constructor
  · by_contra hpos
    have hall : ∀ i, w i ≤ 0 := by
      intro i
      exact le_of_not_gt (fun hi => hpos ⟨i, hi⟩)
    have hz := (sum_eq_zero_iff_of_nonpos
      (fun i (_ : i ∈ (univ : Finset ι)) => mul_nonpos_of_nonneg_of_nonpos (hmass i).le (hall i))).mp hmean
    obtain ⟨i, hi⟩ := hnonzero
    exact hi ((mul_eq_zero.mp (hz i (mem_univ i))).resolve_left (hmass i).ne')
  · by_contra hneg
    have hall : ∀ i, 0 ≤ w i := by
      intro i
      exact le_of_not_gt (fun hi => hneg ⟨i, hi⟩)
    have hz := (sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (univ : Finset ι)) => mul_nonneg (hmass i).le (hall i))).mp hmean
    obtain ⟨i, hi⟩ := hnonzero
    exact hi ((mul_eq_zero.mp (hz i (mem_univ i))).resolve_left (hmass i).ne')

theorem dipole_solution_signs (lam : ℝ) (mass : ι → ℝ) (g : ι → ι → ℝ)
    (w : ι → ℝ) (a b : ι) (hlam : 0 < lam) (hmass : ∀ i, 0 < mass i)
    (hsym : ∀ i j, g i j = g j i) (hab : a ≠ b)
    (heq : ∀ i, graphOperator lam mass g w i = dipole a b i) :
    (∃ i, 0 < w i) ∧ (∃ i, w i < 0) := by
  exact weighted_zero_has_both_signs mass w hmass
    (dipole_weighted_mean_zero lam mass g w a b hlam hsym heq)
    (dipole_solution_nonzero lam mass g w a b hab heq)

theorem dipole_maximum_at_source (lam : ℝ) (mass : ι → ℝ) (g : ι → ι → ℝ)
    (w : ι → ℝ) (a b : ι) (hlam : 0 < lam) (hmass : ∀ i, 0 < mass i)
    (hg : ∀ i j, 0 ≤ g i j) (hsym : ∀ i j, g i j = g j i) (hab : a ≠ b)
    (heq : ∀ i, graphOperator lam mass g w i = dipole a b i) :
    ∀ i, w i ≤ w a := by
  obtain ⟨m, _, hmax⟩ := exists_max_image (univ : Finset ι) w univ_nonempty
  obtain ⟨k, hk⟩ := (dipole_solution_signs lam mass g w a b hlam hmass hsym hab heq).1
  have hmpos : 0 < w m := lt_of_lt_of_le hk (hmax k (mem_univ k))
  have hma : m = a := by
    by_contra hma
    have hflow : 0 ≤ ∑ j, g m j * (w m - w j) :=
      sum_nonneg (fun j _ => mul_nonneg (hg m j) (sub_nonneg.mpr (hmax j (mem_univ j))))
    have hstrict : 0 < graphOperator lam mass g w m := by
      unfold graphOperator
      have hkilled := mul_pos (mul_pos hlam (hmass m)) hmpos
      linarith
    have hright : dipole a b m ≤ 0 := by
      simp only [dipole, if_neg hma, zero_sub]
      split_ifs <;> norm_num
    rw [heq m] at hstrict
    linarith
  intro i
  simpa [hma] using hmax i (mem_univ i)

theorem dipole_minimum_at_sink (lam : ℝ) (mass : ι → ℝ) (g : ι → ι → ℝ)
    (w : ι → ℝ) (a b : ι) (hlam : 0 < lam) (hmass : ∀ i, 0 < mass i)
    (hg : ∀ i j, 0 ≤ g i j) (hsym : ∀ i j, g i j = g j i) (hab : a ≠ b)
    (heq : ∀ i, graphOperator lam mass g w i = dipole a b i) :
    ∀ i, w b ≤ w i := by
  obtain ⟨m, _, hmin⟩ := exists_min_image (univ : Finset ι) w univ_nonempty
  obtain ⟨k, hk⟩ := (dipole_solution_signs lam mass g w a b hlam hmass hsym hab heq).2
  have hmneg : w m < 0 := lt_of_le_of_lt (hmin k (mem_univ k)) hk
  have hmb : m = b := by
    by_contra hmb
    have hflow : (∑ j, g m j * (w m - w j)) ≤ 0 :=
      sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hg m j)
        (sub_nonpos.mpr (hmin j (mem_univ j))))
    have hstrict : graphOperator lam mass g w m < 0 := by
      unfold graphOperator
      have hkilled := mul_neg_of_pos_of_neg (mul_pos hlam (hmass m)) hmneg
      linarith
    have hright : 0 ≤ dipole a b m := by
      simp only [dipole, if_neg hmb, sub_zero]
      split_ifs <;> norm_num
    rw [heq m] at hstrict
    linarith
  intro i
  simpa [hmb] using hmin i (mem_univ i)

theorem weighted_graph_maximum_principle (lam : ℝ) (mass : ι → ℝ) (g : ι → ι → ℝ)
    (w : ι → ℝ) (a b : ι) (hlam : 0 < lam) (hmass : ∀ i, 0 < mass i)
    (hg : ∀ i j, 0 ≤ g i j) (hsym : ∀ i j, g i j = g j i) (hab : a ≠ b)
    (heq : ∀ i, graphOperator lam mass g w i = dipole a b i) :
    ∀ i, w b ≤ w i ∧ w i ≤ w a := by
  intro i
  exact ⟨dipole_minimum_at_sink lam mass g w a b hlam hmass hg hsym hab heq i,
    dipole_maximum_at_source lam mass g w a b hlam hmass hg hsym hab heq i⟩

theorem weighted_graph_oscillation_bound (lam : ℝ) (mass : ι → ℝ) (g : ι → ι → ℝ)
    (w : ι → ℝ) (a b : ι) (hlam : 0 < lam) (hmass : ∀ i, 0 < mass i)
    (hg : ∀ i j, 0 ≤ g i j) (hsym : ∀ i j, g i j = g j i) (hab : a ≠ b)
    (heq : ∀ i, graphOperator lam mass g w i = dipole a b i) :
    ∀ i j, |w i - w j| ≤ w a - w b := by
  have hb := weighted_graph_maximum_principle lam mass g w a b hlam hmass hg hsym hab heq
  intro i j
  rw [abs_le]
  constructor <;> linarith [(hb i).1, (hb i).2, (hb j).1, (hb j).2]

theorem weighted_graph_l1_bound (lam : ℝ) (mass : ι → ℝ) (g : ι → ι → ℝ)
    (w : ι → ℝ) (a b : ι) (hlam : 0 < lam) (hmass : ∀ i, 0 < mass i)
    (hg : ∀ i j, 0 ≤ g i j) (hsym : ∀ i j, g i j = g j i) (hab : a ≠ b)
    (heq : ∀ i, graphOperator lam mass g w i = dipole a b i) :
    (∑ i, mass i * |w i|) ≤ (∑ i, mass i) * (w a - w b) := by
  have hb := weighted_graph_maximum_principle lam mass g w a b hlam hmass hg hsym hab heq
  obtain ⟨hp, hn⟩ := dipole_solution_signs lam mass g w a b hlam hmass hsym hab heq
  obtain ⟨p, hp⟩ := hp
  obtain ⟨m, hm⟩ := hn
  have hsource : 0 < w a := lt_of_lt_of_le hp (hb p).2
  have hsink : w b < 0 := lt_of_le_of_lt (hb m).1 hm
  have hpoint : ∀ i, |w i| ≤ w a - w b := by
    intro i
    rw [abs_le]
    constructor <;> linarith [(hb i).1, (hb i).2]
  calc
    _ ≤ ∑ i, mass i * (w a - w b) :=
      sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hmass i).le)
    _ = _ := (sum_mul _ _ _).symm

end Part2.WeightedGraphMaximum
