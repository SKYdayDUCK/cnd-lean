import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite-sum algebra for Part 2 pairwise estimators

This module proves deterministic algebra only.  In particular, interpreting a
finite weighted sum as a conditional expectation requires the sampling and
centering assumptions proved outside this module.
-/

namespace Part2.Pairwise

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pairScore (p : ι → ℝ) (i j a : ι) : ℝ :=
  ((if a = i then p j else 0) - (if a = j then p i else 0)) / (p i + p j)

theorem weighted_indicator (p : ι → ℝ) (i : ι) (c : ℝ) :
    (∑ a, p a * (if a = i then c else 0)) = p i * c := by
  classical
  simp [mul_ite]

theorem pairScore_mean_zero (p : ι → ℝ) (i j : ι) :
    (∑ a, p a * pairScore p i j a) = 0 := by
  have hpoint (a : ι) : p a * pairScore p i j a =
      (p a * (if a = i then p j else 0) -
        p a * (if a = j then p i else 0)) / (p i + p j) := by
    unfold pairScore
    ring
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [weighted_indicator, weighted_indicator]
  ring

theorem pairScore_zero_denominator (p : ι → ℝ) (i j a : ι)
    (hs : p i + p j = 0) : pairScore p i j a = 0 := by
  simp [pairScore, hs]

theorem pair_variance_bounds (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 < a + b) (hu : a + b ≤ 1) :
    0 ≤ a*b/(a+b) ∧ a*b/(a+b) ≤ 1/4 ∧ a*b ≤ a*b/(a+b) := by
  have hab : 0 ≤ a*b := mul_nonneg ha hb
  constructor
  · exact div_nonneg hab (le_of_lt hs)
  constructor
  · apply (div_le_iff₀ hs).2
    nlinarith [sq_nonneg (a-b), mul_nonneg (le_of_lt hs) (sub_nonneg.mpr hu)]
  · apply (le_div_iff₀ hs).2
    nlinarith [mul_nonneg hab (sub_nonneg.mpr hu)]

theorem pairScore_signal (p θ : ι → ℝ) (z : ℝ) (i j : ι) :
    (∑ a, p a * pairScore p i j a * (θ a + z)) =
      (p i * p j / (p i + p j)) * (θ i - θ j) := by
  classical
  have h (k : ι) (c : ℝ) :
      (∑ a, p a * (if a = k then c else 0) * (θ a + z)) =
        p k * c * (θ k + z) := by
    simp [mul_ite, ite_mul]
  have hpoint (a : ι) : p a * pairScore p i j a * (θ a + z) =
      (p a * (if a = i then p j else 0) * (θ a + z) -
        p a * (if a = j then p i else 0) * (θ a + z)) / (p i + p j) := by
    unfold pairScore
    ring
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [h, h]
  ring

theorem pairScore_second_moment (p : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (hs : p i + p j ≠ 0) :
    (∑ a, p a * (pairScore p i j a)^2) = p i * p j / (p i + p j) := by
  classical
  have hpoint (a : ι) :
      p a * (pairScore p i j a)^2 =
      (if a = i then p i * (p j)^2 / (p i + p j)^2 else 0) +
      (if a = j then p j * (p i)^2 / (p i + p j)^2 else 0) := by
    by_cases hi : a = i
    · subst a
      simp [pairScore, hij, div_pow] <;> ring
    · by_cases hj : a = j
      · subst a
        simp [pairScore, hi, div_pow] <;> ring
      · simp [pairScore, hi, hj]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp [hs]
  <;> ring

theorem pairScore_abs_le_one (p : ι → ℝ) (hp : ∀ a, 0 ≤ p a) (i j a : ι) :
    |pairScore p i j a| ≤ 1 := by
  by_cases hs : p i + p j = 0
  · simp [pairScore, hs]
  have hspos : 0 < p i + p j := lt_of_le_of_ne (add_nonneg (hp i) (hp j)) (Ne.symm hs)
  rw [pairScore, abs_div, abs_of_pos hspos, div_le_one hspos, abs_le]
  constructor <;> split_ifs <;> linarith [hp i, hp j]

/-- The zero-mass branch is included; no exploration lower bound is required. -/
theorem pairScore_second_moment_nonneg (p : ι → ℝ) (hp : ∀ a, 0 ≤ p a)
    (i j : ι) (hij : i ≠ j) :
    (∑ a, p a * (pairScore p i j a)^2) = p i * p j / (p i + p j) := by
  by_cases hs : p i + p j = 0
  · simp [pairScore, hs]
  · exact pairScore_second_moment p i j hij hs

/-- A finite inner noise experiment, centered separately at every action. -/
theorem pairScore_centered_noise {ω : Type*} [Fintype ω]
    (p : ι → ℝ) (q e : ι → ω → ℝ) (i j : ι)
    (he : ∀ a, ∑ w, q a w * e a w = 0) :
    (∑ a, ∑ w, p a * pairScore p i j a * (q a w * e a w)) = 0 := by
  simp_rw [← Finset.mul_sum, he, mul_zero]
  simp

theorem pairScore_signal_with_centered_noise {ω : Type*} [Fintype ω]
    (p θ : ι → ℝ) (q e : ι → ω → ℝ) (z : ℝ) (i j : ι)
    (hq : ∀ a, ∑ w, q a w = 1) (he : ∀ a, ∑ w, q a w * e a w = 0) :
    (∑ a, ∑ w, p a * pairScore p i j a * q a w * (θ a + z - e a w)) =
      (p i * p j / (p i + p j)) * (θ i - θ j) := by
  have hpoint (a : ι) :
      (∑ w, p a * pairScore p i j a * q a w * (θ a + z - e a w)) =
        p a * pairScore p i j a * (θ a + z) := by
    calc
      _ = p a * pairScore p i j a *
          ((θ a + z) * (∑ w, q a w) - ∑ w, q a w * e a w) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro w hw <;> ring
      _ = _ := by rw [hq a, he a]; ring
  simp_rw [hpoint]
  exact pairScore_signal p θ z i j

theorem antisymmetric_weighted_sum_zero (p : ι → ℝ)
    (G : ι → ι → ℝ) (hG : ∀ i j, G i j = -G j i) :
    (∑ i, ∑ j, p i * p j * G i j) = 0 := by
  have hswap : (∑ i, ∑ j, p i * p j * G i j) =
      -(∑ i, ∑ j, p i * p j * G i j) := by
    calc
      _ = ∑ j, ∑ i, p i * p j * G i j := Finset.sum_comm
      _ = -(∑ i, ∑ j, p i * p j * G i j) := by
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hG j i]
        ring
  linarith

theorem gamma_full_sum (p : ι → ℝ) (g m r : ι → ι → ℝ)
    (hg : ∀ i j, g i j = -g j i) (hm : ∀ i j, m i j = -m j i) :
    (∑ i, p i * (∑ j, p j * (g i j - m i j + r i j))) =
      ∑ i, ∑ j, p i * p j * r i j := by
  have ha : ∀ i j, (g i j - m i j) = -(g j i - m j i) := by
    intro i j
    rw [hg i j, hm i j]
    ring
  have hz := antisymmetric_weighted_sum_zero p (fun i j => g i j - m i j) ha
  calc
    _ = (∑ i, ∑ j, p i * p j * (g i j - m i j)) +
        (∑ i, ∑ j, p i * p j * r i j) := by
      simp_rw [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
        apply Finset.sum_congr rfl <;> intro j hj <;> ring
    _ = _ := by rw [hz, zero_add]

theorem midpoint_interval (l u g : ℝ) (hl : l ≤ g) (hu : g ≤ u) :
    |g-(l+u)/2| ≤ (u-l)/2 := by
  rw [abs_le]
  constructor <;> linarith

theorem reversed_interval_midpoint (l u : ℝ) :
    ((-u)+(-l))/2 = -((l+u)/2) ∧
      ((-l)-(-u))/2 = (u-l)/2 := by
  constructor <;> ring

/-- Intersecting a confidence interval with the parameter range preserves truth. -/
theorem clipped_midpoint_radius (R c ρ g : ℝ)
    (hc : -R ≤ c ∧ c ≤ R) (hρ : 0 ≤ ρ)
    (hg : -R ≤ g ∧ g ≤ R) (hcover : |g - c| ≤ ρ) :
    let l := max (-R) (c - ρ)
    let u := min R (c + ρ)
    |g - (l + u) / 2| ≤ (u - l) / 2 ∧
      0 ≤ (u - l) / 2 ∧ (u - l) / 2 ≤ R ∧ (u - l) / 2 ≤ ρ := by
  dsimp
  have hcove := abs_le.mp hcover
  have hl : max (-R) (c - ρ) ≤ g := max_le hg.1 (by linarith [hcove.1])
  have hu : g ≤ min R (c + ρ) := le_min hg.2 (by linarith [hcove.2])
  refine ⟨midpoint_interval _ _ _ hl hu, ?_, ?_, ?_⟩
  · linarith
  · have := le_max_left (-R) (c - ρ)
    have := min_le_left R (c + ρ)
    linarith
  · have := le_max_right (-R) (c - ρ)
    have := min_le_right R (c + ρ)
    linarith

theorem moving_gauge_identity (p θ a : ι → ℝ) (r : ι → ι → ℝ)
    (hp : ∑ j, p j = 1) (i : ι) :
    θ i - (∑ j, p j * θ j) -
      (a i - (∑ j, p j * a j) - (∑ j, p j * r i j)) =
    ∑ j, p j * ((θ i - θ j) - (a i - a j) + r i j) := by
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  simp only [hp, one_mul]
  ring

theorem moving_gauge_bounds (p : ι → ℝ) (d r : ι → ι → ℝ) (B : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1)
    (hl : ∀ i j, -r i j ≤ d i j) (hu : ∀ i j, d i j ≤ r i j)
    (hr : ∀ i j, r i j ≤ B) (i : ι) :
    0 ≤ (∑ j, p j * (d i j + r i j)) ∧
      (∑ j, p j * (d i j + r i j)) ≤ 2 * B := by
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hp j) (by linarith [hl i j])
  · calc
      _ ≤ ∑ j, p j * (2 * B) := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (hp j)
        linarith [hu i j, hr i j]
      _ = 2 * B := by rw [← Finset.sum_mul, hs, one_mul]

theorem symmetric_sum_upper_triangle [LinearOrder ι] (p : ι → ℝ)
    (r : ι → ι → ℝ) (hr : ∀ i j, r i j = r j i) (hd : ∀ i, r i i = 0) :
    (∑ i, ∑ j, p i * p j * r i j) =
      2 * (∑ i, ∑ j, if i < j then p i * p j * r i j else 0) := by
  classical
  have hpoint (i j : ι) : p i * p j * r i j =
      (if i < j then p i * p j * r i j else 0) +
      (if j < i then p i * p j * r i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h]
  have hswap :
      (∑ i, ∑ j, if j < i then p i * p j * r i j else 0) =
      (∑ i, ∑ j, if i < j then p i * p j * r i j else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : i < j
    · simp only [if_pos h]
      rw [hr j i]
      ring
    · simp only [if_neg h]
  calc
    _ = ∑ i, ∑ j,
        ((if i < j then p i * p j * r i j else 0) +
          (if j < i then p i * p j * r i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpoint i j
    _ = (∑ i, ∑ j, if i < j then p i * p j * r i j else 0) +
        (∑ i, ∑ j, if j < i then p i * p j * r i j else 0) := by
      simp_rw [Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring

theorem gamma_upper_triangle [LinearOrder ι] (p : ι → ℝ)
    (g m r : ι → ι → ℝ)
    (hg : ∀ i j, g i j = -g j i) (hm : ∀ i j, m i j = -m j i)
    (hr : ∀ i j, r i j = r j i) (hd : ∀ i, r i i = 0) :
    (∑ i, p i * (∑ j, p j * (g i j - m i j + r i j))) =
      2 * (∑ i, ∑ j, if i < j then p i * p j * r i j else 0) := by
  rw [gamma_full_sum p g m r hg hm,
    symmetric_sum_upper_triangle p r hr hd]

theorem gamma_nonneg_le (p : ι → ℝ) (r : ι → ι → ℝ) (R : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hr : ∀ i j, 0 ≤ r i j ∧ r i j ≤ R) :
    0 ≤ (∑ i, ∑ j, p i * p j * r i j) ∧
      (∑ i, ∑ j, p i * p j * r i j) ≤ R := by
  constructor
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hp i) (hp j)) (hr i j).1
  · calc
      _ ≤ ∑ i, ∑ j, p i * p j * R := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hr i j).2 (mul_nonneg (hp i) (hp j))
      _ = R := by simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hs]; ring

theorem pair_mass_le_half [LinearOrder ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∑ i, ∑ j, if i < j then p i * p j else 0) ≤ 1/2 := by
  let r : ι → ι → ℝ := fun i j => if i = j then 0 else 1
  have hr : ∀ i j, 0 ≤ r i j ∧ r i j ≤ 1 := by
    intro i j
    dsimp [r]
    split_ifs <;> norm_num
  have hsym : ∀ i j, r i j = r j i := by
    intro i j
    simp [r, eq_comm]
  have hd : ∀ i, r i i = 0 := by intro i; simp [r]
  have hbound := (gamma_nonneg_le p r 1 hp hs hr).2
  rw [symmetric_sum_upper_triangle p r hsym hd] at hbound
  have hterm (i j : ι) :
      (if i < j then p i * p j * r i j else 0) =
        (if i < j then p i * p j else 0) := by
    by_cases hij : i < j
    · simp [hij, r, ne_of_lt hij]
    · simp [hij]
  simp_rw [hterm] at hbound
  linarith

/-- The logarithmic increment inequality used for information accumulation. -/
theorem small_increment_le_log (x : ℝ) (hx : 0 ≤ x) (hu : x ≤ 1/4) :
    x ≤ (5/4 : ℝ) * Real.log (1+x) := by
  have hpos : 0 < 1+x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hfrac : 1-(1+x)⁻¹ = x/(1+x) := by field_simp [ne_of_gt hpos]; ring
  rw [hfrac] at hlog
  have hxfrac : x ≤ (5/4 : ℝ) * (x/(1+x)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hpos).2
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hu)]
  exact hxfrac.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

theorem information_sum_bound {κ : Type*} (s : Finset κ) (u v V : κ → ℝ)
    (hv : ∀ k ∈ s, 0 ≤ v k ∧ v k ≤ 1/4)
    (hV : ∀ k ∈ s, 1 ≤ V k) (huv : ∀ k ∈ s, u k ≤ v k) :
    (∑ k ∈ s, u k / V k) ≤
      (5/4 : ℝ) * (∑ k ∈ s, Real.log (1 + v k / V k)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hpos : 0 < V k := by linarith [hV k hk]
  have hnonneg : 0 ≤ v k / V k := div_nonneg (hv k hk).1 (le_of_lt hpos)
  have hsmall : v k / V k ≤ 1/4 := by
    apply (div_le_iff₀ hpos).2
    linarith [(hv k hk).2, hV k hk]
  exact (div_le_div_of_nonneg_right (huv k hk) (le_of_lt hpos)).trans
    (small_increment_le_log _ hnonneg hsmall)

/-- Cauchy--Schwarz retains `u`, avoiding a separate sum of pairwise square roots. -/
theorem retained_mass_cauchy {κ : Type*} (s : Finset κ) (u V : κ → ℝ)
    (hu : ∀ k ∈ s, 0 ≤ u k) (hV : ∀ k ∈ s, 0 < V k) :
    (∑ k ∈ s, u k / Real.sqrt (V k)) ^ 2 ≤
      (∑ k ∈ s, u k) * (∑ k ∈ s, u k / V k) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s hu
    (fun k hk => div_nonneg (hu k hk) (le_of_lt (hV k hk)))
  intro k hk
  rw [div_pow, Real.sq_sqrt (le_of_lt (hV k hk))]
  ring

/-- The algebraic width budget before substituting a logarithmic information bound.
The index set may contain all (time, unordered-pair) coordinates at once. -/
theorem width_budget_retained_mass {κ : Type*} (s : Finset κ)
    (u V r : κ → ℝ) (A B : ℝ)
    (hu : ∀ k ∈ s, 0 ≤ u k) (hV : ∀ k ∈ s, 0 < V k)
    (hB : 0 ≤ B) (hr : ∀ k ∈ s, r k ≤ A / V k + B / Real.sqrt (V k)) :
    2 * (∑ k ∈ s, u k * r k) ≤
      2 * A * (∑ k ∈ s, u k / V k) +
        2 * B * Real.sqrt ((∑ k ∈ s, u k) * (∑ k ∈ s, u k / V k)) := by
  have hlinear : (∑ k ∈ s, u k * r k) ≤
      A * (∑ k ∈ s, u k / V k) + B * (∑ k ∈ s, u k / Real.sqrt (V k)) := by
    calc
      _ ≤ ∑ k ∈ s, u k * (A / V k + B / Real.sqrt (V k)) :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hr k hk) (hu k hk)
      _ = _ := by
        simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hcs := Real.le_sqrt_of_sq_le (retained_mass_cauchy s u V hu hV)
  have hscaled := mul_le_mul_of_nonneg_left hcs hB
  linarith

theorem k2_gamma_identity (p r : ℝ) :
    p * ((1-p) * r) + (1-p) * (p * r) = 2*p*(1-p)*r := by
  ring

theorem k2_predictor_difference (p m r : ℝ) :
    (1-p)*(m-r) - p*(-m-r) = m-r+2*p*r := by
  ring

end Part2.Pairwise
