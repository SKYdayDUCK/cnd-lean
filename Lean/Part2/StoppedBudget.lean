import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stopped nonnegative private budgets

The stopping mask is applied on the original probability space. No measure is
restricted to a statistical success event. The generic supermartingale theorem
below is conditional on the usual adaptedness/integrability interface, not a
formalization of the full learning algorithm or its confidence event.
-/

open MeasureTheory Filter
open scoped ProbabilityTheory BigOperators

namespace Part2.StoppedBudget

theorem exp_chord {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + (Real.exp 1 - 1) * x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1 - x by linarith) hx0 (show 1 - x + x = 1 by ring)
  calc
    Real.exp x = Real.exp ((1 - x) * 0 + x * 1) := by congr 1; ring
    _ ≤ (1 - x) * Real.exp 0 + x * Real.exp 1 := by
      simpa only [smul_eq_mul] using h
    _ = _ := by rw [Real.exp_zero]; ring

theorem exp_scaled_chord {B u : ℝ} (hB : 0 < B) (hu0 : 0 ≤ u) (huB : u ≤ B) :
    Real.exp (u / B) ≤ 1 + (Real.exp 1 - 1) * (u / B) :=
  exp_chord (div_nonneg hu0 hB.le) ((div_le_one hB).2 huB)

/-- This mask includes the first bad round in the zero part; it is not a
conditional probability measure. Predictability of `good` is supplied when
using the conditional-expectation interface. -/
def stoppedIncrement {Ω : Type*} (good : Ω → Prop) [DecidablePred good]
    (U : Ω → ℝ) (ω : Ω) : ℝ := if good ω then U ω else 0

theorem stoppedIncrement_bounds {Ω : Type*} (good : Ω → Prop) [DecidablePred good]
    (U : Ω → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hU : ∀ ω, good ω → 0 ≤ U ω ∧ U ω ≤ B) :
    ∀ ω, 0 ≤ stoppedIncrement good U ω ∧ stoppedIncrement good U ω ≤ B := by
  intro ω
  by_cases h : good ω
  · simpa [stoppedIncrement, h] using hU ω h
  · simp [stoppedIncrement, h, hB]

section Conditional

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {m : MeasurableSpace Ω}

/-- A predictable stopping mask commutes with conditional expectation on the
original space. In particular this does not condition `μ` on `good`. -/
theorem stopped_conditional_mean (good : Ω → Prop) [DecidablePred good]
    {U : Ω → ℝ} (hUi : Integrable U μ) (hgood : MeasurableSet[m] {ω | good ω}) :
    μ[stoppedIncrement good U | m] =ᵐ[μ] stoppedIncrement good (μ[U | m]) := by
  have heq (f : Ω → ℝ) : stoppedIncrement good f = {ω | good ω}.indicator f := by
    funext ω
    by_cases h : good ω <;> simp [stoppedIncrement, Set.indicator_apply, h]
  rw [heq U, heq (μ[U | m])]
  exact condExp_indicator hUi hgood

/-- The convex exponential chord implies the one-step conditional MGF bound.
All expectations refer to the same original measure `μ`. -/
theorem conditional_exp_chord (hm : m ≤ m₀) {X : Ω → ℝ}
    (hXm : AEStronglyMeasurable[m₀] X μ) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω ∧ X ω ≤ 1) :
    μ[fun ω => Real.exp (X ω) | m] ≤ᵐ[μ]
      fun ω => Real.exp ((Real.exp 1 - 1) * (μ[X | m]) ω) := by
  have hXi : Integrable X μ := (integrable_const (1 : ℝ)).mono' hXm (by
    filter_upwards [hX] with ω hω
    simpa [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2)
  have hEi : Integrable (fun ω => Real.exp (X ω)) μ :=
    (integrable_const (Real.exp 1)).mono' (Real.continuous_exp.comp_aestronglyMeasurable hXm) (by
      filter_upwards [hX] with ω hω
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hω.2)
  have hLi : Integrable (fun ω => 1 + (Real.exp 1 - 1) * X ω) μ :=
    (integrable_const (1 : ℝ)).add (hXi.const_mul _)
  have hmono := condExp_mono (m := m) hEi hLi (hX.mono fun ω hω => exp_chord hω.1 hω.2)
  have hadd := condExp_add (integrable_const (1 : ℝ)) (hXi.const_mul (Real.exp 1 - 1)) m
  have hmul := condExp_smul (μ := μ) (Real.exp 1 - 1) X m
  filter_upwards [hmono, hadd, hmul] with ω hω ha hb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const hm] at ha hb
  change (μ[fun x => 1 + (Real.exp 1 - 1) * X x | m]) ω =
    1 + (μ[fun x => (Real.exp 1 - 1) * X x | m]) ω at ha
  change (μ[fun x => (Real.exp 1 - 1) * X x | m]) ω =
    (Real.exp 1 - 1) * (μ[X | m]) ω at hb
  calc
    _ ≤ (μ[fun ω => 1 + (Real.exp 1 - 1) * X ω | m]) ω := hω
    _ = 1 + (Real.exp 1 - 1) * (μ[X | m]) ω := ha.trans (congrArg (fun z => 1 + z) hb)
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp ((Real.exp 1 - 1) * (μ[X | m]) ω)

/-- Conditional martingale interface: a nonnegative adapted integrable process
with the exponential-budget recursion is a genuine mathlib supermartingale.
The recursion is structural; no conditional MGF or supermartingale inequality
is assumed. `X` can be a stopped increment divided by its deterministic bound. -/
theorem budget_supermartingale_conditional {ℱ : Filtration ℕ m₀}
    {X Z : ℕ → Ω → ℝ}
    (hZm : Adapted ℱ Z) (hZi : ∀ n, Integrable (Z n) μ)
    (hZ0 : ∀ n ω, 0 ≤ Z n ω)
    (hXm : ∀ n, AEStronglyMeasurable[m₀] (X n) μ)
    (hX : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω ∧ X n ω ≤ 1)
    (hrec : ∀ n ω, Z (n + 1) ω = Z n ω *
      Real.exp (X n ω - (Real.exp 1 - 1) * (μ[X n | ℱ n]) ω)) :
    Supermartingale Z ℱ μ := by
  apply supermartingale_nat hZm hZi
  intro n
  let D : Ω → ℝ := fun ω => Z n ω *
    Real.exp (-((Real.exp 1 - 1) * (μ[X n | ℱ n]) ω))
  have hDm : StronglyMeasurable[ℱ n] D :=
    (hZm n).mul (Real.continuous_exp.comp_stronglyMeasurable
      ((stronglyMeasurable_condExp.const_mul (Real.exp 1 - 1)).neg))
  have heq : (fun ω => D ω * Real.exp (X n ω)) = Z (n + 1) := by
    funext ω
    rw [hrec]
    dsimp [D]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hEi : Integrable (fun ω => Real.exp (X n ω)) μ :=
    (integrable_const (Real.exp 1)).mono'
      (Real.continuous_exp.comp_aestronglyMeasurable (hXm n)) (by
        filter_upwards [hX n] with ω hω
        simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hω.2)
  have hprod : Integrable (fun ω => D ω * Real.exp (X n ω)) μ := by
    rw [heq]
    exact hZi (n + 1)
  have hpull := condExp_mul_of_stronglyMeasurable_left hDm hprod hEi
  have hmgf := conditional_exp_chord (ℱ.le n) (hXm n) (hX n)
  filter_upwards [hpull, hmgf] with ω hp hm
  rw [← heq]
  calc
    _ = D ω * (μ[fun ω => Real.exp (X n ω) | ℱ n]) ω := hp
    _ ≤ D ω * Real.exp ((Real.exp 1 - 1) * (μ[X n | ℱ n]) ω) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (hZ0 n ω) (Real.exp_pos _).le)
    _ = Z n ω := by
      dsimp [D]
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end Conditional

/-- Markov converts the actual supermartingale (not an assumed MGF bound) into
a fixed-time tail estimate. The exceptional event has real measure at most
`exp (-L)` on the original probability space. -/
theorem supermartingale_tail {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
    {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ)
    (hZ0 : ∀ n ω, 0 ≤ Z n ω) (hinit : Z 0 = fun _ => 1) (n : ℕ) (L : ℝ) :
    μ.real {ω | Real.exp L ≤ Z n ω} ≤ Real.exp (-L) := by
  have hmean : (∫ ω, Z n ω ∂μ) ≤ 1 := by
    calc
      _ = ∫ ω, (μ[Z n | ℱ 0]) ω ∂μ := (integral_condExp (ℱ.le 0)).symm
      _ ≤ ∫ ω, Z 0 ω ∂μ :=
        integral_mono_ae integrable_condExp (hZ.2.2 0) (hZ.2.1 0 n (Nat.zero_le n))
      _ = 1 := by rw [hinit]; simp
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (hZ0 n)) (hZ.2.2 n) (Real.exp L)
  rw [Real.exp_neg, ← one_div]
  apply (le_div_iff₀ (Real.exp_pos L)).2
  simpa [mul_comm] using hmarkov.trans hmean

/-- Deterministic decoding of the exponential budget. `S` and `M` stand for
the actual stopped sum and the sum of its predictable conditional means. -/
theorem actual_budget_of_exponential_bound {B S M L : ℝ} (hB : 0 < B)
    (h : Real.exp ((S - (Real.exp 1 - 1) * M) / B) < Real.exp L) :
    S ≤ (Real.exp 1 - 1) * M + B * L := by
  have hlog := Real.exp_lt_exp.mp h
  have hscaled := (div_lt_iff₀ hB).mp hlog
  nlinarith

/-- Conditional actual-budget tail. The interface assumes an exponential
representation of a genuine supermartingale, not its tail inequality. The
learning algorithm's predictable stopping time and cumulative-mean formula
still need to be instantiated separately. -/
theorem actual_budget_tail_conditional {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
    {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ)
    (hZ0 : ∀ n ω, 0 ≤ Z n ω) (hinit : Z 0 = fun _ => 1)
    {B : ℝ} (hB : 0 < B) (n : ℕ) (S M : Ω → ℝ)
    (hformula : ∀ ω, Z n ω = Real.exp ((S ω - (Real.exp 1 - 1) * M ω) / B))
    (L : ℝ) :
    μ.real {ω | (Real.exp 1 - 1) * M ω + B * L ≤ S ω} ≤ Real.exp (-L) := by
  have hset : {ω | (Real.exp 1 - 1) * M ω + B * L ≤ S ω} =
      {ω | Real.exp L ≤ Z n ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, hformula, Real.exp_le_exp]
    rw [le_div_iff₀ hB]
    constructor <;> intro h <;> nlinarith
  rw [hset]
  exact supermartingale_tail hZ hZ0 hinit n L

section ExplicitProcess

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : Measure Ω)
  (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)

/-- The actual cumulative exponential process, defined on the original space. -/
noncomputable def budgetProcess (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (∑ i ∈ Finset.range n,
    (X i ω - (Real.exp 1 - 1) * (μ[X i | ℱ i]) ω))

theorem budgetProcess_zero : budgetProcess μ ℱ X 0 = fun _ => 1 := by
  funext ω
  simp [budgetProcess]

theorem budgetProcess_succ (n : ℕ) : budgetProcess μ ℱ X (n + 1) =
    fun ω => budgetProcess μ ℱ X n ω *
      Real.exp (X n ω - (Real.exp 1 - 1) * (μ[X n | ℱ n]) ω) := by
  funext ω
  simp only [budgetProcess, Finset.sum_range_succ, Real.exp_add]

theorem budgetProcess_adapted
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n)) :
    Adapted ℱ (budgetProcess μ ℱ X) := by
  intro n
  apply Real.continuous_exp.comp_stronglyMeasurable
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hXi : StronglyMeasurable[ℱ n] (X i) :=
    (hXm i).mono (ℱ.mono (Nat.succ_le_of_lt hin))
  have hMi : StronglyMeasurable[ℱ n] (μ[X i | ℱ i]) :=
    stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_of_lt hin))
  exact hXi.sub (hMi.const_mul _)

variable [IsProbabilityMeasure μ]

/-- A deterministic envelope proves integrability rather than assuming it. -/
theorem budgetProcess_le
    (hX : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω ∧ X n ω ≤ 1) (n : ℕ) :
    ∀ᵐ ω ∂μ, budgetProcess μ ℱ X n ω ≤ Real.exp (n : ℝ) := by
  have hc : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  induction n with
  | zero => simp [budgetProcess]
  | succ n ih =>
    have hmean : 0 ≤ᵐ[μ] μ[X n | ℱ n] :=
      condExp_nonneg (m := ℱ n) ((hX n).mono fun _ h => h.1)
    filter_upwards [ih, hX n, hmean] with ω hn hx hm
    rw [budgetProcess_succ]
    have hinc : X n ω - (Real.exp 1 - 1) * (μ[X n | ℱ n]) ω ≤ 1 := by
      nlinarith [mul_nonneg hc hm]
    calc
      _ ≤ Real.exp (n : ℝ) * Real.exp 1 :=
        mul_le_mul hn (Real.exp_le_exp.mpr hinc) (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((n + 1 : ℕ) : ℝ) := by rw [← Real.exp_add]; simp

theorem budgetProcess_integrable
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω ∧ X n ω ≤ 1) (n : ℕ) :
    Integrable (budgetProcess μ ℱ X n) μ := by
  have hmeas := ((budgetProcess_adapted μ ℱ X hXm) n).mono (ℱ.le n)
  apply (integrable_const (Real.exp (n : ℝ))).mono' hmeas.aestronglyMeasurable
  filter_upwards [budgetProcess_le μ ℱ X hX n] with ω hω
  simpa only [budgetProcess, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hω

/-- A complete generic construction from adapted bounded increments; no
supermartingale, cumulative-process integrability, or MGF is assumed. -/
theorem bounded_budget_supermartingale
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω ∧ X n ω ≤ 1) :
    Supermartingale (budgetProcess μ ℱ X) ℱ μ := by
  apply budget_supermartingale_conditional
    (budgetProcess_adapted μ ℱ X hXm) (budgetProcess_integrable μ ℱ X hXm hX)
    (fun _ _ => (Real.exp_pos _).le)
    (fun n => ((hXm n).mono (ℱ.le (n + 1))).aestronglyMeasurable) hX
  intro n ω
  exact congrFun (budgetProcess_succ μ ℱ X n) ω

/-- Generic original-space fixed-time nonnegative-budget concentration.
Instantiating `X n` with a normalized predictable stopped increment requires no
conditioning on the confidence-success event. -/
theorem bounded_budget_tail
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω ∧ X n ω ≤ 1) (n : ℕ) (L : ℝ) :
    μ.real {ω | (Real.exp 1 - 1) * (∑ i ∈ Finset.range n, (μ[X i | ℱ i]) ω) + L ≤
      ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-L) := by
  have hformula (ω : Ω) : budgetProcess μ ℱ X n ω =
      Real.exp (((∑ i ∈ Finset.range n, X i ω) - (Real.exp 1 - 1) *
        (∑ i ∈ Finset.range n, (μ[X i | ℱ i]) ω)) / 1) := by
    simp only [budgetProcess, div_one, Finset.sum_sub_distrib, Finset.mul_sum]
  simpa only [one_mul] using actual_budget_tail_conditional
    (bounded_budget_supermartingale μ ℱ X hXm hX) (fun _ _ => (Real.exp_pos _).le)
    (budgetProcess_zero μ ℱ X) (show (0 : ℝ) < 1 by exact zero_lt_one) n
    (fun ω => ∑ i ∈ Finset.range n, X i ω)
    (fun ω => ∑ i ∈ Finset.range n, (μ[X i | ℱ i]) ω) hformula L

end ExplicitProcess

end Part2.StoppedBudget
