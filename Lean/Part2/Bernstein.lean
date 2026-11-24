import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# Finite-time martingale Bernstein bounds on the original probability space

No conditional moment-generating-function or tail estimate is assumed. The
conditional exponential estimate is derived from bounded centered increments
and predictable upper bounds on their conditional second moments.
-/

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators

namespace Part2.Bernstein

/-- The radius `3/2` is important: with increments bounded by `c`, it permits
`t ≤ 3/(2c)` and hence the conservative linear Bernstein term `2cL/3`. -/
lemma exp_le_quadratic {x : ℝ} (hx : |x| ≤ 3 / 2) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hc : ‖(x : ℂ)‖ / (2 + 1 : ℕ) ≤ (1 / 2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    norm_num
    linarith
  have h := Complex.exp_bound' (n := 2) hc
  have hr : |Real.exp x - (1 + x)| ≤ x ^ 2 := by
    norm_num [Finset.sum_range_succ] at h
    have hr' : ‖((Real.exp x - (1 + x) : ℝ) : ℂ)‖ ≤ x ^ 2 := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one,
        Complex.ofReal_exp] using h
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hr'
  have := (abs_le.mp hr).2
  linarith

section Conditional

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] {m : MeasurableSpace Ω}

/-- Restricted-parameter conditional Bernstein MGF, derived from boundedness,
conditional centering, and an upper bound on the conditional second moment. -/
theorem conditional_mgf {X V : Ω → ℝ} {c t : ℝ} (hm : m ≤ m₀)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hsmall : t * c ≤ 3 / 2)
    (hXm : AEStronglyMeasurable[m₀] X μ) (hX : ∀ᵐ ω ∂μ, |X ω| ≤ c)
    (hmean : μ[X | m] =ᵐ[μ] fun _ => 0)
    (hvar : μ[fun ω => (X ω) ^ 2 | m] ≤ᵐ[μ] V) :
    μ[fun ω => Real.exp (t * X ω) | m] ≤ᵐ[μ]
      fun ω => Real.exp (t ^ 2 * V ω) := by
  have hXi : Integrable X μ := (integrable_const c).mono' hXm (by
    simpa only [Real.norm_eq_abs] using hX)
  have hXsq : ∀ᵐ ω ∂μ, (X ω) ^ 2 ≤ c ^ 2 := hX.mono fun ω hω => by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (X ω)) hc).2 hω
  have hX2i : Integrable (fun ω => (X ω) ^ 2) μ :=
    (integrable_const (c ^ 2)).mono' (hXm.pow 2) (by
      filter_upwards [hXsq] with ω hω
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω))] using hω)
  have hEi : Integrable (fun ω => Real.exp (t * X ω)) μ :=
    (integrable_const (Real.exp (t * c))).mono'
      (Real.continuous_exp.comp_aestronglyMeasurable (hXm.const_mul t)) (by
        filter_upwards [hX] with ω hω
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hω) ht))
  have h1i : Integrable (fun ω => 1 + t * X ω) μ :=
    (integrable_const (1 : ℝ)).add (hXi.const_mul t)
  have hPi : Integrable (fun ω => 1 + t * X ω + t ^ 2 * (X ω) ^ 2) μ :=
    h1i.add (hX2i.const_mul (t ^ 2))
  have hmono := condExp_mono (m := m) hEi hPi (hX.mono fun ω hω => by
    have hscaled : |t * X ω| ≤ 3 / 2 := by
      rw [abs_mul, abs_of_nonneg ht]
      exact (mul_le_mul_of_nonneg_left hω ht).trans hsmall
    simpa only [mul_pow] using exp_le_quadratic hscaled)
  have hsum1 := condExp_add (integrable_const (1 : ℝ)) (hXi.const_mul t) m
  have hsum2 := condExp_add h1i (hX2i.const_mul (t ^ 2)) m
  have hmul1 := condExp_smul (μ := μ) t X m
  have hmul2 := condExp_smul (μ := μ) (t ^ 2) (fun ω => (X ω) ^ 2) m
  filter_upwards [hmono, hsum1, hsum2, hmul1, hmul2, hmean, hvar] with
    ω hω hs1 hs2 hm1 hm2 hzero hv
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const hm] at hs1 hs2 hm1 hm2
  change (μ[fun ω => 1 + t * X ω | m]) ω =
    1 + (μ[fun ω => t * X ω | m]) ω at hs1
  change (μ[fun ω => 1 + t * X ω + t ^ 2 * (X ω) ^ 2 | m]) ω =
    (μ[fun ω => 1 + t * X ω | m]) ω +
      (μ[fun ω => t ^ 2 * (X ω) ^ 2 | m]) ω at hs2
  change (μ[fun ω => t * X ω | m]) ω = t * (μ[X | m]) ω at hm1
  change (μ[fun ω => t ^ 2 * (X ω) ^ 2 | m]) ω =
    t ^ 2 * (μ[fun ω => (X ω) ^ 2 | m]) ω at hm2
  calc
    _ ≤ (μ[fun ω => 1 + t * X ω + t ^ 2 * (X ω) ^ 2 | m]) ω := hω
    _ = 1 + t ^ 2 * (μ[fun ω => (X ω) ^ 2 | m]) ω := by
      rw [hs2, hs1, hm1, hm2, hzero, mul_zero, add_zero]
    _ ≤ 1 + t ^ 2 * V ω := by gcongr
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (t ^ 2 * V ω)

end Conditional

section Process

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
  {ℱ : Filtration ℕ m₀} {X V : ℕ → Ω → ℝ} {c : ℝ}

/-- Raw martingale-difference hypotheses. `V n` is a predictable nonnegative
upper bound on the conditional second moment, not an exponential-moment bound.
No independence between different increments is required. -/
structure BoundedIncrements (ℱ : Filtration ℕ m₀) (μ : Measure Ω)
    (X V : ℕ → Ω → ℝ) (c : ℝ) : Prop where
  bound_nonneg : 0 ≤ c
  increment_measurable : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n)
  variance_measurable : ∀ n, StronglyMeasurable[ℱ n] (V n)
  bound : ∀ n ω, |X n ω| ≤ c
  variance_nonneg : ∀ n ω, 0 ≤ V n ω
  centered : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ => 0
  second_moment : ∀ n, μ[fun ω => (X n ω) ^ 2 | ℱ n] ≤ᵐ[μ] V n

def sumProcess (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

noncomputable def exponentialProcess (X V : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (t * sumProcess X n ω - t ^ 2 * sumProcess V n ω)

lemma exponentialProcess_pos (t : ℝ) (n : ℕ) (ω : Ω) :
    0 < exponentialProcess X V t n ω := Real.exp_pos _

lemma exponentialProcess_zero (t : ℝ) :
    exponentialProcess X V t 0 = fun _ => 1 := by
  funext ω
  simp [exponentialProcess, sumProcess]

lemma exponentialProcess_succ (t : ℝ) (n : ℕ) (ω : Ω) :
    exponentialProcess X V t (n + 1) ω = exponentialProcess X V t n ω *
      Real.exp (t * X n ω - t ^ 2 * V n ω) := by
  simp only [exponentialProcess, sumProcess, Finset.sum_range_succ, ← Real.exp_add]
  congr 1
  ring

lemma exponentialProcess_adapted (h : BoundedIncrements ℱ μ X V c) (t : ℝ) :
    Adapted ℱ (exponentialProcess X V t) := by
  intro n
  have hXm : StronglyMeasurable[ℱ n] (sumProcess X n) :=
    (Finset.range n).stronglyMeasurable_fun_sum fun i hi =>
      (h.increment_measurable i).mono (ℱ.mono (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)))
  have hVm : StronglyMeasurable[ℱ n] (sumProcess V n) :=
    (Finset.range n).stronglyMeasurable_fun_sum fun i hi =>
      (h.variance_measurable i).mono (ℱ.mono (Finset.mem_range.mp hi).le)
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((hXm.const_mul t).sub (hVm.const_mul (t ^ 2)))

lemma exponentialProcess_bound (h : BoundedIncrements ℱ μ X V c)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (ω : Ω) :
    exponentialProcess X V t n ω ≤ Real.exp (t * ((n : ℝ) * c)) := by
  have hXS : sumProcess X n ω ≤ (n : ℝ) * c := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, c := Finset.sum_le_sum fun i _ =>
        (le_abs_self _).trans (h.bound i ω)
      _ = _ := by simp
  have hVS : 0 ≤ sumProcess V n ω :=
    Finset.sum_nonneg fun i _ => h.variance_nonneg i ω
  apply Real.exp_le_exp.mpr
  exact (sub_le_self _ (mul_nonneg (sq_nonneg t) hVS)).trans
    (mul_le_mul_of_nonneg_left hXS ht)

lemma exponentialProcess_integrable [IsFiniteMeasure μ]
    (h : BoundedIncrements ℱ μ X V c) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Integrable (exponentialProcess X V t n) μ := by
  apply (integrable_const (Real.exp (t * ((n : ℝ) * c)))).mono'
    (((exponentialProcess_adapted h t n).mono (ℱ.le n)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_pos (exponentialProcess_pos t n ω)]
  exact exponentialProcess_bound h ht n ω

/-- The explicit cumulative exponential process is a genuine mathlib
supermartingale. Adaptedness and integrability are proved here, not assumed. -/
theorem exponential_supermartingale [IsFiniteMeasure μ]
    (h : BoundedIncrements ℱ μ X V c) {t : ℝ} (ht : 0 ≤ t)
    (hsmall : t * c ≤ 3 / 2) :
    Supermartingale (exponentialProcess X V t) ℱ μ := by
  apply supermartingale_nat (exponentialProcess_adapted h t)
    (exponentialProcess_integrable h ht)
  intro n
  let D : Ω → ℝ := fun ω => exponentialProcess X V t n ω * Real.exp (-(t ^ 2 * V n ω))
  have hDm : StronglyMeasurable[ℱ n] D :=
    (exponentialProcess_adapted h t n).mul
      (Real.continuous_exp.comp_stronglyMeasurable ((h.variance_measurable n).const_mul (t ^ 2)).neg)
  have heq : (fun ω => D ω * Real.exp (t * X n ω)) = exponentialProcess X V t (n + 1) := by
    funext ω
    rw [exponentialProcess_succ]
    dsimp [D]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hEi : Integrable (fun ω => Real.exp (t * X n ω)) μ :=
    (integrable_const (Real.exp (t * c))).mono'
      (Real.continuous_exp.comp_aestronglyMeasurable
        (((h.increment_measurable n).mono (ℱ.le (n + 1))).aestronglyMeasurable.const_mul t))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (h.bound n ω)) ht))
  have hprod : Integrable (fun ω => D ω * Real.exp (t * X n ω)) μ := by
    rw [heq]
    exact exponentialProcess_integrable h ht (n + 1)
  have hpull := condExp_mul_of_stronglyMeasurable_left hDm hprod hEi
  have hmgf := conditional_mgf (ℱ.le n) h.bound_nonneg ht hsmall
    (((h.increment_measurable n).mono (ℱ.le (n + 1))).aestronglyMeasurable)
    (Eventually.of_forall (h.bound n)) (h.centered n) (h.second_moment n)
  filter_upwards [hpull, hmgf] with ω hp hm
  rw [← heq]
  calc
    _ = D ω * (μ[fun ω => Real.exp (t * X n ω) | ℱ n]) ω := hp
    _ ≤ D ω * Real.exp (t ^ 2 * V n ω) :=
      mul_le_mul_of_nonneg_left hm
        (mul_nonneg (exponentialProcess_pos t n ω).le (Real.exp_pos _).le)
    _ = exponentialProcess X V t n ω := by
      dsimp [D]
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end Process

section Tail

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {X V : ℕ → Ω → ℝ} {c : ℝ}

/-- Fixed-time, fixed-variance exponential tail, derived from the original
bounded martingale-difference assumptions. The variance event is intersected
in the original space; the measure is never conditioned on that event. -/
theorem exponential_tail (h : BoundedIncrements ℱ μ X V c)
    {t : ℝ} (ht : 0 ≤ t) (hsmall : t * c ≤ 3 / 2) (n : ℕ) (s v : ℝ) :
    μ.real {ω | s ≤ sumProcess X n ω ∧ sumProcess V n ω ≤ v} ≤
      Real.exp (t ^ 2 * v - t * s) := by
  have hsm := exponential_supermartingale h ht hsmall
  have hmean : (∫ ω, exponentialProcess X V t n ω ∂μ) ≤ 1 := by
    calc
      _ = ∫ ω, (μ[exponentialProcess X V t n | ℱ 0]) ω ∂μ :=
        (integral_condExp (ℱ.le 0)).symm
      _ ≤ ∫ ω, exponentialProcess X V t 0 ω ∂μ :=
        integral_mono_ae integrable_condExp (hsm.2.2 0) (hsm.2.1 0 n (Nat.zero_le n))
      _ = 1 := by rw [exponentialProcess_zero]; simp
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => (exponentialProcess_pos t n ω).le)
    (hsm.2.2 n) (Real.exp (t * s - t ^ 2 * v))
  have htail : μ.real {ω | Real.exp (t * s - t ^ 2 * v) ≤ exponentialProcess X V t n ω} ≤
      Real.exp (t ^ 2 * v - t * s) := by
    have heq : t ^ 2 * v - t * s = -(t * s - t ^ 2 * v) := by ring
    rw [heq, Real.exp_neg, ← one_div]
    apply (le_div_iff₀ (Real.exp_pos _)).2
    simpa only [mul_comm] using hmarkov.trans hmean
  apply (measureReal_mono (μ := μ) (s₂ :=
    {ω | Real.exp (t * s - t ^ 2 * v) ≤ exponentialProcess X V t n ω}) ?_).trans htail
  intro ω hω
  apply Real.exp_le_exp.mpr
  have hx := mul_le_mul_of_nonneg_left hω.1 ht
  have hv := mul_le_mul_of_nonneg_left hω.2 (sq_nonneg t)
  linarith

end Tail

/-- A parameter choice avoiding division by `v`, including the zero-variance
case. It optimizes the restricted quadratic MGF sufficiently for the paper's
conservative Bernstein constants. -/
lemma bernstein_parameter {c v L : ℝ} (hc : 0 < c) (hv : 0 ≤ v) (hL : 0 < L) :
    let t := L / (Real.sqrt (v * L) + (2 * c / 3) * L)
    0 ≤ t ∧ t * c ≤ 3 / 2 ∧
      t ^ 2 * v - t * (2 * Real.sqrt (v * L) + (2 * c / 3) * L) ≤ -L := by
  let a := Real.sqrt (v * L)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = v * L := Real.sq_sqrt (mul_nonneg hv hL.le)
  have hd : 0 < a + (2 * c / 3) * L := by positivity
  let t := L / (a + (2 * c / 3) * L)
  change 0 ≤ t ∧ t * c ≤ 3 / 2 ∧
    t ^ 2 * v - t * (2 * a + (2 * c / 3) * L) ≤ -L
  have ht : 0 ≤ t := div_nonneg hL.le hd.le
  have hprod : t * (a + (2 * c / 3) * L) = L := div_mul_cancel₀ L hd.ne'
  have hsmall : t * c ≤ 3 / 2 := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hta : 0 ≤ t * a := mul_nonneg ht ha
  have htal : t * a ≤ L := by
    have := mul_nonneg ht (mul_nonneg (by positivity : 0 ≤ 2 * c / 3) hL.le)
    nlinarith [hprod]
  have hsq : (t * a) ^ 2 ≤ L * (t * a) := by
    nlinarith [mul_nonneg hta (sub_nonneg.mpr htal)]
  have hvar : t ^ 2 * v ≤ t * a := by
    have hid : (t * a) ^ 2 = (t ^ 2 * v) * L := by rw [mul_pow, ha2]; ring
    nlinarith
  exact ⟨ht, hsmall, by nlinarith [hprod]⟩

section BernsteinTail

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {X V : ℕ → Ω → ℝ} {c : ℝ}

/-- Finite-time martingale Bernstein/Freedman inequality with a fixed
predictable-variance threshold. This theorem assumes neither an MGF bound nor
a supermartingale: both are proved from `BoundedIncrements` above. -/
theorem bernstein_tail (h : BoundedIncrements ℱ μ X V c) (hc : 0 < c)
    (n : ℕ) {v L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    μ.real {ω | 2 * Real.sqrt (v * L) + (2 * c / 3) * L ≤ sumProcess X n ω ∧
      sumProcess V n ω ≤ v} ≤ Real.exp (-L) := by
  obtain ⟨ht, hsmall, hopt⟩ := bernstein_parameter hc hv hL
  exact (exponential_tail h ht hsmall n
    (2 * Real.sqrt (v * L) + (2 * c / 3) * L) v).trans (Real.exp_le_exp.mpr hopt)

lemma BoundedIncrements.neg (h : BoundedIncrements ℱ μ X V c) :
    BoundedIncrements ℱ μ (fun n ω => -X n ω) V c := by
  refine ⟨h.bound_nonneg, fun n => (h.increment_measurable n).neg,
    h.variance_measurable, ?_, h.variance_nonneg, ?_, ?_⟩
  · intro n ω
    simpa only [abs_neg] using h.bound n ω
  · intro n
    have hn := condExp_neg (μ := μ) (X n) (ℱ n)
    filter_upwards [hn, h.centered n] with ω hn hz
    simpa only [Pi.neg_apply, hz, neg_zero] using hn
  · intro n
    simpa only [neg_sq] using h.second_moment n

lemma sumProcess_neg (n : ℕ) (ω : Ω) :
    sumProcess (fun i ω => -X i ω) n ω = -sumProcess X n ω := by
  simp only [sumProcess, Finset.sum_neg_distrib]

lemma BoundedIncrements.const_mul (h : BoundedIncrements ℱ μ X V c)
    {a : ℝ} (ha : 0 ≤ a) :
    BoundedIncrements ℱ μ (fun n ω => a * X n ω)
      (fun n ω => a ^ 2 * V n ω) (a * c) := by
  refine ⟨mul_nonneg ha h.bound_nonneg,
    fun n => (h.increment_measurable n).const_mul a,
    fun n => (h.variance_measurable n).const_mul (a ^ 2), ?_, ?_, ?_, ?_⟩
  · intro n ω
    rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (h.bound n ω) ha
  · intro n ω
    exact mul_nonneg (sq_nonneg a) (h.variance_nonneg n ω)
  · intro n
    have hm := condExp_smul (μ := μ) a (X n) (ℱ n)
    filter_upwards [hm, h.centered n] with ω hm hz
    change (μ[fun ω => a * X n ω | ℱ n]) ω = a * (μ[X n | ℱ n]) ω at hm
    simpa only [hz, mul_zero] using hm
  · intro n
    have hm := condExp_smul (μ := μ) (a ^ 2) (fun ω => (X n ω) ^ 2) (ℱ n)
    filter_upwards [hm, h.second_moment n] with ω hm hv
    change (μ[fun ω => a ^ 2 * (X n ω) ^ 2 | ℱ n]) ω =
      a ^ 2 * (μ[fun ω => (X n ω) ^ 2 | ℱ n]) ω at hm
    simpa only [mul_pow] using hm.le.trans (mul_le_mul_of_nonneg_left hv (sq_nonneg a))

lemma sumProcess_const_mul (a : ℝ) (n : ℕ) (ω : Ω) :
    sumProcess (fun i ω => a * X i ω) n ω = a * sumProcess X n ω := by
  simp only [sumProcess, Finset.mul_sum]

theorem bernstein_two_sided (h : BoundedIncrements ℱ μ X V c) (hc : 0 < c)
    (n : ℕ) {v L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    μ.real {ω | 2 * Real.sqrt (v * L) + (2 * c / 3) * L ≤ |sumProcess X n ω| ∧
      sumProcess V n ω ≤ v} ≤ 2 * Real.exp (-L) := by
  let s := 2 * Real.sqrt (v * L) + (2 * c / 3) * L
  let Epos := {ω | s ≤ sumProcess X n ω ∧ sumProcess V n ω ≤ v}
  let Eneg := {ω | s ≤ -sumProcess X n ω ∧ sumProcess V n ω ≤ v}
  have hpos : μ.real Epos ≤ Real.exp (-L) := bernstein_tail h hc n hv hL
  have hneg : μ.real Eneg ≤ Real.exp (-L) := by
    simpa only [Eneg, sumProcess_neg] using bernstein_tail h.neg hc n hv hL
  have hsub : {ω | s ≤ |sumProcess X n ω| ∧ sumProcess V n ω ≤ v} ⊆ Epos ∪ Eneg := by
    intro ω hω
    by_cases hz : 0 ≤ sumProcess X n ω
    · exact Or.inl ⟨by simpa only [abs_of_nonneg hz] using hω.1, hω.2⟩
    · exact Or.inr ⟨by simpa only [abs_of_neg (lt_of_not_ge hz)] using hω.1, hω.2⟩
  exact (measureReal_mono hsub).trans ((measureReal_union_le Epos Eneg).trans (by linarith))

/-- Union over any finite collection of times and deterministic variance bins.
The two sides are paid exactly once for each time/bin pair. -/
theorem bernstein_time_bins (h : BoundedIncrements ℱ μ X V c) (hc : 0 < c)
    (times bins : Finset ℕ) (b : ℕ → ℝ) (hb : ∀ j ∈ bins, 0 ≤ b j)
    {L : ℝ} (hL : 0 < L) :
    μ.real (⋃ n ∈ times, ⋃ j ∈ bins,
      {ω | 2 * Real.sqrt (b j * L) + (2 * c / 3) * L ≤ |sumProcess X n ω| ∧
        sumProcess V n ω ≤ b j}) ≤
      (times.card : ℝ) * (bins.card : ℝ) * (2 * Real.exp (-L)) := by
  calc
    _ ≤ ∑ n ∈ times, μ.real (⋃ j ∈ bins,
        {ω | 2 * Real.sqrt (b j * L) + (2 * c / 3) * L ≤ |sumProcess X n ω| ∧
          sumProcess V n ω ≤ b j}) := measureReal_biUnion_finset_le times _
    _ ≤ ∑ n ∈ times, ∑ j ∈ bins, (2 * Real.exp (-L)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact (measureReal_biUnion_finset_le bins _).trans
        (Finset.sum_le_sum fun j hj => bernstein_two_sided h hc n (hb j hj) hL)
    _ = _ := by simp; ring

/-- Integer variance peeling plus a finite time union. When each predictable
variance increment is at most one, the failure bound is `2(T+1)^2 exp(-L)`.
This is the probability step used by the paper after normalizing by H. -/
theorem bernstein_uniform (h : BoundedIncrements ℱ μ X V c) (hc : 0 < c)
    (hV1 : ∀ i ω, V i ω ≤ 1) (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ T,
      2 * Real.sqrt ((1 + sumProcess V n ω) * L) + (2 * c / 3) * L ≤
        |sumProcess X n ω|} ≤ 2 * ((T + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-L) := by
  have hU := bernstein_time_bins h hc (Finset.range (T + 1)) (Finset.range (T + 1))
    (fun j => (j : ℝ) + 1) (fun j _ => by positivity) hL
  have hsub : {ω | ∃ n ≤ T,
      2 * Real.sqrt ((1 + sumProcess V n ω) * L) + (2 * c / 3) * L ≤ |sumProcess X n ω|} ⊆
      ⋃ n ∈ Finset.range (T + 1), ⋃ j ∈ Finset.range (T + 1),
        {ω | 2 * Real.sqrt (((j : ℝ) + 1) * L) + (2 * c / 3) * L ≤ |sumProcess X n ω| ∧
          sumProcess V n ω ≤ (j : ℝ) + 1} := by
    intro ω hω
    obtain ⟨n, hn, htail⟩ := hω
    have hV0 : 0 ≤ sumProcess V n ω :=
      Finset.sum_nonneg fun i _ => h.variance_nonneg i ω
    have hVT : sumProcess V n ω ≤ (T : ℝ) := by
      calc
        _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hV1 i ω
        _ = (n : ℝ) := by simp
        _ ≤ _ := by exact_mod_cast hn
    let j := ⌊sumProcess V n ω⌋₊
    have hjT : j ≤ T := Nat.floor_le_of_le hVT
    have hjlo : (j : ℝ) ≤ sumProcess V n ω := Nat.floor_le hV0
    have hjhi : sumProcess V n ω ≤ (j : ℝ) + 1 := (Nat.lt_floor_add_one _).le
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn),
      j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjT), ?_, hjhi⟩
    have hsqrt : Real.sqrt (((j : ℝ) + 1) * L) ≤ Real.sqrt ((1 + sumProcess V n ω) * L) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (by linarith) hL.le)
    linarith
  simp only [Finset.card_range] at hU
  exact (measureReal_mono hsub).trans (by nlinarith [hU])

/-- The exact conservative confidence radius used in COMMON_DRIFT and
MULTIARM_PROGRESS. The input is a bounded centered process with |X|≤2H and
conditional second moment bounded by H²q; no pre-proved concentration is
assumed. Per-step q≤1 covers the paper's stronger q≤1/4 condition. -/
theorem paper_uniform {H : ℝ} (hH : 0 < H) {q : ℕ → Ω → ℝ}
    (h : BoundedIncrements ℱ μ X (fun i ω => H ^ 2 * q i ω) (2 * H))
    (hq : ∀ i ω, q i ω ≤ 1) (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ T,
      2 * H * Real.sqrt ((1 + sumProcess q n ω) * L) + (4 / 3) * H * L ≤
        |sumProcess X n ω|} ≤ 2 * ((T + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-L) := by
  have hnorm := h.const_mul (a := H⁻¹) (inv_nonneg.mpr hH.le)
  have hc : H⁻¹ * (2 * H) = 2 := by field_simp
  have hv : (fun i ω => (H⁻¹) ^ 2 * (H ^ 2 * q i ω)) = q := by
    funext i ω
    field_simp
  rw [hc, hv] at hnorm
  have hU := bernstein_uniform hnorm (by norm_num : (0 : ℝ) < 2) hq T hL
  have hsub : {ω | ∃ n ≤ T,
      2 * H * Real.sqrt ((1 + sumProcess q n ω) * L) + (4 / 3) * H * L ≤ |sumProcess X n ω|} ⊆
      {ω | ∃ n ≤ T,
        2 * Real.sqrt ((1 + sumProcess q n ω) * L) + (2 * (2 : ℝ) / 3) * L ≤
          |sumProcess (fun i ω => H⁻¹ * X i ω) n ω|} := by
    intro ω hω
    obtain ⟨n, hn, hr⟩ := hω
    refine ⟨n, hn, ?_⟩
    rw [sumProcess_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hH)]
    have hscaled := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hH.le)
    have heq : H⁻¹ * (2 * H * Real.sqrt ((1 + sumProcess q n ω) * L) + (4 / 3) * H * L) =
        2 * Real.sqrt ((1 + sumProcess q n ω) * L) + (2 * (2 : ℝ) / 3) * L := by
      field_simp
      ring
    rwa [heq] at hscaled
  exact (measureReal_mono hsub).trans hU

/-- Simultaneous confidence over an arbitrary finite family of processes,
e.g. all unordered arm pairs. Their samples may be arbitrarily dependent. -/
theorem paper_uniform_family {ι : Type*} [Fintype ι]
    {H : ℝ} (hH : 0 < H) (Y q : ι → ℕ → Ω → ℝ)
    (h : ∀ a, BoundedIncrements ℱ μ (Y a) (fun i ω => H ^ 2 * q a i ω) (2 * H))
    (hq : ∀ a i ω, q a i ω ≤ 1) (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ a, ∃ n ≤ T,
      2 * H * Real.sqrt ((1 + sumProcess (q a) n ω) * L) + (4 / 3) * H * L ≤
        |sumProcess (Y a) n ω|} ≤
      (Fintype.card ι : ℝ) * (2 * ((T + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-L)) := by
  have hset : {ω | ∃ a, ∃ n ≤ T,
      2 * H * Real.sqrt ((1 + sumProcess (q a) n ω) * L) + (4 / 3) * H * L ≤
        |sumProcess (Y a) n ω|} =
      ⋃ a, {ω | ∃ n ≤ T,
        2 * H * Real.sqrt ((1 + sumProcess (q a) n ω) * L) + (4 / 3) * H * L ≤
          |sumProcess (Y a) n ω|} := by ext ω; simp
  rw [hset]
  calc
    _ ≤ ∑ a, μ.real {ω | ∃ n ≤ T,
        2 * H * Real.sqrt ((1 + sumProcess (q a) n ω) * L) + (4 / 3) * H * L ≤
          |sumProcess (Y a) n ω|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : ι, (2 * ((T + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-L)) :=
      Finset.sum_le_sum fun a _ => paper_uniform hH (h a) (hq a) T hL
    _ = _ := by simp

/-- The paper's logarithmic allocation gives total confidence failure at most
δ/4, simultaneously for the complete finite process family and all n≤T. -/
theorem paper_confidence {ι : Type*} [Fintype ι] (hcard : 0 < Fintype.card ι)
    {H : ℝ} (hH : 0 < H) (Y q : ι → ℕ → Ω → ℝ)
    (h : ∀ a, BoundedIncrements ℱ μ (Y a) (fun i ω => H ^ 2 * q a i ω) (2 * H))
    (hq : ∀ a i ω, q a i ω ≤ 1) (T : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let L := Real.log (8 * (Fintype.card ι : ℝ) * ((T + 1 : ℕ) : ℝ) ^ 2 / δ)
    μ.real {ω | ∃ a, ∃ n ≤ T,
      2 * H * Real.sqrt ((1 + sumProcess (q a) n ω) * L) + (4 / 3) * H * L ≤
        |sumProcess (Y a) n ω|} ≤ δ / 4 := by
  let A := 8 * (Fintype.card ι : ℝ) * ((T + 1 : ℕ) : ℝ) ^ 2 / δ
  have hm : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hT : (1 : ℝ) ≤ ((T + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le T)
  have hTsq : 1 ≤ ((T + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hmT : 1 ≤ (Fintype.card ι : ℝ) * ((T + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hTsq)]
  have hA : 1 < A := (lt_div_iff₀ hδ).2 (by nlinarith)
  have hU := paper_uniform_family hH Y q h hq T (Real.log_pos hA)
  have heq : (Fintype.card ι : ℝ) *
      (2 * ((T + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.log A)) = δ / 4 := by
    rw [Real.exp_neg, Real.exp_log (by linarith : 0 < A)]
    dsimp [A]
    field_simp
    <;> ring
  exact hU.trans_eq heq

end BernsteinTail

end Part2.Bernstein

