import staging.cnd20261024.probability.FiniteVille

/-! Bernstein's sharp quadratic coefficient on the original probability space.
The exponential-series proof adapts the locked mathlib `Complex.exp_bound'`
argument, keeping the geometric denominator instead of replacing it by two. -/

open MeasureTheory Filter Finset CauSeq IsAbsoluteValue
open scoped ProbabilityTheory BigOperators

set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SharpBernstein

lemma finite_geometric_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, r ^ i) ≤ 1 / (1 - r) := by
  have hid : (∑ i ∈ Finset.range k, r ^ i) * (1 - r) = 1 - r ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring
  apply (le_div_iff₀ (by linarith : 0 < 1 - r)).2
  rw [hid]
  exact sub_le_self _ (pow_nonneg hr0 _)

/-- The factorial-geometric bound behind Bernstein, with its denominator
retained. This is analysis, not a probabilistic assumption. -/
lemma complex_exp_remainder {x : ℂ} (hx : ‖x‖ < 3) :
    ‖Complex.exp x - (1 + x)‖ ≤ ‖x‖ ^ 2 / 2 * (1 / (1 - ‖x‖ / 3)) := by
  rw [← lim_const (abv := norm) (1 + x), Complex.exp,
    sub_eq_add_neg, ← lim_neg, lim_add, ← Complex.lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨2, fun j hj => ?_⟩)
  change ‖(∑ m ∈ range j, x ^ m / m.factorial) - (1 + x)‖ ≤ _
  have hsum : (∑ m ∈ range 2, x ^ m / m.factorial) = 1 + x := by
    norm_num [Finset.sum_range_succ]
  rw [← hsum]
  let k := j - 2
  have hj' : j = 2 + k := (Nat.add_sub_of_le hj).symm
  rw [hj', sum_range_add_sub_sum_range]
  calc
    _ ≤ ∑ i ∈ range k, ‖x ^ (2 + i) / ((2 + i).factorial : ℂ)‖ :=
      IsAbsoluteValue.abv_sum _ _ _
    _ = ∑ i ∈ range k, ‖x‖ ^ (2 + i) / ((2 + i).factorial : ℝ) := by
      simp [Complex.norm_pow, norm_natCast]
    _ ≤ ∑ i ∈ range k, ‖x‖ ^ (2 + i) / (2 * (3 : ℝ) ^ i) := by
      apply Finset.sum_le_sum
      intro i _
      apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg x) _) (by positivity)
      have hf := @Nat.factorial_mul_pow_le_factorial 2 i
      norm_num at hf
      exact_mod_cast hf
    _ = ‖x‖ ^ 2 / 2 * ∑ i ∈ range k, (‖x‖ / 3) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add, div_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (finite_geometric_bound (div_nonneg (norm_nonneg x) (by norm_num)) (by linarith) k)
      (by positivity)

lemma exp_quadratic {x r : ℝ} (hr : r < 3) (hx : |x| ≤ r) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - r / 3)) := by
  have hxa : |x| < 3 := hx.trans_lt hr
  have hc := complex_exp_remainder (x := (x : ℂ)) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hxa)
  have hre : |Real.exp x - (1 + x)| ≤ x ^ 2 / 2 * (1 / (1 - |x| / 3)) := by
    have he : ‖((Real.exp x - (1 + x) : ℝ) : ℂ)‖ ≤ |x| ^ 2 / 2 * (1 / (1 - |x| / 3)) := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one,
        Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs] using hc
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using he
  have hdenx : 0 < 2 * (1 - |x| / 3) := by linarith
  have hdenr : 0 < 2 * (1 - r / 3) := by linarith
  have hfrac : x ^ 2 / (2 * (1 - |x| / 3)) ≤ x ^ 2 / (2 * (1 - r / 3)) :=
    div_le_div_of_nonneg_left (sq_nonneg x) hdenr (by linarith)
  have hupper := (abs_le.mp hre).2
  have heq : x ^ 2 / 2 * (1 / (1 - |x| / 3)) = x ^ 2 / (2 * (1 - |x| / 3)) := by
    rw [div_mul_div_comm, mul_one]
  rw [heq] at hupper
  linarith


noncomputable def coefficient (c t : ℝ) : ℝ := t ^ 2 / (2 * (1 - t * c / 3))

lemma coefficient_nonneg {c t : ℝ} (hsmall : t * c < 3) : 0 ≤ coefficient c t := by
  apply div_nonneg (sq_nonneg t)
  linarith

section Conditional

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] {m : MeasurableSpace Ω}

/-- Restricted-parameter conditional Bernstein MGF, derived from boundedness,
conditional centering, and an upper bound on the conditional second moment. -/
theorem conditional_mgf {X V : Ω → ℝ} {c t : ℝ} (hm : m ≤ m₀)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hsmall : t * c < 3)
    (hXm : AEStronglyMeasurable[m₀] X μ) (hX : ∀ᵐ ω ∂μ, |X ω| ≤ c)
    (hmean : μ[X | m] =ᵐ[μ] fun _ => 0)
    (hvar : μ[fun ω => (X ω) ^ 2 | m] ≤ᵐ[μ] V) :
    μ[fun ω => Real.exp (t * X ω) | m] ≤ᵐ[μ]
      fun ω => Real.exp (coefficient c t * V ω) := by
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
  have hPi : Integrable (fun ω => 1 + t * X ω + coefficient c t * (X ω) ^ 2) μ :=
    h1i.add (hX2i.const_mul (coefficient c t))
  have hmono := condExp_mono (m := m) hEi hPi (hX.mono fun ω hω => by
    have hscaled : |t * X ω| ≤ t * c := by
      rw [abs_mul, abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left hω ht
    simpa only [coefficient, mul_pow, div_mul_eq_mul_div] using exp_quadratic hsmall hscaled)
  have hsum1 := condExp_add (integrable_const (1 : ℝ)) (hXi.const_mul t) m
  have hsum2 := condExp_add h1i (hX2i.const_mul (coefficient c t)) m
  have hmul1 := condExp_smul (μ := μ) t X m
  have hmul2 := condExp_smul (μ := μ) (coefficient c t) (fun ω => (X ω) ^ 2) m
  filter_upwards [hmono, hsum1, hsum2, hmul1, hmul2, hmean, hvar] with
    ω hω hs1 hs2 hm1 hm2 hzero hv
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const hm] at hs1 hs2 hm1 hm2
  change (μ[fun ω => 1 + t * X ω | m]) ω =
    1 + (μ[fun ω => t * X ω | m]) ω at hs1
  change (μ[fun ω => 1 + t * X ω + coefficient c t * (X ω) ^ 2 | m]) ω =
    (μ[fun ω => 1 + t * X ω | m]) ω +
      (μ[fun ω => coefficient c t * (X ω) ^ 2 | m]) ω at hs2
  change (μ[fun ω => t * X ω | m]) ω = t * (μ[X | m]) ω at hm1
  change (μ[fun ω => coefficient c t * (X ω) ^ 2 | m]) ω =
    coefficient c t * (μ[fun ω => (X ω) ^ 2 | m]) ω at hm2
  calc
    _ ≤ (μ[fun ω => 1 + t * X ω + coefficient c t * (X ω) ^ 2 | m]) ω := hω
    _ = 1 + coefficient c t * (μ[fun ω => (X ω) ^ 2 | m]) ω := by
      rw [hs2, hs1, hm1, hm2, hzero, mul_zero, add_zero]
    _ ≤ 1 + coefficient c t * V ω :=
      add_le_add_left (mul_le_mul_of_nonneg_left hv (coefficient_nonneg hsmall)) 1
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (coefficient c t * V ω)

end Conditional

section Process

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
  {ℱ : Filtration ℕ m₀} {X V : ℕ → Ω → ℝ} {c : ℝ}

noncomputable def exponentialProcess (X V : ℕ → Ω → ℝ) (c t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (t * Bernstein.sumProcess X n ω - coefficient c t * Bernstein.sumProcess V n ω)

lemma exponentialProcess_pos (t : ℝ) (n : ℕ) (ω : Ω) :
    0 < exponentialProcess X V c t n ω := Real.exp_pos _

lemma exponentialProcess_zero (t : ℝ) :
    exponentialProcess X V c t 0 = fun _ => 1 := by
  funext ω
  simp [exponentialProcess, Bernstein.sumProcess]

lemma exponentialProcess_succ (t : ℝ) (n : ℕ) (ω : Ω) :
    exponentialProcess X V c t (n + 1) ω = exponentialProcess X V c t n ω *
      Real.exp (t * X n ω - coefficient c t * V n ω) := by
  simp only [exponentialProcess, Bernstein.sumProcess, Finset.sum_range_succ, ← Real.exp_add]
  congr 1
  ring

lemma exponentialProcess_adapted (h : Bernstein.BoundedIncrements ℱ μ X V c) (t : ℝ) :
    Adapted ℱ (exponentialProcess X V c t) := by
  intro n
  have hXm : StronglyMeasurable[ℱ n] (Bernstein.sumProcess X n) :=
    (Finset.range n).stronglyMeasurable_fun_sum fun i hi =>
      (h.increment_measurable i).mono (ℱ.mono (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)))
  have hVm : StronglyMeasurable[ℱ n] (Bernstein.sumProcess V n) :=
    (Finset.range n).stronglyMeasurable_fun_sum fun i hi =>
      (h.variance_measurable i).mono (ℱ.mono (Finset.mem_range.mp hi).le)
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((hXm.const_mul t).sub (hVm.const_mul (coefficient c t)))

lemma exponentialProcess_bound (h : Bernstein.BoundedIncrements ℱ μ X V c)
    {t : ℝ} (ht : 0 ≤ t) (hsmall : t * c < 3) (n : ℕ) (ω : Ω) :
    exponentialProcess X V c t n ω ≤ Real.exp (t * ((n : ℝ) * c)) := by
  have hXS : Bernstein.sumProcess X n ω ≤ (n : ℝ) * c := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, c := Finset.sum_le_sum fun i _ =>
        (le_abs_self _).trans (h.bound i ω)
      _ = _ := by simp
  have hVS : 0 ≤ Bernstein.sumProcess V n ω :=
    Finset.sum_nonneg fun i _ => h.variance_nonneg i ω
  apply Real.exp_le_exp.mpr
  exact (sub_le_self _ (mul_nonneg (coefficient_nonneg hsmall) hVS)).trans
    (mul_le_mul_of_nonneg_left hXS ht)

lemma exponentialProcess_integrable [IsFiniteMeasure μ]
    (h : Bernstein.BoundedIncrements ℱ μ X V c) {t : ℝ} (ht : 0 ≤ t) (hsmall : t * c < 3) (n : ℕ) :
    Integrable (exponentialProcess X V c t n) μ := by
  apply (integrable_const (Real.exp (t * ((n : ℝ) * c)))).mono'
    (((exponentialProcess_adapted h t n).mono (ℱ.le n)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_pos (exponentialProcess_pos (c := c) t n ω)]
  exact exponentialProcess_bound h ht hsmall n ω

/-- The explicit cumulative exponential process is a genuine mathlib
supermartingale. Adaptedness and integrability are proved here, not assumed. -/
theorem exponential_supermartingale [IsFiniteMeasure μ]
    (h : Bernstein.BoundedIncrements ℱ μ X V c) {t : ℝ} (ht : 0 ≤ t)
    (hsmall : t * c < 3) :
    Supermartingale (exponentialProcess X V c t) ℱ μ := by
  apply supermartingale_nat (exponentialProcess_adapted h t)
    (exponentialProcess_integrable h ht hsmall)
  intro n
  let D : Ω → ℝ := fun ω => exponentialProcess X V c t n ω * Real.exp (-(coefficient c t * V n ω))
  have hDm : StronglyMeasurable[ℱ n] D :=
    (exponentialProcess_adapted h t n).mul
      (Real.continuous_exp.comp_stronglyMeasurable ((h.variance_measurable n).const_mul (coefficient c t)).neg)
  have heq : (fun ω => D ω * Real.exp (t * X n ω)) = exponentialProcess X V c t (n + 1) := by
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
    exact exponentialProcess_integrable h ht hsmall (n + 1)
  have hpull := condExp_mul_of_stronglyMeasurable_left hDm hprod hEi
  have hmgf := conditional_mgf (ℱ.le n) h.bound_nonneg ht hsmall
    (((h.increment_measurable n).mono (ℱ.le (n + 1))).aestronglyMeasurable)
    (Eventually.of_forall (h.bound n)) (h.centered n) (h.second_moment n)
  filter_upwards [hpull, hmgf] with ω hp hm
  rw [← heq]
  calc
    _ = D ω * (μ[fun ω => Real.exp (t * X n ω) | ℱ n]) ω := hp
    _ ≤ D ω * Real.exp (coefficient c t * V n ω) :=
      mul_le_mul_of_nonneg_left hm
        (mul_nonneg (exponentialProcess_pos (c := c) t n ω).le (Real.exp_pos _).le)
    _ = exponentialProcess X V c t n ω := by
      dsimp [D]
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end Process

end Part2.CNDProbability.SharpBernstein
