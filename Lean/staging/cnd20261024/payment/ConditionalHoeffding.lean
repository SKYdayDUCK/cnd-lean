import staging.cnd20261024.payment.ObservablePayment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Probability.Moments.SubGaussian

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

namespace Part2.CNDPayment

/-- The two-endpoint chord, retaining its affine centered term. -/
theorem exp_symmetric_chord {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B) (t : ℝ) :
    Real.exp (t * x) ≤
      (Real.exp (t * B) + Real.exp (-(t * B))) / 2 +
        ((Real.exp (t * B) - Real.exp (-(t * B))) / (2 * B)) * x := by
  have hx' := abs_le.mp hx
  have h := convexOn_exp.2 (Set.mem_univ (-(t * B))) (Set.mem_univ (t * B))
    (show 0 ≤ (B - x) / (2 * B) by exact div_nonneg (by linarith [hx'.2]) (by positivity))
    (show 0 ≤ (B + x) / (2 * B) by exact div_nonneg (by linarith [hx'.1]) (by positivity))
    (show (B - x) / (2 * B) + (B + x) / (2 * B) = 1 by field_simp; ring)
  have heq : ((B - x) / (2 * B)) • (-(t * B)) + ((B + x) / (2 * B)) • (t * B) = t * x := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [heq] at h
  convert h using 1
  simp only [smul_eq_mul]
  field_simp
  ring

/-- Conditional Hoeffding on any original probability space. The proof uses
an affine exponential chord and conditional centering, with no independent
encoder hypothesis or regular-conditional-law assumption. -/
theorem conditional_hoeffding
    {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) (X : Ω → ℝ)
    (hXm : Measurable[m₀] X) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω, |X ω| ≤ B)
    (hc : μ[X | m] =ᵐ[μ] fun _ => 0) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) μ ∧
      μ[fun ω => Real.exp (t * X ω) | m] ≤ᵐ[μ] fun _ => Real.exp (B ^ 2 * t ^ 2 / 2) := by
  have hXi : Integrable X μ := PairConfidence.bounded_integrable (m₀ := m₀) hXm hb
  have hEi : Integrable (fun ω => Real.exp (t * X ω)) μ :=
    integrable_exp_mul_of_mem_Icc hXm.aemeasurable (ae_of_all _ fun ω => abs_le.mp (hb ω))
  refine ⟨hEi, ?_⟩
  rcases eq_or_lt_of_le hB with h0 | hpos
  · have hx : X = fun _ => 0 := by
      funext ω
      exact abs_eq_zero.mp (le_antisymm (by simpa only [← h0] using hb ω) (abs_nonneg _))
    subst B
    filter_upwards [] with ω
    simpa [hx] using le_of_eq (congrFun (condExp_const (μ := μ) hm (1 : ℝ)) ω)
  · let c0 : ℝ := (Real.exp (t * B) + Real.exp (-(t * B))) / 2
    let c1 : ℝ := (Real.exp (t * B) - Real.exp (-(t * B))) / (2 * B)
    have henv : Integrable (fun ω => c0 + c1 * X ω) μ := (integrable_const c0).add (hXi.const_mul c1)
    have hmono := condExp_mono (m := m) hEi henv (ae_of_all _ fun ω => exp_symmetric_chord hpos (hb ω) t)
    have hadd := condExp_add (integrable_const c0) (hXi.const_mul c1) m
    have hmul := condExp_smul (μ := μ) c1 X m
    have hmul' : μ[fun ω => c1 * X ω | m] =ᵐ[μ] fun _ => 0 := by
      have hf : (fun ω => c1 * X ω) = c1 • X := rfl
      rw [hf]
      filter_upwards [hmul.trans (hc.const_smul c1)] with ω hω
      simpa only [Pi.smul_apply, smul_eq_mul, mul_zero] using hω
    have hconstant : μ[fun ω => c0 + c1 * X ω | m] =ᵐ[μ] fun _ => c0 := by
      filter_upwards [hadd, hmul'] with ω ha hz
      simpa only [Pi.add_apply, condExp_const hm c0, hz, add_zero] using ha
    filter_upwards [hmono, hconstant] with ω hle heq
    rw [heq] at hle
    apply hle.trans
    have hcosh := Real.cosh_le_exp_half_sq (t * B)
    simpa only [c0, Real.cosh_eq, mul_pow, mul_comm (t ^ 2) (B ^ 2)] using hcosh

end Part2.CNDPayment
