import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Predictable bounded coefficients in conditional exponential moments

All expectations live on the original measure space. Constant-parameter
conditional bounds are extended by bounded simple-function approximation.
There is no regular conditional distribution or independence assumption.
-/

open MeasureTheory Filter
open scoped ProbabilityTheory Topology

set_option maxHeartbeats 1200000

namespace Part2.CNDProbability.SGRandom

section OriginalSpace
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {G : MeasurableSpace Ω}
  {X Λ : Ω → ℝ} {L v : ℝ}

/-- A single integrable envelope controls all coefficients in `[-L,L]`. -/
lemma exp_mul_le_endpoints {a x L : ℝ} (ha : |a| ≤ L) :
    Real.exp (a * x) ≤ Real.exp (L * x) + Real.exp ((-L) * x) := by
  rcases le_total 0 x with hx | hx
  · exact (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (abs_le.mp ha).2 hx)).trans
        (le_add_of_nonneg_right (Real.exp_nonneg _))
  · exact (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_right (abs_le.mp ha).1 hx)).trans
        (le_add_of_nonneg_left (Real.exp_nonneg _))

/-- Exponential integrability is derived, not supplied as the desired mixed MGF. -/
theorem integrable_exp_bounded_mul (hG : G ≤ m₀) (hX : Measurable[m₀] X)
    (hXi : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hΛ : StronglyMeasurable[G] Λ) (hbound : ∀ᵐ ω ∂μ, |Λ ω| ≤ L) :
    Integrable (fun ω => Real.exp (Λ ω * X ω)) μ := by
  apply ((hXi L).add (hXi (-L))).mono'
    (Real.continuous_exp.comp_stronglyMeasurable
      ((hΛ.mono hG).mul hX.stronglyMeasurable)).aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_mul_le_endpoints hω

lemma exp_square_coefficient_le (hL : 0 ≤ L) {a : ℝ} (ha : |a| ≤ L) :
    Real.exp (v ^ 2 * a ^ 2 / 2) ≤ Real.exp (v ^ 2 * L ^ 2 / 2) := by
  have hsq : a ^ 2 ≤ L ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) hL).2 ha
  apply Real.exp_le_exp.mpr
  gcongr

lemma integrable_exp_square_bounded (hG : G ≤ m₀)
    (hΛ : StronglyMeasurable[G] Λ) (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂μ, |Λ ω| ≤ L) :
    Integrable (fun ω => Real.exp (v ^ 2 * Λ ω ^ 2 / 2)) μ := by
  apply (integrable_const (Real.exp (v ^ 2 * L ^ 2 / 2))).mono'
    (Real.continuous_exp.comp_stronglyMeasurable
      (((((hΛ.mono hG).measurable.pow_const 2).const_mul (v ^ 2)).div_const 2).stronglyMeasurable)).aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_square_coefficient_le hL hω

/-- On each measurable fiber of a simple coefficient, use the corresponding
constant-parameter conditional bound. Only finitely many null sets are united. -/
theorem conditional_mgf_simple_coefficient (hG : G ≤ m₀)
    (s : @SimpleFunc Ω G ℝ)
    (hsi : Integrable (fun ω => Real.exp (s ω * X ω)) μ)
    (hXi : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hmgf : ∀ t : ℝ,
      μ[fun ω => Real.exp (t * X ω) | G] ≤ᵐ[μ]
        fun _ => Real.exp (v ^ 2 * t ^ 2 / 2)) :
    μ[fun ω => Real.exp (s ω * X ω) | G] ≤ᵐ[μ]
      fun ω => Real.exp (v ^ 2 * s ω ^ 2 / 2) := by
  classical
  have hcell (a : ℝ) : ∀ᵐ ω ∂μ, s ω = a →
      (μ[fun w => Real.exp (s w * X w) | G]) ω ≤ Real.exp (v ^ 2 * a ^ 2 / 2) := by
    let C : Set Ω := s ⁻¹' {a}
    have hC : MeasurableSet[G] C := s.measurableSet_fiber a
    have hident : C.indicator (fun ω => Real.exp (s ω * X ω)) =
        C.indicator (fun ω => Real.exp (a * X ω)) := by
      funext ω
      by_cases hω : ω ∈ C
      · have heq : s ω = a := hω
        simp only [Set.indicator_of_mem hω, heq]
      · simp only [Set.indicator_of_notMem hω]
    filter_upwards [condExp_indicator hsi hC,
      condExp_indicator (hXi a) hC, hmgf a] with ω hs ha hm
    intro hω
    have hmem : ω ∈ C := hω
    have hce : (μ[fun w => Real.exp (s w * X w) | G]) ω =
        (μ[fun w => Real.exp (a * X w) | G]) ω := by
      calc
        _ = C.indicator (μ[fun w => Real.exp (s w * X w) | G]) ω := by
          simp only [Set.indicator_of_mem hmem]
        _ = (μ[C.indicator (fun w => Real.exp (s w * X w)) | G]) ω := hs.symm
        _ = (μ[C.indicator (fun w => Real.exp (a * X w)) | G]) ω := by rw [hident]
        _ = C.indicator (μ[fun w => Real.exp (a * X w) | G]) ω := ha
        _ = _ := by simp only [Set.indicator_of_mem hmem]
    exact hce.le.trans hm
  have hall : ∀ᵐ ω ∂μ, ∀ a ∈ s.range, s ω = a →
      (μ[fun w => Real.exp (s w * X w) | G]) ω ≤ Real.exp (v ^ 2 * a ^ 2 / 2) :=
    (s.range.eventually_all).2 (fun a _ => hcell a)
  filter_upwards [hall] with ω hω
  exact hω (s ω) (s.mem_range_self ω) rfl

/-- Conditional upper bounds pass to dominated limits on the original space.
Only integrals over `G`-measurable sets are used; trim merely changes the
sigma-algebra for the final integral-order characterization. -/
theorem condExp_le_of_dominated_approximation (hG : G ≤ m₀)
    {F B : ℕ → Ω → ℝ} {f b D E : Ω → ℝ}
    (hFi : ∀ n, Integrable (F n) μ) (hfi : Integrable f μ)
    (hBi : ∀ n, Integrable (B n) μ) (hbi : Integrable b μ)
    (hbm : StronglyMeasurable[G] b)
    (hDi : Integrable D μ) (hEi : Integrable E μ)
    (hFd : ∀ n, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ D ω)
    (hBd : ∀ n, ∀ᵐ ω ∂μ, ‖B n ω‖ ≤ E ω)
    (hFlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (f ω)))
    (hBlim : ∀ᵐ ω ∂μ, Tendsto (fun n => B n ω) atTop (𝓝 (b ω)))
    (hCE : ∀ n, μ[F n | G] ≤ᵐ[μ] B n) :
    μ[f | G] ≤ᵐ[μ] b := by
  have hset (s : Set Ω) (hs : MeasurableSet[G] s) :
      (∫ ω in s, f ω ∂μ) ≤ ∫ ω in s, b ω ∂μ := by
    have htF := tendsto_integral_of_dominated_convergence (μ := μ.restrict s)
      D (fun n => (hFi n).aestronglyMeasurable.restrict) hDi.integrableOn
      (fun n => ae_restrict_of_ae (hFd n)) (ae_restrict_of_ae hFlim)
    have htB := tendsto_integral_of_dominated_convergence (μ := μ.restrict s)
      E (fun n => (hBi n).aestronglyMeasurable.restrict) hEi.integrableOn
      (fun n => ae_restrict_of_ae (hBd n)) (ae_restrict_of_ae hBlim)
    apply le_of_tendsto_of_tendsto' htF htB
    intro n
    rw [← setIntegral_condExp hG (hFi n) hs]
    exact setIntegral_mono_ae integrable_condExp.integrableOn (hBi n).integrableOn
      (hCE n)
  apply ae_le_of_ae_le_trim (hm := hG)
  apply ae_le_of_forall_setIntegral_le
    (integrable_condExp.trim hG stronglyMeasurable_condExp) (hbi.trim hG hbm)
  intro s hs _
  rw [← setIntegral_trim hG stronglyMeasurable_condExp hs,
    ← setIntegral_trim hG hbm hs, setIntegral_condExp hG hfi hs]
  exact hset s hs

/-- The generic predictable-coefficient conditional MGF theorem. Every
constant-parameter exponential is integrable; the random-parameter
exponential's integrability and conditional bound are then derived. -/
theorem conditional_mgf_bounded_coefficient (hG : G ≤ m₀) (hX : Measurable[m₀] X)
    (hXi : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hmgf : ∀ t : ℝ,
      μ[fun ω => Real.exp (t * X ω) | G] ≤ᵐ[μ]
        fun _ => Real.exp (v ^ 2 * t ^ 2 / 2))
    (hΛ : StronglyMeasurable[G] Λ) (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂μ, |Λ ω| ≤ L) :
    μ[fun ω => Real.exp (Λ ω * X ω) | G] ≤ᵐ[μ]
      fun ω => Real.exp (v ^ 2 * Λ ω ^ 2 / 2) := by
  let s : ℕ → @SimpleFunc Ω G ℝ := hΛ.approxBounded L
  have hsbound (n : ℕ) (ω : Ω) : |s n ω| ≤ L := by
    simpa only [Real.norm_eq_abs] using hΛ.norm_approxBounded_le hL n ω
  have hsconv : ∀ᵐ ω ∂μ, Tendsto (fun n => s n ω) atTop (𝓝 (Λ ω)) := by
    apply hΛ.tendsto_approxBounded_ae
    simpa only [Real.norm_eq_abs] using hbound
  let F : ℕ → Ω → ℝ := fun n ω => Real.exp (s n ω * X ω)
  let B : ℕ → Ω → ℝ := fun n ω => Real.exp (v ^ 2 * s n ω ^ 2 / 2)
  have hFi (n : ℕ) : Integrable (F n) μ :=
    integrable_exp_bounded_mul (m₀ := m₀) (G := G) (μ := μ) hG hX hXi (s n).stronglyMeasurable
      (Eventually.of_forall (hsbound n))
  have hBi (n : ℕ) : Integrable (B n) μ :=
    integrable_exp_square_bounded (m₀ := m₀) (G := G) (μ := μ) hG (s n).stronglyMeasurable hL
      (Eventually.of_forall (hsbound n))
  have hbm : StronglyMeasurable[G] (fun ω => Real.exp (v ^ 2 * Λ ω ^ 2 / 2)) :=
    Real.continuous_exp.comp_stronglyMeasurable
      (((((hΛ.measurable.pow_const 2).const_mul (v ^ 2)).div_const 2).stronglyMeasurable))
  apply condExp_le_of_dominated_approximation (m₀ := m₀) (G := G) (μ := μ) hG hFi
    (integrable_exp_bounded_mul (m₀ := m₀) (G := G) (μ := μ) hG hX hXi hΛ hbound) hBi
    (integrable_exp_square_bounded (m₀ := m₀) (G := G) (μ := μ) hG hΛ hL hbound) hbm
    ((hXi L).add (hXi (-L)))
    (integrable_const (Real.exp (v ^ 2 * L ^ 2 / 2)))
  · intro n
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_mul_le_endpoints (hsbound n ω)
  · intro n
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_square_coefficient_le hL (hsbound n ω)
  · filter_upwards [hsconv] with ω hω
    exact Real.continuous_exp.continuousAt.tendsto.comp (hω.mul_const (X ω))
  · filter_upwards [hsconv] with ω hω
    exact Real.continuous_exp.continuousAt.tendsto.comp
      (((hω.pow 2).const_mul (v ^ 2)).div_const 2)
  · intro n
    exact conditional_mgf_simple_coefficient (m₀ := m₀) (G := G) (μ := μ) hG (s n) (hFi n) hXi hmgf

end OriginalSpace
end Part2.CNDProbability.SGRandom
