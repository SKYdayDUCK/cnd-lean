import Part2.SubGaussian
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! Sequential noise/encoder composition from conditional towers.
Unlike the independent special case in the old SubGaussian module, no
unconditional independence between physical noise and encoder is assumed. -/

open MeasureTheory Filter ProbabilityTheory
open scoped ProbabilityTheory NNReal
set_option maxHeartbeats 800000

namespace Part2.CNDProbability.SGConditional

section RawConditional
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {G H : MeasurableSpace Ω} {ξ e : Ω → ℝ}

/-- Exp integrability is included explicitly because conditional Bochner
expectation uses a default value for nonintegrable functions. It is derived
automatically from mathlib's conditional-subGaussian predicate below. -/
theorem conditional_composed_mgf (hGH : G ≤ H) (hH0 : H ≤ m₀)
    (hξm : StronglyMeasurable[H] ξ)
    (hξi : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * ξ ω)) μ)
    (hei : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * e ω)) μ)
    {σ2 σe2 : ℝ}
    (hξ : ∀ t : ℝ, μ[fun ω => Real.exp (t * ξ ω) | G] ≤ᵐ[μ] fun _ => Real.exp (σ2 * t ^ 2 / 2))
    (he : ∀ t : ℝ, μ[fun ω => Real.exp (t * e ω) | H] ≤ᵐ[μ] fun _ => Real.exp (σe2 * t ^ 2 / 2))
    (t : ℝ) :
    μ[fun ω => Real.exp (t * (ξ ω - e ω)) | G] ≤ᵐ[μ]
      fun _ => Real.exp ((σ2 + σe2) * t ^ 2 / 2) := by
  let F : Ω → ℝ := fun ω => Real.exp (t * ξ ω)
  let E : Ω → ℝ := fun ω => Real.exp (-t * e ω)
  have hFi : Integrable F μ := hξi t
  have hEi : Integrable E μ := hei (-t)
  have hprod : Integrable (fun ω => F ω * E ω) μ := by
    apply ((hξi (2 * t)).add (hei (-2 * t))).mono'
      (hFi.aestronglyMeasurable.mul hEi.aestronglyMeasurable)
    apply Eventually.of_forall
    intro ω
    change ‖F ω * E ω‖ ≤ Real.exp ((2 * t) * ξ ω) + Real.exp ((-2 * t) * e ω)
    have hF0 : 0 ≤ F ω := Real.exp_nonneg _
    have hE0 : 0 ≤ E ω := Real.exp_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hF0 hE0)]
    have hF2 : F ω ^ 2 = Real.exp ((2 * t) * ξ ω) := by
      dsimp [F]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hE2 : E ω ^ 2 = Real.exp ((-2 * t) * e ω) := by
      dsimp [E]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    nlinarith [sq_nonneg (F ω - E ω), sq_nonneg (F ω), sq_nonneg (E ω)]
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (Real.continuous_exp.comp_stronglyMeasurable (hξm.const_mul t)) hprod hEi
  let C : ℝ := Real.exp (σe2 * t ^ 2 / 2)
  have hcondH : μ[fun ω => F ω * E ω | H] ≤ᵐ[μ] fun ω => C * F ω := by
    filter_upwards [hpull, he (-t)] with ω hp he
    change (μ[fun ω => F ω * E ω | H]) ω = F ω * (μ[E | H]) ω at hp
    rw [hp]
    have hb : (μ[E | H]) ω ≤ C := by simpa only [neg_sq] using he
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (t * ξ ω))
  have hmono := condExp_mono (m := G) integrable_condExp (hFi.const_mul C) hcondH
  have htower := condExp_condExp_of_le (μ := μ) (f := fun ω => F ω * E ω) hGH hH0
  have hscale := condExp_smul (μ := μ) C F G
  have hformula : (fun ω => Real.exp (t * (ξ ω - e ω))) = fun ω => F ω * E ω := by
    funext ω
    dsimp [F, E]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hformula]
  filter_upwards [hmono, htower, hscale, hξ t] with ω hm ht hs hξ
  change (μ[fun ω => C * F ω | G]) ω = C * (μ[F | G]) ω at hs
  calc
    _ = (μ[μ[fun ω => F ω * E ω | H] | G]) ω := ht.symm
    _ ≤ (μ[fun ω => C * F ω | G]) ω := hm
    _ = C * (μ[F | G]) ω := hs
    _ ≤ C * Real.exp (σ2 * t ^ 2 / 2) := mul_le_mul_of_nonneg_left hξ (Real.exp_nonneg _)
    _ = _ := by dsimp [C]; rw [← Real.exp_add]; congr 1; ring

end RawConditional

section MathlibConditional
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {G H : MeasurableSpace Ω}
  {ξ e : Ω → ℝ} {σ2 σe2 : ℝ≥0}

/-- Official conditional-kernel predicates discharge all exp-integrability
premises of the raw tower theorem, including cross-product integrability. -/
theorem conditional_composed_mgf_of_hasCond (hGH : G ≤ H) (hH0 : H ≤ m₀)
    (hξm : StronglyMeasurable[H] ξ)
    (hξ : HasCondSubgaussianMGF G (hGH.trans hH0) ξ σ2 μ)
    (he : HasCondSubgaussianMGF H hH0 e σe2 μ) (t : ℝ) :
    μ[fun ω => Real.exp (t * (ξ ω - e ω)) | G] ≤ᵐ[μ]
      fun _ => Real.exp (((σ2 + σe2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
  exact conditional_composed_mgf (m₀ := m₀) (μ := μ) (G := G) (H := H) hGH hH0 hξm hξ.integrable_exp_mul he.integrable_exp_mul
    hξ.ae_condExp_le he.ae_condExp_le t

/-- Unconditional sequential projection with the sum of variance proxies.
Encoder dependence on the revealed physical noise is explicitly allowed. -/
theorem encoded_noise_subGaussian_sequential (hH0 : H ≤ m₀) (hξm : Measurable[H] ξ)
    (hξ : HasSubgaussianMGF ξ σ2 μ) (he : HasCondSubgaussianMGF H hH0 e σe2 μ) :
    HasSubgaussianMGF (fun ω => ξ ω - e ω) (σ2 + σe2) μ := by
  have hneg : HasCondSubgaussianMGF H hH0 (-e) σe2 μ := Kernel.HasSubgaussianMGF.neg he
  have h := HasSubgaussianMGF_add_of_HasCondSubgaussianMGF hH0 (hξ.trim hH0 hξm) hneg
  simpa only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg] using h

end MathlibConditional
end Part2.CNDProbability.SGConditional
