import staging.cnd20261024.payment.ConditionalHoeffding

noncomputable section
open MeasureTheory Filter
open scoped ProbabilityTheory

namespace Part2.CNDPayment
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}
variable (h : CNDProbability.M1Model ℱ μ θ R M D)

def encodingDifference (k : ι) (n : ℕ) (ω : Ω) : ℝ :=
  h.error n k ω - h.error n (h.action n ω) ω

theorem encodingDifference_measurable (k : ι) (n : ℕ) :
    Measurable[ℱ (n + 1)] (encodingDifference h k n) :=
  (h.error_measurable n k).sub (h.toSamplingModel.selectedError_measurable n)

theorem encodingDifference_bound (k : ι) (n : ℕ) (ω : Ω) :
    |encodingDifference h k n ω| ≤ 2 * D := by
  exact (abs_sub _ _).trans (by
    have hi := h.error_bound n k ω
    have hj := h.error_bound n (h.action n ω) ω
    linarith)

/-- M1 centers the actual encoding difference after the action, without
requiring independent encoder coordinates. -/
theorem encodingDifference_condExp (k : ι) (n : ℕ) :
    μ[encodingDifference h k n | h.afterAction n] =ᵐ[μ] fun _ => 0 := by
  have hi : Integrable (h.error n k) μ := PairConfidence.bounded_integrable
    ((h.error_measurable n k).mono (ℱ.le (n + 1)) le_rfl) (h.error_bound n k)
  have he := condExp_sub hi (h.toSamplingModel.selectedError_integrable n) (h.afterAction n)
  filter_upwards [he, h.encoder_centered n k, h.toSamplingModel.selectedError_conditional_zero n]
    with ω heω hiω hjω
  change (μ[h.error n k - h.toSamplingModel.selectedError n | h.afterAction n]) ω = 0
  simpa only [Pi.sub_apply, hiω, hjω, sub_self] using heω

theorem encodingDifference_conditional_mgf (k : ι) (n : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * encodingDifference h k n ω)) μ ∧
      μ[fun ω => Real.exp (t * encodingDifference h k n ω) | ℱ n] ≤ᵐ[μ]
        fun _ => Real.exp ((2 * D) ^ 2 * t ^ 2 / 2) := by
  have hc := PairConfidence.conditional_zero_down
    ((h.past_le_pre n).trans (h.pre_le_action n)) (h.action_le n)
    (encodingDifference_condExp h k n)
  exact conditional_hoeffding μ (ℱ.le n) (encodingDifference h k n)
    ((encodingDifference_measurable h k n).mono (ℱ.le (n + 1)) le_rfl)
    (by linarith [h.D_nonneg]) (encodingDifference_bound h k n) hc t

end Part2.CNDPayment
