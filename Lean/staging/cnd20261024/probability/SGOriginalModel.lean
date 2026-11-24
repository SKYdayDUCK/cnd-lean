import staging.cnd20261024.probability.ModelBridge
import staging.cnd20261024.probability.SGDirectionFiber
import staging.cnd20261024.probability.SGRestrictedProcess

open MeasureTheory Filter ProbabilityTheory Finset
open scoped ProbabilityTheory BigOperators NNReal
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability
section OriginalSG
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}

/-- Original-space SG-M1: the inherited bounded M1 record describes the
public/error protocol and noiseless residual. The actual SG residual below
adds `noise`. Physical noise and encoder can be dependent. -/
structure SGModel (ℱ : Filtration ℕ m₀) (μ : Measure Ω) (θ : ι → ℝ)
    (R M D σ σe : ℝ) extends M1Model ℱ μ θ R M D where
  afterNoiseAction : ℕ → MeasurableSpace Ω
  action_le_noiseAction : ∀ n, afterAction n ≤ afterNoiseAction n
  noiseAction_le_next : ∀ n, afterNoiseAction n ≤ ℱ (n + 1)
  noise : ℕ → ι → Ω → ℝ
  noise_afterAction_measurable : ∀ n i, Measurable[afterNoiseAction n] (noise n i)
  noise_encoded_measurable : ∀ n i, Measurable[encoded n] (noise n i)
  noise_exp_integrable : ∀ n i t, Integrable (fun ω => Real.exp (t * noise n i ω)) μ
  noise_conditional_mgf : ∀ n i t,
    μ[fun ω => Real.exp (t * noise n i ω) | pre n] ≤ᵐ[μ] fun _ => Real.exp (σ ^ 2 * t ^ 2 / 2)
  encoder_conditional_mgf : ∀ n i t,
    μ[fun ω => Real.exp (t * error n i ω) | afterNoiseAction n] ≤ᵐ[μ] fun _ => Real.exp (σe ^ 2 * t ^ 2 / 2)

namespace SGModel
variable (h : SGModel ℱ μ θ R M D σ σe)

def combinedNoise (n : ℕ) (i : ι) (ω : Ω) : ℝ := h.noise n i ω - h.error n i ω

lemma combined_measurable (n : ℕ) (i : ι) : Measurable[h.encoded n] (h.combinedNoise n i) :=
  (h.noise_encoded_measurable n i).sub (h.error_encoded n i)

lemma encoder_exp_integrable (n : ℕ) (i : ι) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * h.error n i ω)) μ := by
  apply (integrable_const (Real.exp (|t| * D))).mono'
    (Real.continuous_exp.comp_aestronglyMeasurable
      (((h.error_measurable n i).mono (ℱ.le (n + 1)) le_rfl).stronglyMeasurable.aestronglyMeasurable.const_mul t))
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h.error_bound n i ω) (abs_nonneg t))

lemma combined_exp_integrable (n : ℕ) (i : ι) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * h.combinedNoise n i ω)) μ := by
  have hneg : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * (-h.error n i ω))) μ := by
    intro s
    simpa only [mul_neg, neg_mul] using h.encoder_exp_integrable n i (-s)
  have hprod := SGRestricted.integrable_exp_add (μ := μ) (X := h.noise n i)
    (Y := fun ω => -h.error n i ω) (h.noise_exp_integrable n i) hneg t
  simpa only [combinedNoise, sub_eq_add_neg] using hprod

/-- Sequential conditioning discharges the combined coordinate noise MGF on
G, before any directional mixture. No action-conditioned noise law is added. -/
theorem combined_conditional_mgf (n : ℕ) (i : ι) (t : ℝ) :
    μ[fun ω => Real.exp (t * h.combinedNoise n i ω) | h.pre n] ≤ᵐ[μ]
      fun _ => Real.exp ((σ ^ 2 + σe ^ 2) * t ^ 2 / 2) := by
  exact SGConditional.conditional_composed_mgf (m₀ := m₀) (μ := μ)
    ((h.pre_le_action n).trans (h.action_le_noiseAction n))
    ((h.noiseAction_le_next n).trans (ℱ.le (n + 1)))
    (h.noise_afterAction_measurable n i).stronglyMeasurable
    (h.noise_exp_integrable n i) (h.encoder_exp_integrable n i)
    (h.noise_conditional_mgf n i) (h.encoder_conditional_mgf n i) t

noncomputable def signalAt (b : ι → ℝ) (n : ℕ) (i : ι) (ω : Ω) : ℝ :=
  SGDirectionFiber.signal (fun j => h.p n j ω) b θ (h.drift n ω) i

noncomputable def directionIncrement (b : ι → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  h.signalAt b n (h.action n ω) ω +
    Directional.scoreAt h.toM1Model.statistics b n (h.action n ω) ω * h.combinedNoise n (h.action n ω) ω

lemma signalAt_measurable (b : ι → ℝ) (n : ℕ) (i : ι) :
    Measurable[h.pre n] (h.signalAt b n i) := by
  exact (((Directional.scoreAt_measurable h.toM1Model.statistics b n i).mono (h.past_le_pre n) le_rfl).mul
    (measurable_const.add (h.drift_measurable n))).sub
      ((Directional.mean_measurable h.toM1Model.statistics b n).mono (h.past_le_pre n) le_rfl)

lemma signalAt_bound (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1) (n : ℕ) (i : ι) (ω : Ω) :
    |h.signalAt b n i ω| ≤ 2 * (R + M) :=
  SGDirectionFiber.signal_bound _ _ _ _ _ _ (h.p_nonneg n ω) (h.p_sum n ω) hb h.theta_range (h.drift_range n ω) i

end SGModel
end OriginalSG
end Part2.CNDProbability
