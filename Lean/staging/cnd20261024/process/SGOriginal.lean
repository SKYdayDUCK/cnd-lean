import staging.cnd20261024.process.ActualModel
import staging.cnd20261024.probability.SGOriginalUniform

/-! Original-space SG input chronology and the genuine noisy feedback run.
The M1 projection below is only a same-p public/encoding shadow. Its bounded
residual is never substituted for the observed SG residual in the recursion. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
namespace Part2.CNDProcess.SG
variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [m₀ : MeasurableSpace Ω]

structure Inputs (ℱ : Filtration ℕ m₀) (θ : ι → ℝ) (R M D : ℝ) where
  R_nonneg : 0 ≤ R
  M_nonneg : 0 ≤ M
  D_nonneg : 0 ≤ D
  theta_range : ∀ i, 0 ≤ θ i ∧ θ i ≤ R
  pre : ℕ → MeasurableSpace Ω
  past_le_pre : ∀ n, ℱ n ≤ pre n
  pre_le_next : ∀ n, pre n ≤ ℱ (n + 1)
  action : ℕ → Ω → ι
  noise : ℕ → Ω → Vec ι
  encodingSeed : ℕ → Ω → Vec ι
  publicCost : ℕ → ι → Ω → ℝ
  drift : ℕ → Ω → ℝ
  error : ℕ → ι → Ω → ℝ
  action_measurable : ∀ n, Measurable[ℱ (n + 1)] (action n)
  noise_measurable : ∀ n, Measurable[ℱ (n + 1)] (noise n)
  seed_measurable : ∀ n, Measurable[ℱ (n + 1)] (encodingSeed n)
  public_measurable : ∀ n i, Measurable[pre n] (publicCost n i)
  drift_measurable : ∀ n, Measurable[pre n] (drift n)
  drift_range : ∀ n ω, 0 ≤ drift n ω ∧ drift n ω ≤ M
  error_encoded : ∀ n i, Measurable[pre n ⊔
    (MeasurableSpace.comap (noise n) inferInstance ⊔
      MeasurableSpace.comap (encodingSeed n) inferInstance)] (error n i)
  error_bound : ∀ n i ω, |error n i ω| ≤ D

namespace Inputs
variable {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ}
  (h : Inputs ℱ θ R M D)

def encoded (n : ℕ) : MeasurableSpace Ω := h.pre n ⊔
  (MeasurableSpace.comap (h.noise n) inferInstance ⊔
    MeasurableSpace.comap (h.encodingSeed n) inferInstance)
def afterAction (n : ℕ) : MeasurableSpace Ω :=
  h.pre n ⊔ MeasurableSpace.comap (h.action n) inferInstance
def afterNoiseAction (n : ℕ) : MeasurableSpace Ω :=
  h.afterAction n ⊔ MeasurableSpace.comap (h.noise n) inferInstance

theorem encoded_le_next (n : ℕ) : h.encoded n ≤ ℱ (n + 1) :=
  sup_le (h.pre_le_next n) (sup_le (h.noise_measurable n).comap_le (h.seed_measurable n).comap_le)
theorem afterAction_le_next (n : ℕ) : h.afterAction n ≤ ℱ (n + 1) :=
  sup_le (h.pre_le_next n) (h.action_measurable n).comap_le
theorem afterNoiseAction_le_next (n : ℕ) : h.afterNoiseAction n ≤ ℱ (n + 1) :=
  sup_le (h.afterAction_le_next n) (h.noise_measurable n).comap_le
theorem action_measurable_after (n : ℕ) : Measurable[h.afterAction n] (h.action n) :=
  (comap_measurable (h.action n)).mono le_sup_right le_rfl
theorem noise_encoded (n : ℕ) (i : ι) : Measurable[h.encoded n] (fun ω ↦ h.noise n ω i) :=
  (measurable_pi_apply i).comp ((comap_measurable (h.noise n)).mono
    (le_trans le_sup_left le_sup_right) le_rfl)
theorem noise_afterNoiseAction (n : ℕ) (i : ι) :
    Measurable[h.afterNoiseAction n] (fun ω ↦ h.noise n ω i) :=
  (measurable_pi_apply i).comp ((comap_measurable (h.noise n)).mono le_sup_right le_rfl)

def physical (n : ℕ) (i : ι) (ω : Ω) : ℝ :=
  h.publicCost n i ω + θ i + h.drift n ω + h.noise n ω i
def broadcast (n : ℕ) (ω : Ω) (i : ι) : ℝ := h.publicCost n i ω + h.error n i ω
def residual (n : ℕ) (ω : Ω) : ℝ :=
  h.physical n (h.action n ω) ω - h.broadcast n ω (h.action n ω)

theorem residual_eq (n : ℕ) (ω : Ω) : h.residual n ω =
    θ (h.action n ω) + h.drift n ω + h.noise n ω (h.action n ω) - h.error n (h.action n ω) ω := by
  unfold residual physical broadcast
  ring

theorem broadcast_measurable (n : ℕ) : Measurable[h.encoded n] (h.broadcast n) := by
  have hm (i : ι) : Measurable[h.encoded n] (fun ω ↦ h.publicCost n i ω + h.error n i ω) :=
    ((h.public_measurable n i).mono le_sup_left le_rfl).add (h.error_encoded n i)
  exact @measurable_pi_lambda Ω ι (fun _ ↦ ℝ) (h.encoded n) (fun _ ↦ inferInstance) _ hm

theorem residual_measurable (n : ℕ) : Measurable[ℱ (n + 1)] (h.residual n) := by
  have hm (i : ι) : Measurable[ℱ (n + 1)]
      (fun ω ↦ θ i + h.drift n ω + h.noise n ω i - h.error n i ω) :=
    ((measurable_const.add ((h.drift_measurable n).mono (h.pre_le_next n) le_rfl)).add
      ((measurable_pi_apply i).comp (h.noise_measurable n))).sub
      ((h.error_encoded n i).mono (h.encoded_le_next n) le_rfl)
  have hs := PairConfidence.selected_measurable (h.action_measurable n) hm
  convert hs using 1
  funext ω
  exact h.residual_eq n ω

def feedback : Feedback (ι := ι) ℱ where
  action := h.action
  residual := h.residual
  broadcast := h.broadcast
  action_measurable := h.action_measurable
  residual_measurable := h.residual_measurable
  broadcast_measurable n := (h.broadcast_measurable n).mono (h.encoded_le_next n) le_rfl

theorem broadcast_span (B : ℝ) (n : ℕ) (ω : Ω) (i j : ι)
    (hc : h.publicCost n j ω - h.publicCost n i ω ≤ B) :
    h.broadcast n ω j - h.broadcast n ω i ≤ B + 2 * D := by
  have hi := (abs_le.mp (h.error_bound n i ω)).1
  have hj := (abs_le.mp (h.error_bound n j ω)).2
  dsimp [broadcast]
  linarith
end Inputs

section Model
variable {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D σ σe : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

structure Laws (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : Inputs ℱ θ R M D) (μ : Measure Ω) (σ σe : ℝ) : Prop where
  strong_categorical : ∀ n i,
    μ[PairConfidence.actionIndicator (h.action n) i | h.encoded n] =ᵐ[μ]
      runProbability o d h.feedback n i
  encoder_centered : ∀ n i, μ[h.error n i | h.afterAction n] =ᵐ[μ] fun _ ↦ 0
  noise_exp_integrable : ∀ n i t, Integrable (fun ω ↦ Real.exp (t * h.noise n ω i)) μ
  noise_conditional_mgf : ∀ n i t,
    μ[fun ω ↦ Real.exp (t * h.noise n ω i) | h.pre n] ≤ᵐ[μ]
      fun _ ↦ Real.exp (σ ^ 2 * t ^ 2 / 2)
  encoder_conditional_mgf : ∀ n i t,
    μ[fun ω ↦ Real.exp (t * h.error n i ω) | h.afterNoiseAction n] ≤ᵐ[μ]
      fun _ ↦ Real.exp (σe ^ 2 * t ^ 2 / 2)

namespace Laws
variable (o : DecisionMaps ι) (d : ExpertData ι E) (h : Inputs ℱ θ R M D)
  (hm : Laws o d h μ σ σe)

theorem probability_integrable (n : ℕ) (i : ι) : Integrable (runProbability o d h.feedback n i) μ :=
  PairConfidence.bounded_integrable ((runProbability_measurable o d h.feedback n i).mono (ℱ.le n) le_rfl)
    (fun ω ↦ by simpa only [abs_of_nonneg (runProbability_bounds o d h.feedback n i ω).1] using
      (runProbability_bounds o d h.feedback n i ω).2)

include hm in
theorem categorical_at_pre (n : ℕ) (i : ι) :
    μ[PairConfidence.actionIndicator (h.action n) i | h.pre n] =ᵐ[μ]
      runProbability o d h.feedback n i :=
  PairConfidence.conditional_down (m₁ := h.pre n) (m₂ := h.encoded n) le_sup_left
    ((h.encoded_le_next n).trans (ℱ.le (n + 1))) (hm.strong_categorical n i)
    ((runProbability_measurable o d h.feedback n i).stronglyMeasurable.mono (h.past_le_pre n))
    (probability_integrable o d h n i)

/-- Same actual p/action/public encoding. The noiseless residual of this
record is reserved for public/payment lemmas, never used as SG feedback. -/
def publicShadow : CNDProbability.M1Model ℱ μ θ R M D where
  R_nonneg := h.R_nonneg
  M_nonneg := h.M_nonneg
  D_nonneg := h.D_nonneg
  theta_range := h.theta_range
  pre := h.pre
  afterAction := h.afterAction
  past_le_pre := h.past_le_pre
  pre_le_action := fun _ ↦ le_sup_left
  action_le_next := h.afterAction_le_next
  p := runProbability o d h.feedback
  action := h.action
  publicCost := h.publicCost
  drift := h.drift
  error := h.error
  p_measurable := runProbability_measurable o d h.feedback
  p_nonneg := fun n ω i ↦ (runProbability_bounds o d h.feedback n i ω).1
  p_sum := fun n ω ↦ (runProbability_simplex o d h.feedback n ω).2
  action_measurable := h.action_measurable_after
  public_measurable := h.public_measurable
  drift_measurable := h.drift_measurable
  drift_range := h.drift_range
  error_measurable := fun n i ↦ (h.error_encoded n i).mono (h.encoded_le_next n) le_rfl
  error_bound := h.error_bound
  categorical := categorical_at_pre o d h hm
  encoder_centered := hm.encoder_centered
  encoded := h.encoded
  pre_le_encoded := fun _ ↦ le_sup_left
  encoded_le_next := h.encoded_le_next
  error_encoded := h.error_encoded
  strong_categorical := hm.strong_categorical

def model : CNDProbability.SGModel ℱ μ θ R M D σ σe where
  toM1Model := publicShadow o d h hm
  afterNoiseAction := h.afterNoiseAction
  action_le_noiseAction := fun _ ↦ le_sup_left
  noiseAction_le_next := h.afterNoiseAction_le_next
  noise := fun n i ω ↦ h.noise n ω i
  noise_afterAction_measurable := h.noise_afterNoiseAction
  noise_encoded_measurable := h.noise_encoded
  noise_exp_integrable := hm.noise_exp_integrable
  noise_conditional_mgf := hm.noise_conditional_mgf
  encoder_conditional_mgf := hm.encoder_conditional_mgf

theorem model_probability_actual (n : ℕ) (i : ι) :
    (model o d h hm).p n i = runProbability o d h.feedback n i := rfl

theorem actual_residual_adds_noise (n : ℕ) (ω : Ω) :
    h.residual n ω = (publicShadow o d h hm).toSamplingModel.residual n ω + h.noise n ω (h.action n ω) := by
  rw [h.residual_eq]
  rw [PairConfidence.SamplingModel.residual_eq]
  change θ (h.action n ω) + h.drift n ω + h.noise n ω (h.action n ω) - h.error n (h.action n ω) ω =
    θ (h.action n ω) + h.drift n ω - h.error n (h.action n ω) ω + h.noise n ω (h.action n ω)
  ring
end Laws
end Model
end Part2.CNDProcess.SG
end
