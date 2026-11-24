import staging.cnd20261024.process.CNDProcess

/-!
# Original M1 layers on the actual recursively computed CND distribution

`pre` is the complete pre-action physical information G. `encoded` is exactly
G joined with the potential encoding seed, and `afterAction` is exactly G
joined with the action. The two primitive M1 conditional laws are supplied on
the original probability space; all algorithmic predictability is derived.
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory

namespace Part2.CNDProcess

variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [m₀ : MeasurableSpace Ω]

structure PotentialInputs (ℱ : Filtration ℕ m₀) (θ : ι → ℝ) (R M D : ℝ) where
  R_nonneg : 0 ≤ R
  M_nonneg : 0 ≤ M
  D_nonneg : 0 ≤ D
  theta_range : ∀ a, 0 ≤ θ a ∧ θ a ≤ R
  pre : ℕ → MeasurableSpace Ω
  past_le_pre : ∀ n, ℱ n ≤ pre n
  pre_le_next : ∀ n, pre n ≤ ℱ (n + 1)
  action : ℕ → Ω → ι
  seed : ℕ → Ω → (ι → ℝ)
  publicCost : ℕ → ι → Ω → ℝ
  drift : ℕ → Ω → ℝ
  error : ℕ → ι → Ω → ℝ
  action_measurable : ∀ n, Measurable[ℱ (n + 1)] (action n)
  seed_measurable : ∀ n, Measurable[ℱ (n + 1)] (seed n)
  public_measurable : ∀ n a, Measurable[pre n] (publicCost n a)
  drift_measurable : ∀ n, Measurable[pre n] (drift n)
  drift_range : ∀ n ω, 0 ≤ drift n ω ∧ drift n ω ≤ M
  error_encoded : ∀ n a, Measurable[pre n ⊔ MeasurableSpace.comap (seed n) inferInstance] (error n a)
  error_bound : ∀ n a ω, |error n a ω| ≤ D

namespace PotentialInputs
variable {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ}
  (h : PotentialInputs ℱ θ R M D)

def encoded (n : ℕ) : MeasurableSpace Ω := h.pre n ⊔ MeasurableSpace.comap (h.seed n) inferInstance
def afterAction (n : ℕ) : MeasurableSpace Ω := h.pre n ⊔ MeasurableSpace.comap (h.action n) inferInstance

theorem encoded_le_next (n : ℕ) : h.encoded n ≤ ℱ (n + 1) :=
  sup_le (h.pre_le_next n) (h.seed_measurable n).comap_le

theorem afterAction_le_next (n : ℕ) : h.afterAction n ≤ ℱ (n + 1) :=
  sup_le (h.pre_le_next n) (h.action_measurable n).comap_le

theorem action_measurable_after (n : ℕ) : Measurable[h.afterAction n] (h.action n) :=
  (comap_measurable (h.action n)).mono le_sup_right le_rfl

theorem seed_measurable_encoded (n : ℕ) : Measurable[h.encoded n] (h.seed n) :=
  (comap_measurable (h.seed n)).mono le_sup_right le_rfl

def physical (n : ℕ) (a : ι) (ω : Ω) : ℝ := h.publicCost n a ω + θ a + h.drift n ω
def broadcast (n : ℕ) (ω : Ω) (a : ι) : ℝ := h.publicCost n a ω + h.error n a ω
def residual (n : ℕ) (ω : Ω) : ℝ :=
  h.physical n (h.action n ω) ω - h.broadcast n ω (h.action n ω)

theorem potential_broadcast_measurable (n : ℕ) : Measurable[h.encoded n] (h.broadcast n) := by
  have hm (a : ι) : Measurable[h.encoded n] (fun ω ↦ h.publicCost n a ω + h.error n a ω) :=
    ((h.public_measurable n a).mono le_sup_left le_rfl).add (h.error_encoded n a)
  exact @measurable_pi_lambda Ω ι (fun _ ↦ ℝ) (h.encoded n) (fun _ ↦ inferInstance)
    (h.broadcast n) hm

theorem residual_eq (n : ℕ) (ω : Ω) :
    h.residual n ω = θ (h.action n ω) + h.drift n ω - h.error n (h.action n ω) ω := by
  unfold residual physical broadcast
  ring

theorem residual_measurable (n : ℕ) : Measurable[ℱ (n + 1)] (h.residual n) := by
  have hm (a : ι) : Measurable[ℱ (n + 1)] (fun ω ↦ θ a + h.drift n ω - h.error n a ω) :=
    (measurable_const.add ((h.drift_measurable n).mono (h.pre_le_next n) le_rfl)).sub
      ((h.error_encoded n a).mono (h.encoded_le_next n) le_rfl)
  have hsel := PairConfidence.selected_measurable (h.action_measurable n) hm
  convert hsel using 1
  funext ω
  exact h.residual_eq n ω

theorem residual_bound (n : ℕ) (ω : Ω) : |h.residual n ω| ≤ R + M + D := by
  rw [h.residual_eq, abs_le]
  obtain ⟨he0, he1⟩ := abs_le.mp (h.error_bound n (h.action n ω) ω)
  have ht := h.theta_range (h.action n ω)
  have hz := h.drift_range n ω
  constructor <;> linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg]

def feedback : Feedback (ι := ι) ℱ where
  action := h.action
  residual := h.residual
  broadcast := h.broadcast
  action_measurable := h.action_measurable
  residual_measurable := h.residual_measurable
  broadcast_measurable n := (h.potential_broadcast_measurable n).mono (h.encoded_le_next n) le_rfl

end PotentialInputs

section M1Construction
variable {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exactly the original M1 primitive laws, using the probability calculated
by the actual state recursion. No free predictable distribution, statistical
confidence premise, good-event field or MGF hypothesis is introduced. -/
structure OriginalM1 (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ θ R M D) (μ : Measure Ω) : Prop where
  strong_categorical : ∀ n a,
    μ[PairConfidence.actionIndicator (h.action n) a | h.encoded n] =ᵐ[μ]
      runProbability o d h.feedback n a
  encoder_centered : ∀ n a, μ[h.error n a | h.afterAction n] =ᵐ[μ] fun _ ↦ 0

namespace OriginalM1
variable (o : DecisionMaps ι) (d : ExpertData ι E) (h : PotentialInputs ℱ θ R M D)
  (hm : OriginalM1 o d h μ)

theorem probability_bounds (n : ℕ) (a : ι) (ω : Ω) :
    0 ≤ runProbability o d h.feedback n a ω ∧ runProbability o d h.feedback n a ω ≤ 1 := by
  have hp := runProbability_simplex o d h.feedback n ω
  refine ⟨hp.1 a, ?_⟩
  calc
    _ ≤ ∑ i, runProbability o d h.feedback n i ω :=
      Finset.single_le_sum (fun i _ ↦ hp.1 i) (Finset.mem_univ a)
    _ = 1 := hp.2

theorem probability_integrable (n : ℕ) (a : ι) : Integrable (runProbability o d h.feedback n a) μ :=
  PairConfidence.bounded_integrable ((runProbability_measurable o d h.feedback n a).mono (ℱ.le n) le_rfl)
    (fun ω ↦ by simpa only [abs_of_nonneg (probability_bounds o d h n a ω).1] using
      (probability_bounds o d h n a ω).2)

include hm in
theorem categorical_at_pre (n : ℕ) (a : ι) :
    μ[PairConfidence.actionIndicator (h.action n) a | h.pre n] =ᵐ[μ]
      runProbability o d h.feedback n a :=
  PairConfidence.conditional_down (m₁ := h.pre n) (m₂ := h.encoded n) le_sup_left
    ((h.encoded_le_next n).trans (ℱ.le (n + 1))) (hm.strong_categorical n a)
    ((runProbability_measurable o d h.feedback n a).stronglyMeasurable.mono (h.past_le_pre n))
    (probability_integrable o d h n a)

/-- The generic probability library is instantiated by the computed run,
not by a new unrelated sequence p. All measurability obligations are discharged. -/
def toM1Model : CNDProbability.M1Model ℱ μ θ R M D where
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
  p_nonneg := fun n ω a ↦ (probability_bounds o d h n a ω).1
  p_sum := fun n ω ↦ (runProbability_simplex o d h.feedback n ω).2
  action_measurable := h.action_measurable_after
  public_measurable := h.public_measurable
  drift_measurable := h.drift_measurable
  drift_range := h.drift_range
  error_measurable := fun n a ↦ (h.error_encoded n a).mono (h.encoded_le_next n) le_rfl
  error_bound := h.error_bound
  categorical := categorical_at_pre o d h hm
  encoder_centered := hm.encoder_centered
  encoded := h.encoded
  pre_le_encoded := fun _ ↦ le_sup_left
  encoded_le_next := h.encoded_le_next
  error_encoded := h.error_encoded
  strong_categorical := hm.strong_categorical

theorem model_probability_is_computed (n : ℕ) (a : ι) :
    (toM1Model o d h hm).p n a = runProbability o d h.feedback n a := rfl

theorem model_residual_is_observed (n : ℕ) :
    (toM1Model o d h hm).toSamplingModel.residual n = h.residual n := rfl

end OriginalM1
end M1Construction
end Part2.CNDProcess

end
