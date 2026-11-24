import staging.cnd20261026.«fix-bounded-sg».ExponentialStochastic
import staging.cnd20261026.«fix-bounded-sg».AdjacentEncoderSG
import staging.cnd20261025.sg.NoiseEvents

/-! Original finite SG feedback for the actual exponential recursion.
The categorical RHS is the new computed exponential probability. No law of
the old Prod run is used, and the M1 shadow is never fed into the SG recursion.
-/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 1600000

namespace Part2.ExponentialSGStochastic
open CNDProcess CNDHorizon
variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [Nonempty E]
  [m₀ : MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D σ σe : ℝ} {T : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (o : DecisionMaps ι) (d : ExpertData ι E) (prior : E → ℝ)
  (h : SGInputs ℱ θ R M D T)

def finiteProbability (n : ℕ) (i : ι) (ω : Ω) : ℝ :=
  probability o d n (ExponentialStochastic.rawRun o d prior h.action h.residual h.broadcast n ω) i

theorem finite_run_prefix (n : ℕ) (hn : n≤T) :
    ExponentialStochastic.run o d prior h.extend.feedback n =
      ExponentialStochastic.rawRun o d prior h.action h.residual h.broadcast n :=
  ExponentialStochastic.rawRun_prefix o d prior _ _ _ _ _ _ T
    (fun t ht => h.extend_action ht) (fun t ht => h.extend_residual ht)
    (fun t ht => h.extend_broadcast ht) n hn

theorem finite_probability_prefix (n : ℕ) (hn : n≤T) :
    ExponentialStochastic.runProbability o d prior h.extend.feedback n = finiteProbability o d prior h n := by
  funext i ω
  simp only [ExponentialStochastic.runProbability, finiteProbability,
    congrFun (finite_run_prefix o d prior h n hn) ω]

/-- Primitive protocol laws at the actual exponential probability. The final
two fields condition on the physical information specified in A0. -/
structure FiniteLaws : Prop where
  strong_categorical : ∀ n<T, ∀ i,
    μ[PairConfidence.actionIndicator (h.action n) i | h.encoded n] =ᵐ[μ]
      finiteProbability o d prior h n i
  encoder_centered : ∀ n<T, ∀ i, μ[h.error n i | h.afterAction n] =ᵐ[μ] fun _ => 0
  noise_exp_integrable : ∀ n<T, ∀ i t, Integrable (fun ω => Real.exp (t * h.noise n ω i)) μ
  noise_conditional_mgf : ∀ n<T, ∀ i t,
    μ[fun ω => Real.exp (t * h.noise n ω i) | h.pre n] ≤ᵐ[μ]
      fun _ => Real.exp (σ ^ 2 * t ^ 2 / 2)
  encoder_conditional_mgf : ∀ n<T, ∀ i t,
    μ[fun ω => Real.exp (t * h.error n i ω) | h.afterNoiseAction n] ≤ᵐ[μ]
      fun _ => Real.exp (σe ^ 2 * t ^ 2 / 2)

/-- The adjacent-grid protocol supplies both encoder laws at Δ/2, while
the categorical RHS remains this actual exponential run. -/
def laws_of_adjacent (Δ : ℝ) (hΔ : 0 ≤ Δ) (cell : ℕ → ι → Ω → ℝ)
    (hcellm : ∀ n<T, ∀ i, Measurable[h.afterNoiseAction n] (cell n i))
    (hcellrange : ∀ n<T, ∀ i ω, cell n i ω ∈ Set.Icc 0 1)
    (hcell : ∀ n<T, ∀ i ω,
      h.error n i ω ∈ Set.Icc (-Δ * cell n i ω) (Δ * (1 - cell n i ω)))
    (hcenter : ∀ n<T, ∀ i, μ[h.error n i | h.afterNoiseAction n] =ᵐ[μ] 0)
    (hsample : ∀ n<T, ∀ i,
      μ[PairConfidence.actionIndicator (h.action n) i | h.encoded n] =ᵐ[μ]
        finiteProbability o d prior h n i)
    (hnoiseExp : ∀ n<T, ∀ i t, Integrable (fun ω => Real.exp (t * h.noise n ω i)) μ)
    (hnoiseMGF : ∀ n<T, ∀ i t,
      μ[fun ω => Real.exp (t * h.noise n ω i) | h.pre n] ≤ᵐ[μ]
        fun _ => Real.exp (σ ^ 2 * t ^ 2 / 2)) :
    FiniteLaws o d prior h (μ := μ) (σ := σ) (σe := Δ/2) where
  strong_categorical := hsample
  noise_exp_integrable := hnoiseExp
  noise_conditional_mgf := hnoiseMGF
  encoder_conditional_mgf := CNDHorizon.adjacent_encoder_conditional_mgf
    h Δ hΔ cell hcellm hcellrange hcell hcenter
  encoder_centered n hn i := by
    have hpre : h.pre n ≤ m₀ := (h.pre_le_next n hn).trans (ℱ.le _)
    have hA : Measurable (h.action n) := (h.action_measurable n hn).mono (ℱ.le _) le_rfl
    have hN : Measurable (h.noise n) := (h.noise_measurable n hn).mono (ℱ.le _) le_rfl
    have hm : h.afterNoiseAction n ≤ m₀ := sup_le (sup_le hpre hA.comap_le) hN.comap_le
    have ht := condExp_condExp_of_le (μ := μ) (f := h.error n i)
      (show h.afterAction n ≤ h.afterNoiseAction n from le_sup_left) hm
    exact ht.symm.trans ((condExp_congr_ae (hcenter n hn i)).trans (by
      simp only [condExp_zero]
      exact Filter.Eventually.of_forall fun _ => rfl))

def primitive (g : CNDProcess.SG.Inputs ℱ θ R M D) : Primitive ℱ θ R M D where
  R_nonneg := g.R_nonneg
  M_nonneg := g.M_nonneg
  D_nonneg := g.D_nonneg
  theta_range := g.theta_range
  pre := g.pre
  afterAction := g.afterAction
  encoded := g.encoded
  past_le_pre := g.past_le_pre
  pre_le_action := fun _ => le_sup_left
  action_le_next := g.afterAction_le_next
  pre_le_encoded := fun _ => le_sup_left
  encoded_le_next := g.encoded_le_next
  p := ExponentialStochastic.runProbability o d prior g.feedback
  action := g.action
  publicCost := g.publicCost
  drift := g.drift
  error := g.error
  p_measurable := ExponentialStochastic.runProbability_measurable o d prior g.feedback
  p_nonneg := fun n ω i => (ExponentialStochastic.runProbability_simplex o d prior g.feedback n ω).1 i
  p_sum := fun n ω => (ExponentialStochastic.runProbability_simplex o d prior g.feedback n ω).2
  action_measurable := g.action_measurable_after
  public_measurable := g.public_measurable
  drift_measurable := g.drift_measurable
  drift_range := g.drift_range
  error_encoded := g.error_encoded
  error_bound := g.error_bound

def publicShadow (hm : FiniteLaws o d prior h (μ := μ) (σ := σ) (σe := σe)) :
    CNDProbability.M1Model ℱ μ θ R M D :=
  (primitive o d prior h.extend).stopped T CNDHorizon.root
    (by
      intro n hn i
      change μ[PairConfidence.actionIndicator (h.extend.action n) i | h.extend.encoded n] =ᵐ[μ]
        ExponentialStochastic.runProbability o d prior h.extend.feedback n i
      rw [finite_probability_prefix o d prior h n hn.le]
      simpa only [SGInputs.extend, if_pos hn, CNDProcess.SG.Inputs.encoded, SGInputs.encoded]
        using hm.strong_categorical n hn i)
    (by
      intro n hn i
      simpa only [primitive, CNDProcess.SG.Inputs.afterAction, SGInputs.extend, if_pos hn,
        SGInputs.afterAction] using hm.encoder_centered n hn i)

def model (hm : FiniteLaws o d prior h (μ := μ) (σ := σ) (σe := σe)) :
    CNDProbability.SGModel ℱ μ θ R M D σ σe where
  toM1Model := publicShadow o d prior h hm
  afterNoiseAction n := if n<T then h.extend.afterNoiseAction n else ℱ n
  action_le_noiseAction n := by
    simp only [publicShadow, Primitive.stopped, primitive]
    split_ifs; exact le_sup_left; exact le_rfl
  noiseAction_le_next n := by
    split_ifs; exact h.extend.afterNoiseAction_le_next n; exact ℱ.mono (Nat.le_succ n)
  noise n i := if n<T then fun ω => h.extend.noise n ω i else fun _ => 0
  noise_afterAction_measurable n i := by
    split_ifs; exact h.extend.noise_afterNoiseAction n i; exact measurable_const
  noise_encoded_measurable n i := by
    simp only [publicShadow, Primitive.stopped, primitive]
    split_ifs; exact h.extend.noise_encoded n i; exact measurable_const
  noise_exp_integrable n i t := by
    by_cases hn : n<T
    · simpa only [SGInputs.extend, if_pos hn] using hm.noise_exp_integrable n hn i t
    · simp only [if_neg hn, mul_zero]; exact integrable_const _
  noise_conditional_mgf n i t := by
    by_cases hn : n<T
    · simpa only [publicShadow, Primitive.stopped, primitive, SGInputs.extend, if_pos hn]
        using hm.noise_conditional_mgf n hn i t
    · simp only [publicShadow, Primitive.stopped, primitive, if_neg hn, mul_zero, Real.exp_zero,
        condExp_const (ℱ.le n)]
      exact Filter.Eventually.of_forall fun _ => Real.one_le_exp (by positivity)
  encoder_conditional_mgf n i t := by
    by_cases hn : n<T
    · simpa only [publicShadow, Primitive.stopped, primitive, SGInputs.extend, if_pos hn,
        CNDProcess.SG.Inputs.afterNoiseAction, CNDProcess.SG.Inputs.afterAction,
        SGInputs.afterNoiseAction, SGInputs.afterAction] using hm.encoder_conditional_mgf n hn i t
    · simp only [publicShadow, Primitive.stopped, primitive, if_neg hn, mul_zero, Real.exp_zero,
        condExp_const (ℱ.le n)]
      exact Filter.Eventually.of_forall fun _ => Real.one_le_exp (by positivity)

variable (hm : FiniteLaws o d prior h (μ := μ) (σ := σ) (σe := σe))

theorem model_p {n : ℕ} (hn : n<T) :
    (model o d prior h hm).p n = ExponentialStochastic.runProbability o d prior h.extend.feedback n := by
  funext i ω
  simp only [model, publicShadow, Primitive.stopped, primitive, stopP, if_pos hn]

theorem model_finite_p {n : ℕ} (hn : n<T) :
    (model o d prior h hm).p n = finiteProbability o d prior h n := by
  rw [model_p o d prior h hm hn, finite_probability_prefix o d prior h n hn.le]

theorem model_action {n : ℕ} (hn : n<T) : (model o d prior h hm).action n=h.action n := by
  simp only [model, publicShadow, Primitive.stopped, primitive, stop, SGInputs.extend, if_pos hn]

theorem model_public {n : ℕ} (hn : n<T) : (model o d prior h hm).publicCost n=h.publicCost n := by
  funext i ω
  simp only [model, publicShadow, Primitive.stopped, primitive, SGInputs.extend, if_pos hn]

theorem model_error {n : ℕ} (hn : n<T) : (model o d prior h hm).error n=h.error n := by
  funext i ω
  simp only [model, publicShadow, Primitive.stopped, primitive, SGInputs.extend, if_pos hn]

theorem model_drift {n : ℕ} (hn : n<T) : (model o d prior h hm).drift n=h.drift n := by
  simp only [model, publicShadow, Primitive.stopped, primitive, stop, SGInputs.extend, if_pos hn]

theorem model_noise {n : ℕ} (hn : n<T) (i : ι) :
    (model o d prior h hm).noise n i = fun ω => h.noise n ω i := by
  simp only [model, SGInputs.extend, if_pos hn]

/-- This is the genuine observed noisy residual, not the bounded M1 shadow
residual. It is the feedback used by `finite_run_prefix`. -/
theorem model_observed_residual {n : ℕ} (hn : n<T) :
    (fun ω => θ ((model o d prior h hm).action n ω) +
      (model o d prior h hm).drift n ω +
      (model o d prior h hm).noise n ((model o d prior h hm).action n ω) ω -
      (model o d prior h hm).error n ((model o d prior h hm).action n ω) ω) = h.residual n := by
  funext ω
  simp only [model_action o d prior h hm hn, model_drift o d prior h hm hn,
    model_noise o d prior h hm hn, model_error o d prior h hm hn]
  unfold SGInputs.residual SGInputs.physical SGInputs.broadcast
  ring

end Part2.ExponentialSGStochastic
