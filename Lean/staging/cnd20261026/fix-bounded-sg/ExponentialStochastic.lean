import staging.cnd20261026.«fix-bounded-sg».FiniteLaws
import staging.cnd20261024.process.ActualInvariants

/-! Actual exponential state recursion and its original finite-feedback M1
instance. The raw categorical/encoder laws are the sampling protocol at the
new computed probability, never inherited from the different Prod run. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 1600000

namespace Part2.ExponentialStochastic
open CNDProcess CNDHorizon
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [Nonempty E]

def initial (prior : E → ℝ) : State ι E := ((initialState (ι := ι) (E := E)).1, prior)

/-- Same sufficient-statistic update and decision maps, with the actual
exponential excess update and a separate identity for every preset expert. -/
def step (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ)
    (s : State ι E) (A : ι) (Y : ℝ) (b : Vec ι) : State ι E :=
  ((CNDProcess.step o d n s A Y b).1, fun e =>
    if d.W = 0 then s.2 e else if d.active n e then
      s.2 e * Real.exp (d.eta e * (meanExpertLoss o d n s b - expertLoss o d n s b e))
    else s.2 e)

section Measurability
variable {Ω : Type*} [m : MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {s : Ω → State ι E} (hs : Measurable s) (o : DecisionMaps ι) (d : ExpertData ι E)

include hs in
theorem step_measurable (n : ℕ) {A : Ω → ι} (hA : Measurable A)
    {Y : Ω → ℝ} (hY : Measurable Y) {b : Ω → Vec ι} (hb : Measurable b) :
    Measurable (fun ω => step o d n (s ω) (A ω) (Y ω) (b ω)) := by
  refine (measurable_fst.comp (CNDProcess.step_measurable hs o d n hA hY hb)).prodMk ?_
  apply measurable_pi_lambda
  intro e
  have hw := (measurable_pi_apply e).comp (measurable_snd.comp hs)
  split_ifs
  · exact hw
  · exact hw.mul ((((meanExpertLoss_measurable hs o d n hb).sub
      (expertLoss_measurable hs o d n hb e)).const_mul _).exp)
  · exact hw
end Measurability

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def rawRun (o : DecisionMaps ι) (d : ExpertData ι E) (prior : E → ℝ)
    (A : ℕ → Ω → ι) (Y : ℕ → Ω → ℝ) (b : ℕ → Ω → Vec ι) : ℕ → Ω → State ι E
  | 0, _ => initial prior
  | n+1, ω => step o d n (rawRun o d prior A Y b n ω) (A n ω) (Y n ω) (b n ω)

def run (o : DecisionMaps ι) (d : ExpertData ι E) (prior : E → ℝ)
    {ℱ : Filtration ℕ m₀} (f : Feedback (ι := ι) ℱ) : ℕ → Ω → State ι E :=
  rawRun o d prior f.action f.residual f.broadcast

theorem rawRun_prefix (o : DecisionMaps ι) (d : ExpertData ι E) (prior : E → ℝ)
    (A A' : ℕ → Ω → ι) (Y Y' : ℕ → Ω → ℝ) (b b' : ℕ → Ω → Vec ι)
    (T : ℕ) (hA : ∀ t<T, A t=A' t) (hY : ∀ t<T, Y t=Y' t) (hb : ∀ t<T, b t=b' t)
    (n : ℕ) (hn : n≤T) :
    rawRun o d prior A Y b n=rawRun o d prior A' Y' b' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ω
    simp only [rawRun, congrFun (ih (by omega)) ω, hA n (by omega), hY n (by omega), hb n (by omega)]

variable {ℱ : Filtration ℕ m₀}
  (o : DecisionMaps ι) (d : ExpertData ι E) (prior : E → ℝ) (f : Feedback (ι := ι) ℱ)

theorem run_measurable (n : ℕ) : Measurable[ℱ n] (run o d prior f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact step_measurable (m := ℱ (n+1)) (ih.mono (ℱ.mono (Nat.le_succ n)) le_rfl)
      o d n (f.action_measurable n) (f.residual_measurable n) (f.broadcast_measurable n)

def runProbability (n : ℕ) (i : ι) (ω : Ω) : ℝ := probability o d n (run o d prior f n ω) i

theorem runProbability_measurable (n : ℕ) (i : ι) :
    Measurable[ℱ n] (runProbability o d prior f n i) :=
  (measurable_pi_apply i).comp (probability_measurable (m := ℱ n) (run_measurable o d prior f n) o d n)

theorem runProbability_simplex (n : ℕ) (ω : Ω) :
    (fun i => runProbability o d prior f n i ω) ∈ CND.simplex := o.prox_simplex _

theorem run_center_measurable (n : ℕ) (i : ι) :
    Measurable[ℱ n] (fun ω => confidence o d (run o d prior f n ω) i) :=
  (measurable_pi_apply i).comp (confidence_measurable (m := ℱ n) (run_measurable o d prior f n) o d)

theorem run_radius_measurable (n : ℕ) (i j : ι) :
    Measurable[ℱ n] (fun ω => radius o d (run o d prior f n ω) i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (radius_measurable (m := ℱ n) (run_measurable o d prior f n) o d))

/-- Positive exponential weights require no learning-rate cap and no loss
span; the statement includes all preset sleeping and retired experts. -/
theorem run_weights_positive (hprior : ∀ e, 0 < prior e) (n : ℕ) (ω : Ω) :
    ∀ e, 0 < (run o d prior f n ω).2 e := by
  induction n with
  | zero => exact hprior
  | succ n ih =>
    intro e
    change 0 < (step o d n (run o d prior f n ω) _ _ _).2 e
    dsimp only [step]
    split_ifs
    · exact ih e
    · exact mul_pos (ih e) (Real.exp_pos _)
    · exact ih e

theorem run_suggestion_simplex (hprior : ∀ e, 0 < prior e)
    (heta : ∀ e, 0 < d.eta e) (hW : d.W ≠ 0) (n : ℕ) (ω : Ω)
    (hactive : (activeSet d n).Nonempty) :
    suggestion d n (run o d prior f n ω) ∈ CND.simplex :=
  suggestion_simplex_of_positive d hW n _ hactive heta (run_weights_positive o d prior f hprior n ω)

theorem run_suggestion_positive (hprior : ∀ e, 0 < prior e)
    (heta : ∀ e, 0 < d.eta e) (hW : d.W ≠ 0) (n : ℕ) (ω : Ω)
    (k : ι) (root : E) (hroot : root ∈ activeSet d n) (harm : d.arm root = k) :
    0 < suggestion d n (run o d prior f n ω) k := by
  let s := run o d prior f n ω
  have hw := run_weights_positive o d prior f hprior n ω
  have hd := Prod.denominator_pos (activeSet d n) d.eta s.2
    (fun e _ => heta e) (fun e _ => hw e) ⟨root,hroot⟩
  have hn (e : E) : 0 ≤ Prod.coefficient d.eta s.2 e * pureAdvice d e k := by
    unfold pureAdvice
    split_ifs
    · simpa only [mul_one, Prod.coefficient] using (mul_pos (heta e) (hw e)).le
    · simp only [mul_zero, le_refl]
  have hs := single_le_sum (fun e _ => hn e) hroot
  have hp : 0 < ∑ e ∈ activeSet d n, Prod.coefficient d.eta s.2 e * pureAdvice d e k := by
    apply lt_of_lt_of_le (mul_pos (heta root) (hw root))
    simpa [pureAdvice, harm, Prod.coefficient] using hs
  rw [suggestion_eq_pure_mixture d hW n s]
  exact div_pos hp hd

section FiniteBounded
variable {θ : ι → ℝ} {R M D : ℝ} {T : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (h : BoundedInputs ℱ θ R M D T)

def finiteProbability (n : ℕ) (i : ι) (ω : Ω) : ℝ :=
  probability o d n (rawRun o d prior h.action h.residual h.broadcast n ω) i

theorem finite_run_prefix (n : ℕ) (hn : n≤T) :
    run o d prior h.extend.feedback n = rawRun o d prior h.action h.residual h.broadcast n := by
  exact rawRun_prefix o d prior _ _ _ _ _ _ T
    (fun t ht => h.extend_action ht) (fun t ht => h.extend_residual ht)
    (fun t ht => h.extend_broadcast ht) n hn

theorem finite_probability_prefix (n : ℕ) (hn : n≤T) :
    runProbability o d prior h.extend.feedback n = finiteProbability o d prior h n := by
  funext i ω
  simp only [runProbability, finiteProbability, congrFun (finite_run_prefix o d prior h n hn) ω]

/-- Exactly the two finite original sampling/encoding protocol laws, now
evaluated at the new actual exponential probability. The old Prod laws have
a different RHS and are not used to establish these assumptions. -/
structure FiniteLaws : Prop where
  strong_categorical : ∀ n<T, ∀ i,
    μ[PairConfidence.actionIndicator (h.action n) i | h.encoded n] =ᵐ[μ]
      finiteProbability o d prior h n i
  encoder_centered : ∀ n<T, ∀ i, μ[h.error n i | h.afterAction n] =ᵐ[μ] fun _ => 0

def primitive (g : PotentialInputs ℱ θ R M D) : Primitive ℱ θ R M D where
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
  p := runProbability o d prior g.feedback
  action := g.action
  publicCost := g.publicCost
  drift := g.drift
  error := g.error
  p_measurable := runProbability_measurable o d prior g.feedback
  p_nonneg := fun n ω i => (runProbability_simplex o d prior g.feedback n ω).1 i
  p_sum := fun n ω => (runProbability_simplex o d prior g.feedback n ω).2
  action_measurable := g.action_measurable_after
  public_measurable := g.public_measurable
  drift_measurable := g.drift_measurable
  drift_range := g.drift_range
  error_encoded := g.error_encoded
  error_bound := g.error_bound

def model (hm : FiniteLaws o d prior h (μ := μ)) : CNDProbability.M1Model ℱ μ θ R M D :=
  (primitive o d prior h.extend).stopped T CNDHorizon.root
    (by
      intro n hn i
      change μ[PairConfidence.actionIndicator (h.extend.action n) i | h.extend.encoded n] =ᵐ[μ]
        runProbability o d prior h.extend.feedback n i
      rw [finite_probability_prefix o d prior h n hn.le]
      simpa only [BoundedInputs.extend, if_pos hn, PotentialInputs.encoded, BoundedInputs.encoded]
        using hm.strong_categorical n hn i)
    (by
      intro n hn i
      simpa only [primitive, PotentialInputs.afterAction, BoundedInputs.extend, if_pos hn,
        BoundedInputs.afterAction] using hm.encoder_centered n hn i)

variable (hm : FiniteLaws o d prior h (μ := μ))

theorem model_p {n : ℕ} (hn : n<T) :
    (model o d prior h hm).p n = runProbability o d prior h.extend.feedback n := by
  funext i ω
  simp only [model, Primitive.stopped, primitive, stopP, if_pos hn]

theorem model_finite_p {n : ℕ} (hn : n<T) :
    (model o d prior h hm).p n = finiteProbability o d prior h n := by
  rw [model_p o d prior h hm hn, finite_probability_prefix o d prior h n hn.le]

theorem model_action {n : ℕ} (hn : n<T) : (model o d prior h hm).action n=h.action n := by
  simp only [model, Primitive.stopped, primitive, stop, BoundedInputs.extend, if_pos hn]

theorem model_public {n : ℕ} (hn : n<T) : (model o d prior h hm).publicCost n=h.publicCost n := by
  funext i ω
  simp only [model, Primitive.stopped, primitive, BoundedInputs.extend, if_pos hn]

theorem model_error {n : ℕ} (hn : n<T) : (model o d prior h hm).error n=h.error n := by
  funext i ω
  simp only [model, Primitive.stopped, primitive, BoundedInputs.extend, if_pos hn]

theorem model_drift {n : ℕ} (hn : n<T) : (model o d prior h hm).drift n=h.drift n := by
  simp only [model, Primitive.stopped, primitive, stop, BoundedInputs.extend, if_pos hn]

/-- The stochastic library's selected residual is the original finite
physical observation minus the one reconstructed public observation. -/
theorem model_observed_residual {n : ℕ} (hn : n<T) :
    (model o d prior h hm).toSamplingModel.residual n = h.residual n := by
  funext ω
  simp only [PairConfidence.SamplingModel.residual, model_action o d prior h hm hn,
    model_public o d prior h hm hn, model_drift o d prior h hm hn, model_error o d prior h hm hn]
  rfl
end FiniteBounded

#print axioms run_measurable
#print axioms runProbability_measurable
#print axioms run_weights_positive
#print axioms run_suggestion_positive
#print axioms model
#print axioms model_finite_p
#print axioms model_observed_residual
end Part2.ExponentialStochastic
