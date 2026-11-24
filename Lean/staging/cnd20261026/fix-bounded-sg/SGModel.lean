import staging.cnd20261026.«fix-bounded-sg».BoundedModel
import staging.cnd20261024.net.SGUniformDirections

noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory NNReal
namespace Part2.CNDHorizon.SG
open CNDProcess CNDProcess.SG
variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D σ σe : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ}

structure Laws (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : Inputs ℱ θ R M D) (μ : Measure Ω) (σ σe : ℝ) (T : ℕ) : Prop where
  strong_categorical : ∀ n<T, ∀ i,
    μ[PairConfidence.actionIndicator (h.action n) i | h.encoded n] =ᵐ[μ] runProbability o d h.feedback n i
  encoder_centered : ∀ n<T, ∀ i, μ[h.error n i | h.afterAction n] =ᵐ[μ] fun _ => 0
  noise_exp_integrable : ∀ n<T, ∀ i t, Integrable (fun ω => Real.exp (t*h.noise n ω i)) μ
  noise_conditional_mgf : ∀ n<T, ∀ i t,
    μ[fun ω => Real.exp (t*h.noise n ω i) | h.pre n] ≤ᵐ[μ] fun _ => Real.exp (σ^2*t^2/2)
  encoder_conditional_mgf : ∀ n<T, ∀ i t,
    μ[fun ω => Real.exp (t*h.error n i ω) | h.afterNoiseAction n] ≤ᵐ[μ] fun _ => Real.exp (σe^2*t^2/2)

def primitive (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : Inputs ℱ θ R M D) : Primitive ℱ θ R M D where
  R_nonneg := h.R_nonneg
  M_nonneg := h.M_nonneg
  D_nonneg := h.D_nonneg
  theta_range := h.theta_range
  pre := h.pre
  afterAction := h.afterAction
  encoded := h.encoded
  past_le_pre := h.past_le_pre
  pre_le_action := fun _ => le_sup_left
  action_le_next := h.afterAction_le_next
  pre_le_encoded := fun _ => le_sup_left
  encoded_le_next := h.encoded_le_next
  p := runProbability o d h.feedback
  action := h.action
  publicCost := h.publicCost
  drift := h.drift
  error := h.error
  p_measurable := runProbability_measurable o d h.feedback
  p_nonneg := fun n ω i => (runProbability_simplex o d h.feedback n ω).1 i
  p_sum := fun n ω => (runProbability_simplex o d h.feedback n ω).2
  action_measurable := h.action_measurable_after
  public_measurable := h.public_measurable
  drift_measurable := h.drift_measurable
  drift_range := h.drift_range
  error_encoded := h.error_encoded
  error_bound := h.error_bound


def publicShadow (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : Inputs ℱ θ R M D) (hm : Laws o d h μ σ σe T) : CNDProbability.M1Model ℱ μ θ R M D :=
  (primitive o d h).stopped T root hm.strong_categorical hm.encoder_centered

def model (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : Inputs ℱ θ R M D) (hm : Laws o d h μ σ σe T) : CNDProbability.SGModel ℱ μ θ R M D σ σe where
  toM1Model := publicShadow o d h hm
  afterNoiseAction n := if n<T then h.afterNoiseAction n else ℱ n
  action_le_noiseAction n := by
    simp only [publicShadow,Primitive.stopped,primitive]
    split_ifs; exact le_sup_left; exact le_rfl
  noiseAction_le_next n := by split_ifs; exact h.afterNoiseAction_le_next n; exact ℱ.mono (Nat.le_succ n)
  noise n i := if n<T then fun ω => h.noise n ω i else fun _ => 0
  noise_afterAction_measurable n i := by split_ifs; exact h.noise_afterNoiseAction n i; exact measurable_const
  noise_encoded_measurable n i := by
    simp only [publicShadow,Primitive.stopped,primitive]
    split_ifs; exact h.noise_encoded n i; exact measurable_const
  noise_exp_integrable n i t := by
    by_cases hn : n<T
    · simpa only [if_pos hn] using hm.noise_exp_integrable n hn i t
    · simp only [if_neg hn,mul_zero]; exact integrable_const _
  noise_conditional_mgf n i t := by
    by_cases hn : n<T
    · simpa only [publicShadow,Primitive.stopped,primitive,if_pos hn] using hm.noise_conditional_mgf n hn i t
    · simp only [publicShadow,Primitive.stopped,primitive,if_neg hn,mul_zero,Real.exp_zero,
        condExp_const (ℱ.le n)]
      exact Filter.Eventually.of_forall fun _ => Real.one_le_exp (by positivity)
  encoder_conditional_mgf n i t := by
    by_cases hn : n<T
    · simpa only [publicShadow,Primitive.stopped,primitive,if_pos hn] using hm.encoder_conditional_mgf n hn i t
    · simp only [publicShadow,Primitive.stopped,primitive,if_neg hn,mul_zero,Real.exp_zero,
        condExp_const (ℱ.le n)]
      exact Filter.Eventually.of_forall fun _ => Real.one_le_exp (by positivity)

@[simp] theorem model_p (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : Inputs ℱ θ R M D) (hm : Laws o d h μ σ σe T) {n : ℕ} (hn : n<T) :
    (model o d h hm).p n=runProbability o d h.feedback n := by
  funext i ω
  simp only [model,publicShadow,Primitive.stopped,primitive,stopP,if_pos hn]

@[simp] theorem model_action (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : Inputs ℱ θ R M D) (hm : Laws o d h μ σ σe T) {n : ℕ} (hn : n<T) :
    (model o d h hm).action n=h.action n := by
  simp only [model,publicShadow,Primitive.stopped,primitive,stop,if_pos hn]

def actualModel {d K : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K)] {θ : Fin K → ℝ}
    (h : Inputs ℱ θ R M D) (ν : ℝ≥0) (Lc W : ℝ) (hW : 0≤W)
    (hm : Laws (maps ν Lc R M W h.R_nonneg hW) (treeData d K W R) h μ σ σe T) :
    CNDProbability.SGModel ℱ μ θ R M D σ σe := model _ _ h hm

end Part2.CNDHorizon.SG
