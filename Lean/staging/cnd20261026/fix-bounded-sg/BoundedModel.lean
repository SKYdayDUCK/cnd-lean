import staging.cnd20261026.«fix-bounded-sg».FiniteInputs
import staging.cnd20261024.main.ConfidenceBridge

noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
namespace Part2.CNDHorizon.Bounded
open CNDProcess
variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ}

/-- Internal finite laws on deterministically completed measurable data. -/
structure Laws (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ θ R M D) (μ : Measure Ω) (T : ℕ) : Prop where
  strong_categorical : ∀ n < T, ∀ i,
    μ[PairConfidence.actionIndicator (h.action n) i | h.encoded n] =ᵐ[μ] runProbability o d h.feedback n i
  encoder_centered : ∀ n < T, ∀ i, μ[h.error n i | h.afterAction n] =ᵐ[μ] fun _ => 0

def primitive (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ θ R M D) : Primitive ℱ θ R M D where
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

def model (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ θ R M D) (hm : Laws o d h μ T) : CNDProbability.M1Model ℱ μ θ R M D :=
  (primitive o d h).stopped T root hm.strong_categorical hm.encoder_centered

@[simp] theorem model_p (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ θ R M D) (hm : Laws o d h μ T) {n : ℕ} (hn : n<T) :
    (model o d h hm).p n=runProbability o d h.feedback n := by
  funext i ω; simp only [model, Primitive.stopped, primitive, stopP, if_pos hn]

@[simp] theorem model_action (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ θ R M D) (hm : Laws o d h μ T) {n : ℕ} (hn : n<T) :
    (model o d h hm).action n=h.action n := by
  simp only [model, Primitive.stopped, primitive, stop, if_pos hn]

@[simp] theorem model_public (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ θ R M D) (hm : Laws o d h μ T) {n : ℕ} (hn : n<T) :
    (model o d h hm).publicCost n=h.publicCost n := by funext i ω; exact if_pos hn

@[simp] theorem model_error (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ θ R M D) (hm : Laws o d h μ T) {n : ℕ} (hn : n<T) :
    (model o d h hm).error n=h.error n := by funext i ω; exact if_pos hn

@[simp] theorem model_drift (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ θ R M D) (hm : Laws o d h μ T) {n : ℕ} (hn : n<T) :
    (model o d h hm).drift n=h.drift n := by
  simp only [model, Primitive.stopped, primitive, stop, if_pos hn]

def actualM1Model {d K : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K)] {θ : Fin K → ℝ} {L W : ℝ}
    (h : PotentialInputs ℱ θ R M D) (hW : 0≤W) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hm : Laws (concreteMaps (R+M+D) L R W h.R_nonneg hW) (treeData d K W R) h μ T) :
    CNDProbability.M1Model ℱ μ θ R M D := model _ _ h hm

end Part2.CNDHorizon.Bounded

namespace Part2.CNDHorizon
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem information_prefix (p q : ℕ → ι → ℝ) (n : ℕ)
    (hpq : ∀ t<n, p t=q t) : CNDPhysical.information p n=CNDPhysical.information q n := by
  unfold CNDPhysical.information
  congr 1
  apply sum_congr rfl
  intro t ht
  rw [hpq t (mem_range.mp ht)]

theorem pairRadius_prefix (p q : ℕ → ι → ℝ) (n : ℕ) (H L R : ℝ)
    (hpq : ∀ t<n, p t=q t) : CNDPhysical.pairRadius p n H L R=CNDPhysical.pairRadius q n H L R := by
  unfold CNDPhysical.pairRadius CNDPhysical.resistance
  rw [information_prefix p q n hpq]

theorem radius_prefix (p q : ℕ → ι → ℝ) (n : ℕ) (H L R : ℝ)
    (hpq : ∀ t<n, p t=q t) :
    CNDPhysical.actualSaturatedRadius p n H L R=CNDPhysical.actualSaturatedRadius q n H L R := by
  unfold CNDPhysical.actualSaturatedRadius
  rw [pairRadius_prefix p q n H L R hpq]

end Part2.CNDHorizon
