import staging.cnd20261026.«fix-bounded-sg».SGModel

noncomputable section
open MeasureTheory Filter Finset
open scoped ProbabilityTheory
namespace Part2.CNDHorizon
open CNDProcess
variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ} {T : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def rawProbability (o : DecisionMaps ι) (d : ExpertData ι E)
    (A : ℕ → Ω → ι) (Y : ℕ → Ω → ℝ) (b : ℕ → Ω → Vec ι)
    (n : ℕ) (i : ι) (ω : Ω) : ℝ := probability o d n (rawRun o d A Y b n ω) i

namespace BoundedInputs
variable (h : BoundedInputs ℱ θ R M D T)
def encoded (n : ℕ) : MeasurableSpace Ω := h.pre n ⊔ MeasurableSpace.comap (h.seed n) inferInstance
def afterAction (n : ℕ) : MeasurableSpace Ω := h.pre n ⊔ MeasurableSpace.comap (h.action n) inferInstance
def actualP (o : DecisionMaps ι) (d : ExpertData ι E) : ℕ → ι → Ω → ℝ :=
  rawProbability o d h.action h.residual h.broadcast
theorem probability_prefix (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ) (hn : n≤T) :
    runProbability o d h.extend.feedback n=h.actualP o d n := by
  funext i ω
  simp only [runProbability,actualP,rawProbability,congrFun (h.extend_run o d n hn) ω]
end BoundedInputs

structure BoundedLaws (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : BoundedInputs ℱ θ R M D T) (μ : Measure Ω) : Prop where
  strong_categorical : ∀ n<T, ∀ i,
    μ[PairConfidence.actionIndicator (h.action n) i | h.encoded n] =ᵐ[μ] h.actualP o d n i
  encoder_centered : ∀ n<T, ∀ i, μ[h.error n i | h.afterAction n] =ᵐ[μ] fun _ => 0

def BoundedLaws.toInternal {o : DecisionMaps ι} {d : ExpertData ι E}
    {h : BoundedInputs ℱ θ R M D T} (hm : BoundedLaws o d h μ) : Bounded.Laws o d h.extend μ T where
  strong_categorical n hn i := by
    rw [h.probability_prefix o d n (Nat.le_of_lt hn)]
    simpa only [PotentialInputs.encoded,BoundedInputs.extend,if_pos hn,BoundedInputs.encoded] using
      hm.strong_categorical n hn i
  encoder_centered n hn i := by
    simpa only [PotentialInputs.afterAction,BoundedInputs.extend,if_pos hn,BoundedInputs.afterAction] using
      hm.encoder_centered n hn i

namespace SGInputs
variable (h : SGInputs ℱ θ R M D T)
def encoded (n : ℕ) : MeasurableSpace Ω := h.pre n ⊔
  (MeasurableSpace.comap (h.noise n) inferInstance ⊔ MeasurableSpace.comap (h.encodingSeed n) inferInstance)
def afterAction (n : ℕ) : MeasurableSpace Ω := h.pre n ⊔ MeasurableSpace.comap (h.action n) inferInstance
def afterNoiseAction (n : ℕ) : MeasurableSpace Ω := h.afterAction n ⊔ MeasurableSpace.comap (h.noise n) inferInstance
def actualP (o : DecisionMaps ι) (d : ExpertData ι E) : ℕ → ι → Ω → ℝ :=
  rawProbability o d h.action h.residual h.broadcast
theorem probability_prefix (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ) (hn : n≤T) :
    runProbability o d h.extend.feedback n=h.actualP o d n := by
  funext i ω
  simp only [runProbability,actualP,rawProbability,congrFun (h.extend_run o d n hn) ω]
end SGInputs

structure SGLaws (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : SGInputs ℱ θ R M D T) (μ : Measure Ω) (σ σe : ℝ) : Prop where
  strong_categorical : ∀ n<T, ∀ i,
    μ[PairConfidence.actionIndicator (h.action n) i | h.encoded n] =ᵐ[μ] h.actualP o d n i
  encoder_centered : ∀ n<T, ∀ i, μ[h.error n i | h.afterAction n] =ᵐ[μ] fun _ => 0
  noise_exp_integrable : ∀ n<T, ∀ i t, Integrable (fun ω => Real.exp (t*h.noise n ω i)) μ
  noise_conditional_mgf : ∀ n<T, ∀ i t,
    μ[fun ω => Real.exp (t*h.noise n ω i) | h.pre n] ≤ᵐ[μ] fun _ => Real.exp (σ^2*t^2/2)
  encoder_conditional_mgf : ∀ n<T, ∀ i t,
    μ[fun ω => Real.exp (t*h.error n i ω) | h.afterNoiseAction n] ≤ᵐ[μ] fun _ => Real.exp (σe^2*t^2/2)

def SGLaws.toInternal {o : DecisionMaps ι} {d : ExpertData ι E}
    {h : SGInputs ℱ θ R M D T} {σ σe : ℝ} (hm : SGLaws o d h μ σ σe) :
    SG.Laws o d h.extend μ σ σe T where
  strong_categorical n hn i := by
    rw [h.probability_prefix o d n (Nat.le_of_lt hn)]
    simpa only [CNDProcess.SG.Inputs.encoded,SGInputs.extend,if_pos hn,SGInputs.encoded] using
      hm.strong_categorical n hn i
  encoder_centered n hn i := by
    simpa only [CNDProcess.SG.Inputs.afterAction,SGInputs.extend,if_pos hn,SGInputs.afterAction] using
      hm.encoder_centered n hn i
  noise_exp_integrable n hn i t := by
    simpa only [SGInputs.extend,if_pos hn] using hm.noise_exp_integrable n hn i t
  noise_conditional_mgf n hn i t := by
    simpa only [SGInputs.extend,if_pos hn] using hm.noise_conditional_mgf n hn i t
  encoder_conditional_mgf n hn i t := by
    simpa only [CNDProcess.SG.Inputs.afterNoiseAction,CNDProcess.SG.Inputs.afterAction,
      SGInputs.extend,if_pos hn,SGInputs.afterNoiseAction,SGInputs.afterAction] using hm.encoder_conditional_mgf n hn i t
end Part2.CNDHorizon
