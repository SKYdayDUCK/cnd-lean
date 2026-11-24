import staging.cnd20261026.«fix-bounded-sg».ExponentialSGStochastic
import staging.cnd20261026.«fix-bounded-sg».ExponentialStatistics
import staging.cnd20261024.net.SGUniformDirections
import staging.cnd20261024.main.ConfidenceBridge

/-! The canonical SG confidence event belongs to the actual exponential
feedback run. The generic SG score theorem is identified with the shared
computed statistics; no confidence conclusion is supplied as a model field. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators Matrix NNReal
set_option maxHeartbeats 1600000

namespace Part2.ExponentialSGConfidence
open CNDProcess CNDHorizon

section Generic
variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [Nonempty E]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D σ σe : ℝ} {T : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (o : DecisionMaps ι) (d : ExpertData ι E) (prior : E → ℝ)
  (h : SGInputs ℱ θ R M D T)
  (hm : ExponentialSGStochastic.FiniteLaws o d prior h (μ := μ) (σ := σ) (σe := σe))

theorem actualScoreSum_eq_runS (hR : d.R ≠ 0) (n : ℕ) (hn : n≤T) (ω : Ω) :
    CNDSGNet.actualScoreSum (ExponentialSGStochastic.model o d prior h hm) n ω =
      fun i => ExponentialStochastic.runS o d prior h.extend.feedback n i ω := by
  funext i
  rw [ExponentialStochastic.actual_statistic_identity o d prior h.extend.feedback hR]
  unfold CNDSGNet.actualScoreSum
  apply sum_congr rfl
  intro t ht
  have htT : t<T := lt_of_lt_of_le (mem_range.mp ht) hn
  have hp := congrArg (fun p => p i ω) (ExponentialSGStochastic.model_p o d prior h hm htT)
  dsimp only at hp
  have ha := congrFun (ExponentialSGStochastic.model_action o d prior h hm htT) ω
  have hy := congrFun (ExponentialSGStochastic.model_observed_residual o d prior h hm htT) ω
  have heA := congrFun (h.extend_action htT) ω
  have heY := congrFun (h.extend_residual htT) ω
  change ((if (ExponentialSGStochastic.model o d prior h hm).action t ω = i then 1 else 0) -
    (ExponentialSGStochastic.model o d prior h hm).p t i ω) *
      (θ ((ExponentialSGStochastic.model o d prior h hm).action t ω) +
        (ExponentialSGStochastic.model o d prior h hm).drift t ω +
        (ExponentialSGStochastic.model o d prior h hm).noise t
          ((ExponentialSGStochastic.model o d prior h hm).action t ω) ω -
        (ExponentialSGStochastic.model o d prior h hm).error t
          ((ExponentialSGStochastic.model o d prior h hm).action t ω) ω) =
    ((if h.extend.action t ω = i then 1 else 0) -
      ExponentialStochastic.runProbability o d prior h.extend.feedback t i ω) * h.extend.residual t ω
  rw [hy, hp, ha, heA, heY]

theorem computed_estimate_eq_actual (hR : d.R ≠ 0) (n : ℕ) (hn : n≤T) (ω : Ω) :
    StatisticalMaps.estimate (ExponentialStochastic.run o d prior h.extend.feedback n ω).1 =
      CNDSGNet.actualEstimator (ExponentialSGStochastic.model o d prior h hm) n ω := by
  rw [CNDSGNet.actualEstimator, actualScoreSum_eq_runS o d prior h hm hR n hn ω]
  have hi := information_prefix
    (fun t i => (ExponentialSGStochastic.model o d prior h hm).p t i ω)
    (fun t i => ExponentialStochastic.runProbability o d prior h.extend.feedback t i ω) n
    (fun t ht => congrArg (fun p => fun i => p i ω)
      (ExponentialSGStochastic.model_p o d prior h hm (lt_of_lt_of_le ht hn)))
  funext i
  rw [ExponentialStochastic.estimate_is_actual_inverse_statistic o d prior h.extend.feedback hR]
  unfold CNDPhysical.inverseInformation
  rw [hi]
  rfl

theorem computed_rawPairRadius_eq_model (hR : d.R ≠ 0) (n : ℕ) (hn : n≤T)
    (ω : Ω) (H L : ℝ) :
    StatisticalMaps.rawPairRadius H L R (ExponentialStochastic.run o d prior h.extend.feedback n ω).1 =
      CNDPhysical.pairRadius (fun t i => (ExponentialSGStochastic.model o d prior h hm).p t i ω) n H L R := by
  rw [ExponentialStochastic.computed_rawPairRadius_eq_actual o d prior h.extend.feedback hR]
  exact pairRadius_prefix
    (fun t i => ExponentialStochastic.runProbability o d prior h.extend.feedback t i ω)
    (fun t i => (ExponentialSGStochastic.model o d prior h hm).p t i ω) n H L R
    (fun t ht => (congrArg (fun p => fun i => p i ω)
      (ExponentialSGStochastic.model_p o d prior h hm (lt_of_lt_of_le ht hn))).symm)
end Generic

section Canonical
variable {K : ℕ} {E Ω : Type*} [Nonempty (Fin K)]
  [Fintype E] [DecidableEq E] [Nonempty E]
  [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)] [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D σ σe : ℝ} {T : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def maps (h : SGInputs ℱ θ R M D T) (ν : ℝ≥0) (L W : ℝ) (hW : 0 ≤ W) :
    DecisionMaps (Fin K) := concreteMaps (R+M+(ν : ℝ)) (4*L) R W h.R_nonneg hW

def center (h : SGInputs ℱ θ R M D T) (d : ExpertData (Fin K) E) (prior : E → ℝ)
    (ν : ℝ≥0) (L W : ℝ) (hW : 0 ≤ W) (t : ℕ) (ω : Ω) : Fin K → ℝ :=
  confidence (maps h ν L W hW) d
    (ExponentialStochastic.run (maps h ν L W hW) d prior h.extend.feedback t ω)

def radius (h : SGInputs ℱ θ R M D T) (d : ExpertData (Fin K) E) (prior : E → ℝ)
    (ν : ℝ≥0) (L W : ℝ) (hW : 0 ≤ W) (t : ℕ) (ω : Ω) : Fin K → Fin K → ℝ :=
  CNDProcess.radius (maps h ν L W hW) d
    (ExponentialStochastic.run (maps h ν L W hW) d prior h.extend.feedback t ω)

/-- Legal c=s=1 confidence, with exactly Hs=R+M+ν and L=4Lc.
All randomness and probabilities are those of the actual exponential run. -/
theorem center_confidence_event
    (h : SGInputs ℱ θ R M D T) (d : ExpertData (Fin K) E) (hdR : d.R = R) (prior : E → ℝ)
    (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2+σe^2) (W : ℝ) (hW : 0 ≤ W)
    (hT : 1 ≤ T) (hK : 2 ≤ K) {δc : ℝ} (hc : 0 < δc) (hc1 : δc ≤ 1)
    (hm : ExponentialSGStochastic.FiniteLaws
      (maps h ν (CNDNet.paperLc (Fin K) T δc) W hW) d prior h (μ := μ) (σ := σ) (σe := σe)) :
    ∃ G : Set Ω, μ.real Gᶜ ≤ δc ∧ ∀ ω ∈ G, ∀ n≤T, ∀ i j : Fin K,
      |(θ i - center h d prior ν (CNDNet.paperLc (Fin K) T δc) W hW n ω i) -
        (θ j - center h d prior ν (CNDNet.paperLc (Fin K) T δc) W hW n ω j)| ≤
          radius h d prior ν (CNDNet.paperLc (Fin K) T δc) W hW n ω i j := by
  by_cases hz : R = 0
  · refine ⟨Set.univ, by simpa using hc.le, ?_⟩
    intro ω _ n _ i j
    have hi : θ i = 0 := le_antisymm (by simpa [hz] using (h.theta_range i).2) (h.theta_range i).1
    have hj : θ j = 0 := le_antisymm (by simpa [hz] using (h.theta_range j).2) (h.theta_range j).1
    simp [center, radius, confidence, CNDProcess.radius, hdR, hz, hi, hj]
  · have hd : d.R ≠ 0 := by rwa [hdR]
    have hRpos : 0 < R := lt_of_le_of_ne h.R_nonneg (Ne.symm hz)
    let L := CNDNet.paperLc (Fin K) T δc
    let o := maps h ν L W hW
    obtain ⟨G,hG,hcube⟩ := CNDSGNet.confidence_cube_event
      (ExponentialSGStochastic.model o d prior h hm) ν hν T hT
      (by simpa using hK) hc hc1
    refine ⟨G,hG,?_⟩
    intro ω hω n hn i j
    have hcubestate : θ ∈ CNDNet.contrastCube
        (StatisticalMaps.estimate (ExponentialStochastic.run o d prior h.extend.feedback n ω).1)
        (StatisticalMaps.rawPairRadius (R+M+(ν : ℝ)) (4*L) R
          (ExponentialStochastic.run o d prior h.extend.feedback n ω).1) R := by
      rw [computed_estimate_eq_actual o d prior h hm hd n hn ω,
        computed_rawPairRadius_eq_model o d prior h hm hd n hn ω]
      exact hcube ω hω n hn
    have hb := CNDMainConfidence.canonical_center_saturated_bound
      (StatisticalMaps.estimate (ExponentialStochastic.run o d prior h.extend.feedback n ω).1) θ
      (StatisticalMaps.rawPairRadius (R+M+(ν : ℝ)) (4*L) R
        (ExponentialStochastic.run o d prior h.extend.feedback n ω).1)
      R hRpos hcubestate i j
    change |(θ i - confidence o d (ExponentialStochastic.run o d prior h.extend.feedback n ω) i) -
      (θ j - confidence o d (ExponentialStochastic.run o d prior h.extend.feedback n ω) j)| ≤
        CNDProcess.radius o d (ExponentialStochastic.run o d prior h.extend.feedback n ω) i j
    simp only [confidence, CNDProcess.radius, if_neg hd]
    exact hb
end Canonical

#print axioms actualScoreSum_eq_runS
#print axioms computed_estimate_eq_actual
#print axioms computed_rawPairRadius_eq_model
#print axioms center_confidence_event
end Part2.ExponentialSGConfidence
