import staging.cnd20261026.«fix-bounded-sg».SGModel
import staging.cnd20261024.net.SGUniformDirections
import staging.cnd20261024.main.ConfidenceBridge

noncomputable section
open MeasureTheory Finset
open scoped BigOperators Matrix NNReal
set_option maxHeartbeats 1600000
namespace Part2.CNDHorizon.SGMain
open CNDProcess CNDProcess.SG
variable {K d T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D W : ℝ}

def center (h : Inputs ℱ θ R M D) (ν : ℝ≥0) (Lc : ℝ) (hW : 0 ≤ W)
    (t : ℕ) (ω : Ω) : Fin K → ℝ :=
  confidence (maps (K := K) ν Lc R M W h.R_nonneg hW) (treeData d K W R)
    (run (maps (K := K) ν Lc R M W h.R_nonneg hW) (treeData d K W R) h.feedback t ω)

def radius (h : Inputs ℱ θ R M D) (ν : ℝ≥0) (Lc : ℝ) (hW : 0 ≤ W)
    (t : ℕ) (ω : Ω) : Fin K → Fin K → ℝ :=
  CNDProcess.radius (maps (K := K) ν Lc R M W h.R_nonneg hW) (treeData d K W R)
    (run (maps (K := K) ν Lc R M W h.R_nonneg hW) (treeData d K W R) h.feedback t ω)

theorem center_measurable (h : Inputs ℱ θ R M D) (ν : ℝ≥0) (Lc : ℝ) (hW : 0 ≤ W) (t : ℕ) :
    Measurable[ℱ t] (center (d := d) h ν Lc hW t) :=
  confidence_measurable (m := ℱ t) (run_measurable _ _ h.feedback t) _ _

theorem radius_measurable (h : Inputs ℱ θ R M D) (ν : ℝ≥0) (Lc : ℝ) (hW : 0 ≤ W) (t : ℕ) :
    Measurable[ℱ t] (radius (d := d) h ν Lc hW t) :=
  CNDProcess.radius_measurable (m := ℱ t) (run_measurable _ _ h.feedback t) _ _

theorem radius_eq_actual (h : Inputs ℱ θ R M D) (ν : ℝ≥0) (Lc : ℝ) (hW : 0 ≤ W)
    (n : ℕ) (ω : Ω) :
    radius (d := d) h ν Lc hW n ω = CNDPhysical.actualSaturatedRadius
      (fun t i => runProbability (maps (K := K) ν Lc R M W h.R_nonneg hW)
        (treeData d K W R) h.feedback t i ω) n (R+M+(ν:ℝ)) (4*Lc) R := by
  by_cases hz : R = 0
  · funext i j
    simp [radius, CNDProcess.radius, treeData, hz, CNDPhysical.actualSaturatedRadius, CNDPhysical.saturatedRadius]
  · change (if (treeData d K W R).R = 0 then _ else _) = _
    rw [if_neg (show (treeData d K W R).R ≠ 0 from hz)]
    exact computed_radius_eq_actual _ _ h.feedback hz n ω _ _ _

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {σ σe : ℝ}

theorem radius_eq_model (h : Inputs ℱ θ R M D) (ν : ℝ≥0) (Lc : ℝ) (hW : 0≤W)
    (hm : CNDHorizon.SG.Laws (maps ν Lc R M W h.R_nonneg hW) (treeData d K W R) h μ σ σe T)
    (n : ℕ) (hn : n≤T) (ω : Ω) :
    radius (d:=d) h ν Lc hW n ω=CNDPhysical.actualSaturatedRadius
      (fun t i => (CNDHorizon.SG.actualModel h ν Lc W hW hm).p t i ω) n (R+M+(ν:ℝ)) (4*Lc) R := by
  rw [radius_eq_actual]
  apply radius_prefix
  intro t ht
  funext i
  exact (congrFun (congrFun (SG.model_p _ _ h hm (lt_of_lt_of_le ht hn)) i) ω).symm

theorem computed_estimate_eq_actual (h : Inputs ℱ θ R M D) (ν : ℝ≥0) (Lc : ℝ) (hW : 0 ≤ W)
    (hm : CNDHorizon.SG.Laws (maps (K := K) ν Lc R M W h.R_nonneg hW) (treeData d K W R) h μ σ σe T)
    (hz : R ≠ 0) (n : ℕ) (hn : n≤T) (ω : Ω) :
    StatisticalMaps.estimate
      (run (maps (K := K) ν Lc R M W h.R_nonneg hW) (treeData d K W R) h.feedback n ω).1 =
        CNDSGNet.actualEstimator (CNDHorizon.SG.actualModel h ν Lc W hW hm) n ω := by
  rw [estimator_uses_actual_score _ _ h hz]
  unfold CNDSGNet.actualEstimator
  have hi := information_prefix
    (fun t i => (CNDHorizon.SG.actualModel h ν Lc W hW hm).p t i ω)
    (fun t i => runProbability (maps ν Lc R M W h.R_nonneg hW) (treeData d K W R) h.feedback t i ω) n
    (fun t ht => congrArg (fun p => fun i => p i ω)
      (SG.model_p _ _ h hm (lt_of_lt_of_le ht hn)))
  simp only [CNDPhysical.inverseInformation,hi]
  congr 1
  funext i
  apply sum_congr rfl
  intro t ht
  have htT : t<T := lt_of_lt_of_le (mem_range.mp ht) hn
  simp only [CNDSGNet.actualScoreSum,actualScoreSum,CNDHorizon.SG.actualModel,
    CNDHorizon.SG.model,CNDHorizon.SG.publicShadow,Primitive.stopped,CNDHorizon.SG.primitive,
    stop,stopP,if_pos htT,PairConfidence.actionIndicator]

/-- The real noisy score, original SG constants and actual canonical center share one event. -/
theorem center_confidence_event (h : Inputs ℱ θ R M D) (ν : ℝ≥0) (hν : (ν:ℝ)^2=σ^2+σe^2)
    (hW : 0 ≤ W) (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ K)
    {δc : ℝ} (hc : 0 < δc) (hc1 : δc ≤ 1)
    (hm : CNDHorizon.SG.Laws (maps (K := K) ν (CNDNet.paperLc (Fin K) T δc) R M W h.R_nonneg hW)
      (treeData d K W R) h μ σ σe T) :
    ∃ G : Set Ω, μ.real Gᶜ ≤ δc ∧ ∀ ω ∈ G, ∀ n ≤ T, ∀ i j : Fin K,
      |(θ i-center (d := d) h ν (CNDNet.paperLc (Fin K) T δc) hW n ω i)-
        (θ j-center (d := d) h ν (CNDNet.paperLc (Fin K) T δc) hW n ω j)| ≤
          radius (d := d) h ν (CNDNet.paperLc (Fin K) T δc) hW n ω i j := by
  by_cases hz : R = 0
  · refine ⟨Set.univ, by simpa using hc.le, ?_⟩
    intro ω _ n _ i j
    have hi : θ i = 0 := le_antisymm (by simpa [hz] using (h.theta_range i).2) (h.theta_range i).1
    have hj : θ j = 0 := le_antisymm (by simpa [hz] using (h.theta_range j).2) (h.theta_range j).1
    simp [center, radius, confidence, CNDProcess.radius, treeData, hz, hi, hj]
  · have hRpos : 0 < R := lt_of_le_of_ne h.R_nonneg (Ne.symm hz)
    obtain ⟨G,hG,hcube⟩ := CNDSGNet.confidence_cube_event
      (CNDHorizon.SG.actualModel h ν (CNDNet.paperLc (Fin K) T δc) W hW hm) ν hν T hT
      (by simpa using hK) hc hc1
    refine ⟨G,hG,?_⟩
    intro ω hω n hn i j
    let L := CNDNet.paperLc (Fin K) T δc
    let o := maps (K := K) ν L R M W h.R_nonneg hW
    let a := treeData d K W R
    have hcubestate : θ ∈ CNDNet.contrastCube
        (StatisticalMaps.estimate (run o a h.feedback n ω).1)
        (StatisticalMaps.rawPairRadius (R+M+(ν:ℝ)) (4*L) R (run o a h.feedback n ω).1) R := by
      rw [computed_estimate_eq_actual h ν L hW hm hz n hn ω,
        CNDMainConfidence.computed_rawPairRadius_eq_actual o a h.feedback hz n ω]
      rw [pairRadius_prefix (fun t i => runProbability o a h.feedback t i ω)
        (fun t i => (CNDHorizon.SG.model o a h hm).p t i ω) n (R+M+(ν:ℝ)) (4*L) R
        (fun t ht => funext fun i => (congrFun (congrFun
          (SG.model_p o a h hm (lt_of_lt_of_le ht hn)) i) ω).symm)]
      exact hcube ω hω n hn
    have hb := CNDMainConfidence.canonical_center_saturated_bound
      (StatisticalMaps.estimate (run o a h.feedback n ω).1) θ
      (StatisticalMaps.rawPairRadius (R+M+(ν:ℝ)) (4*L) R (run o a h.feedback n ω).1)
      R hRpos hcubestate i j
    change |(θ i-confidence o a (run o a h.feedback n ω) i)-
      (θ j-confidence o a (run o a h.feedback n ω) j)| ≤ CNDProcess.radius o a (run o a h.feedback n ω) i j
    simp only [confidence, CNDProcess.radius, if_neg (show a.R ≠ 0 from hz)]
    exact hb
end Part2.CNDHorizon.SGMain
