import staging.cnd20261024.process.ActualModel
import staging.cnd20261024.net.ConfidenceCube

/-!
The actual CND recursion's confidence center is covered on the original M1
confidence event. The score, estimator and pair radius are identified with
the computed state; no center-coverage field is added to the model.
-/

noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory Finset
open scoped BigOperators Matrix

namespace Part2.CNDMainConfidence

open CNDProcess

section CanonicalGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two independently written cube specifications agree exactly. -/
theorem contrastCube_eq_confidenceSet (hat : ι → ℝ) (rho : ι → ι → ℝ) (R : ℝ) :
    CNDNet.contrastCube hat rho R = CNDConfidenceSlabs.confidenceSet ι R (hat, rho) := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨fun i => (hx.1 i).1, fun i => (hx.1 i).2⟩, ?_⟩
    intro i j
    simpa only [abs_sub_comm] using hx.2 i j
  · intro hx
    refine ⟨fun i => ⟨hx.1.1 i, hx.1.2 i⟩, ?_⟩
    intro i j
    simpa only [abs_sub_comm] using hx.2 i j

/-- Feasibility of the true parameter forces feasibility of the actual
canonical center; both points give the precise min(2R,2rho) error bound. -/
theorem canonical_center_pair_bound (hat theta : ι → ℝ) (rho : ι → ι → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (htheta : theta ∈ CNDNet.contrastCube hat rho R)
    (i j : ι) :
    |(theta i - CNDConfidenceSlabs.canonicalConfidence ι R hR (hat, rho) i) -
      (theta j - CNDConfidenceSlabs.canonicalConfidence ι R hR (hat, rho) j)| ≤
        min (2 * R) (2 * rho i j) := by
  have ht : theta ∈ CNDConfidenceSlabs.confidenceSet ι R (hat, rho) := by
    rw [← contrastCube_eq_confidenceSet]
    exact htheta
  have hc := (CNDConfidenceSlabs.canonicalConfidence_spec ι R hR (hat, rho) ⟨theta, ht⟩).1
  let c := CNDConfidenceSlabs.canonicalConfidence ι R hR (hat, rho)
  have hti := htheta.1 i
  have htj := htheta.1 j
  have hci : 0 ≤ c i ∧ c i ≤ R := ⟨hc.1.1 i, hc.1.2 i⟩
  have hcj : 0 ≤ c j ∧ c j ≤ R := ⟨hc.1.1 j, hc.1.2 j⟩
  have hbox : |(theta i - c i) - (theta j - c j)| ≤ 2 * R := by
    rw [abs_le]
    constructor <;> linarith
  have htij : |(theta i - theta j) - (hat i - hat j)| ≤ rho i j := ht.2 i j
  have hcij : |(c i - c j) - (hat i - hat j)| ≤ rho i j := hc.2 i j
  have hrho : |(theta i - c i) - (theta j - c j)| ≤ 2 * rho i j := by
    calc
      _ = |((theta i - theta j) - (hat i - hat j)) -
          ((c i - c j) - (hat i - hat j))| := by congr 1; ring
      _ ≤ |(theta i - theta j) - (hat i - hat j)| +
          |(c i - c j) - (hat i - hat j)| := abs_sub _ _
      _ ≤ 2 * rho i j := by linarith
  exact le_min hbox hrho

theorem canonical_center_saturated_bound (hat theta : ι → ℝ) (rho : ι → ι → ℝ)
    (R : ℝ) (hR : 0 < R) (htheta : theta ∈ CNDNet.contrastCube hat rho R)
    (i j : ι) :
    |(theta i - CNDConfidenceSlabs.canonicalConfidence ι R hR.le (hat, rho) i) -
      (theta j - CNDConfidenceSlabs.canonicalConfidence ι R hR.le (hat, rho) j)| ≤
        CNDPhysical.saturatedRadius R (rho i j) := by
  have hrho : 0 ≤ rho i j := (abs_nonneg _).trans (htheta.2 i j)
  exact (canonical_center_pair_bound hat theta rho R hR.le htheta i j).trans
    (CNDPhysical.saturatedRadius_bounds R (rho i j) hR hrho).1

end CanonicalGeometry

section Statistics
variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}
  {theta : ι → ℝ} {R M D : ℝ} {mu : Measure Ω} [IsProbabilityMeasure mu]

/-- The score sum in the probability library is the actual observed S state. -/
theorem actualScoreSum_eq_runS (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ theta R M D) (hm : OriginalM1 o d h mu)
    (hR : d.R ≠ 0) (n : ℕ) (omega : Ω) :
    CNDNet.actualScoreSum (OriginalM1.toM1Model o d h hm) n omega =
      fun i => runS o d h.feedback n i omega := by
  funext i
  rw [actual_statistic_identity o d h.feedback hR]
  change (∑ t ∈ Finset.range n,
      ((if h.action t omega = i then 1 else 0) - runProbability o d h.feedback t i omega) *
        (theta (h.action t omega) + h.drift t omega - h.error t (h.action t omega) omega)) = _
  apply Finset.sum_congr rfl
  intro t _
  change ((if h.action t omega = i then 1 else 0) - runProbability o d h.feedback t i omega) *
      (theta (h.action t omega) + h.drift t omega - h.error t (h.action t omega) omega) =
    ((if h.action t omega = i then 1 else 0) - runProbability o d h.feedback t i omega) * h.residual t omega
  rw [h.residual_eq]

/-- The implemented tangent inverse estimate is the actual-score estimator,
not an independently supplied confidence center. -/
theorem computed_estimate_eq_actualEstimator (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : PotentialInputs ℱ theta R M D) (hm : OriginalM1 o d h mu)
    (hR : d.R ≠ 0) (n : ℕ) (omega : Ω) :
    StatisticalMaps.estimate (run o d h.feedback n omega).1 =
      CNDNet.actualEstimator (OriginalM1.toM1Model o d h hm) n omega := by
  rw [CNDNet.actualEstimator, actualScoreSum_eq_runS o d h hm hR]
  funext i
  exact estimate_is_actual_inverse_statistic o d h.feedback hR n omega i

theorem computed_rawPairRadius_eq_actual (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (hR : d.R ≠ 0) (n : ℕ) (omega : Ω) (H L R : ℝ) :
    StatisticalMaps.rawPairRadius H L R (run o d f n omega).1 =
      CNDPhysical.pairRadius (fun t a => runProbability o d f t a omega) n H L R := by
  funext i j
  unfold StatisticalMaps.rawPairRadius CNDPhysical.pairRadius
  change 2 * H * Real.sqrt (L * StatisticalMaps.resistance
      (fun i j => runV o d f n i j omega) i j) +
      (4 * H * L + R * Fintype.card ι) * StatisticalMaps.resistance
        (fun i j => runV o d f n i j omega) i j = _
  rw [computed_resistance_eq_actual o d f hR]

end Statistics

section ActualAlgorithm
variable {K : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {theta : Fin K → ℝ} {R M D W : ℝ}

def actualCenter (d : ℕ) (h : PotentialInputs ℱ theta R M D) (hW : 0 ≤ W)
    (L : ℝ) (n : ℕ) (omega : Ω) : Fin K → ℝ :=
  confidence (concreteMaps (R + M + D) L R W h.R_nonneg hW) (treeData d K W R)
    (run (concreteMaps (R + M + D) L R W h.R_nonneg hW) (treeData d K W R) h.feedback n omega)

def actualRadius (d : ℕ) (h : PotentialInputs ℱ theta R M D) (hW : 0 ≤ W)
    (L : ℝ) (n : ℕ) (omega : Ω) : Fin K → Fin K → ℝ :=
  radius (concreteMaps (R + M + D) L R W h.R_nonneg hW) (treeData d K W R)
    (run (concreteMaps (R + M + D) L R W h.R_nonneg hW) (treeData d K W R) h.feedback n omega)

/-- Measurability is unconditional, including infeasible confidence histories. -/
theorem actualCenter_measurable (d : ℕ) (h : PotentialInputs ℱ theta R M D) (hW : 0 ≤ W)
    (L : ℝ) (n : ℕ) : Measurable[ℱ n] (actualCenter d h hW L n) :=
  confidence_measurable (m := ℱ n) (run_measurable _ _ h.feedback n) _ _

theorem actualRadius_measurable (d : ℕ) (h : PotentialInputs ℱ theta R M D) (hW : 0 ≤ W)
    (L : ℝ) (n : ℕ) : Measurable[ℱ n] (actualRadius d h hW L n) :=
  radius_measurable (m := ℱ n) (run_measurable _ _ h.feedback n) _ _

theorem actualCenter_zero_R (d : ℕ) (h : PotentialInputs ℱ theta R M D) (hW : 0 ≤ W)
    (L : ℝ) (n : ℕ) (omega : Ω) (hR : R = 0) : actualCenter d h hW L n omega = 0 := by
  funext i
  simp [actualCenter, confidence, treeData, hR]

/-- The branched implementation is the actual saturated resistance radius,
also at R=0 where both are exactly zero. -/
theorem actualRadius_eq_actualSaturatedRadius (d : ℕ) (h : PotentialInputs ℱ theta R M D)
    (hW : 0 ≤ W) (L : ℝ) (n : ℕ) (omega : Ω) :
    actualRadius d h hW L n omega = CNDPhysical.actualSaturatedRadius
      (fun t a => runProbability (concreteMaps (R + M + D) L R W h.R_nonneg hW)
        (treeData d K W R) h.feedback t a omega) n (R + M + D) L R := by
  by_cases hz : R = 0
  · funext i j
    simp [actualRadius, radius, treeData, hz, CNDPhysical.actualSaturatedRadius,
      CNDPhysical.saturatedRadius]
  · change (if (treeData d K W R).R = 0 then _ else _) = _
    rw [if_neg (show (treeData d K W R).R ≠ 0 from hz)]
    exact computed_radius_eq_actual _ _ h.feedback hz n omega _ _ _

theorem actualRadius_eq_actualModelRadius (d : ℕ) (h : PotentialInputs ℱ theta R M D)
    (hW : 0 ≤ W) (L : ℝ) (mu : Measure Ω) [IsProbabilityMeasure mu]
    (hm : OriginalM1 (concreteMaps (R + M + D) L R W h.R_nonneg hW)
      (treeData d K W R) h mu) (n : ℕ) (omega : Ω) :
    actualRadius d h hW L n omega = CNDPhysical.actualSaturatedRadius
      (fun t a => (actualM1Model h hW mu hm).p t a omega) n (R + M + D) L R :=
  actualRadius_eq_actualSaturatedRadius d h hW L n omega

/-- Original-space CI closure for the actual canonical algorithm. The only
stochastic inputs are PotentialInputs and the two OriginalM1 laws. -/
theorem actual_center_confidence_event (d : ℕ) (h : PotentialInputs ℱ theta R M D)
    (hW : 0 ≤ W) (mu : Measure Ω) [IsProbabilityMeasure mu]
    (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ K) {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hm : OriginalM1
      (concreteMaps (R + M + D) (CNDNet.paperLc (Fin K) T delta) R W h.R_nonneg hW)
      (treeData d K W R) h mu) :
    ∃ G : Set Ω, mu.real Gᶜ ≤ delta ∧ ∀ omega ∈ G, ∀ n ≤ T, ∀ i j : Fin K,
      |(theta i - actualCenter d h hW (CNDNet.paperLc (Fin K) T delta) n omega i) -
        (theta j - actualCenter d h hW (CNDNet.paperLc (Fin K) T delta) n omega j)| ≤
          actualRadius d h hW (CNDNet.paperLc (Fin K) T delta) n omega i j := by
  by_cases hz : R = 0
  · refine ⟨Set.univ, by simpa using hdelta.le, ?_⟩
    intro omega _ n _ i j
    have hti : theta i = 0 := le_antisymm (by simpa [hz] using (h.theta_range i).2) (h.theta_range i).1
    have htj : theta j = 0 := le_antisymm (by simpa [hz] using (h.theta_range j).2) (h.theta_range j).1
    simp [actualCenter, actualRadius, confidence, radius, treeData, hz, hti, htj]
  · have hRpos : 0 < R := lt_of_le_of_ne h.R_nonneg (Ne.symm hz)
    have hH : 0 < R + M + D := by linarith [h.M_nonneg, h.D_nonneg]
    obtain ⟨G, hG, hcube⟩ := CNDNet.actual_confidence_cube_event
      (actualM1Model h hW mu hm) T hT (by simpa using hK) hH hdelta hdelta1
    refine ⟨G, hG, ?_⟩
    intro omega homega n hn i j
    let L := CNDNet.paperLc (Fin K) T delta
    let o : DecisionMaps (Fin K) := concreteMaps (R + M + D) L R W h.R_nonneg hW
    let e := treeData d K W R
    have hcubestate : theta ∈ CNDNet.contrastCube
        (StatisticalMaps.estimate (run o e h.feedback n omega).1)
        (StatisticalMaps.rawPairRadius (R + M + D) L R (run o e h.feedback n omega).1) R := by
      rw [computed_estimate_eq_actualEstimator o e h hm hz n omega,
        computed_rawPairRadius_eq_actual o e h.feedback hz n omega]
      exact hcube omega homega n hn
    have hbound := canonical_center_saturated_bound
      (StatisticalMaps.estimate (run o e h.feedback n omega).1) theta
      (StatisticalMaps.rawPairRadius (R + M + D) L R (run o e h.feedback n omega).1)
      R hRpos hcubestate i j
    change |(theta i - confidence o e (run o e h.feedback n omega) i) -
      (theta j - confidence o e (run o e h.feedback n omega) j)| ≤
        radius o e (run o e h.feedback n omega) i j
    have heR : e.R ≠ 0 := hz
    simp only [confidence, radius, if_neg heR]
    exact hbound

end ActualAlgorithm
end Part2.CNDMainConfidence

end
