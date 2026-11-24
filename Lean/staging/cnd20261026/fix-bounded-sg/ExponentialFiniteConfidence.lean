import staging.cnd20261026.«fix-bounded-sg».ExponentialFinite
import staging.cnd20261024.net.ConfidenceCube

/-! The legal unit-scale confidence branch is supplied by the actual M1
confidence-cube theorem, not by a hypothesized E11 event. Arbitrary smaller
scales use the separate actual-radius gap theorem. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 2400000
namespace Part2.ExponentialFinite
open CNDProcess CNDHorizon CNDMainConfidence
variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
  {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}
  {θ : Fin K → ℝ} {R M D W : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (h : BoundedInputs ℱ θ R M D T) (L : ℝ) (hW : 0<W)
  (c : Config (K := K) (E := E) T R W)
  (hm : Protocol h L hW c (μ := μ))

theorem computed_pairRadius_eq_model (hdR : c.data.R ≠ 0) (t : ℕ) (ht : t≤T) (ω : Ω) :
    StatisticalMaps.rawPairRadius (R+M+D) L R (state h L hW c t ω).1 =
      CNDPhysical.pairRadius (fun n i => (model h L hW c hm).p n i ω) t (R+M+D) L R := by
  rw [state,ExponentialStochastic.computed_rawPairRadius_eq_actual _ _ _ _ hdR]
  symm
  apply CNDHorizon.pairRadius_prefix
  intro n hn
  exact congrArg (fun p => fun i => p i ω)
    (ExponentialStochastic.model_p (maps h L hW c) c.data c.prior h hm (lt_of_lt_of_le hn ht))

theorem center_eq_actual_canonical (hdR : c.data.R ≠ 0) (hc : c.confidence_scale=1)
    (t : ℕ) (ht : t<T) (ω : Ω) :
    (fun i => center h L hW c t i ω) = CNDConfidenceSlabs.canonicalConfidence (Fin K) R h.R_nonneg
      (CNDNet.actualEstimator (model h L hW c hm) t ω,
        CNDPhysical.pairRadius (fun n i => (model h L hW c hm).p n i ω) t (R+M+D) L R) := by
  have he := ExponentialStochastic.computed_estimate_eq_actualEstimator
    (maps h L hW c) c.data c.prior h hm hdR t ht.le ω
  change StatisticalMaps.estimate (state h L hW c t ω).1 =
    CNDNet.actualEstimator (model h L hW c hm) t ω at he
  have hr := computed_pairRadius_eq_model h L hW c hm hdR t ht.le ω
  funext i
  simp only [center,if_pos ht,CNDProcess.confidence,if_neg hdR,maps,ExponentialGeometry.maps,
    ExponentialScaledMaps.decisionMaps,ExponentialScaledMaps.confidence,hc,one_mul]
  rw [← he,← hr]

theorem radius_eq_actual_saturated (hdR : c.data.R ≠ 0) (hs : c.radius_scale=1)
    (t : ℕ) (ht : t<T) (ω : Ω) (i j : Fin K) :
    radius h L hW c t i j ω = CNDPhysical.saturatedRadius R
      (CNDPhysical.pairRadius (fun n i => (model h L hW c hm).p n i ω) t (R+M+D) L R i j) := by
  have hr := computed_pairRadius_eq_model h L hW c hm hdR t ht.le ω
  simp only [radius,if_pos ht,CNDProcess.radius,if_neg hdR,maps,ExponentialGeometry.maps,
    ExponentialScaledMaps.decisionMaps,ExponentialScaledMaps.radius,hs,one_mul]
  rw [← hr]

include hm in
theorem unit_scale_confidence_event (hK : 2≤K) (hT : 1≤T)
    (hc : c.confidence_scale=1) (hs : c.radius_scale=1)
    {δc : ℝ} (hδc : 0<δc) (hδc1 : δc≤1)
    (hL : L=CNDNet.paperLc (Fin K) T δc) :
    ∃ C : Set Ω, μ.real Cᶜ≤δc ∧ ∀ ω∈C,
      ExponentialPhysical.Covers (θ := θ) (center h L hW c) (radius h L hW c) T ω := by
  by_cases hz : R=0
  · refine ⟨Set.univ,by simpa using hδc.le,?_⟩
    intro ω _ t ht i j
    have hti : θ i=0 := le_antisymm (by simpa [hz] using (h.theta_range i).2) (h.theta_range i).1
    have htj : θ j=0 := le_antisymm (by simpa [hz] using (h.theta_range j).2) (h.theta_range j).1
    have hdR : c.data.R=0 := c.range_eq.trans hz
    simp [center,radius,ht,CNDProcess.confidence,CNDProcess.radius,hdR,hti,htj]
  · have hRpos : 0<R := lt_of_le_of_ne h.R_nonneg (Ne.symm hz)
    have hH : 0<R+M+D := by linarith [h.M_nonneg,h.D_nonneg]
    have hdR : c.data.R ≠ 0 := by rw [c.range_eq]; exact hz
    obtain ⟨C,hC,hcube⟩ := CNDNet.actual_confidence_cube_event (model h L hW c hm) T hT
      (by simpa only [Fintype.card_fin] using hK) hH hδc hδc1
    refine ⟨C,hC,?_⟩
    intro ω hω t ht i j
    have hcubet := hcube ω hω t ht.le
    rw [← hL] at hcubet
    have hbound := canonical_center_saturated_bound _ θ _ R hRpos hcubet i j
    have hcen := center_eq_actual_canonical h L hW c hm hdR hc t ht ω
    have hrad := radius_eq_actual_saturated h L hW c hm hdR hs t ht ω i j
    rw [hrad]
    simp_rw [congrFun hcen] 
    convert hbound using 1 <;> congr 1 <;> ring

/-- Actual unit-scale bounded-feedback E12/E13, with the original E11 event
derived from the new exponential M1 instance rather than supplied. -/
theorem unit_scale_main (hK : 2≤K) (hT : 1≤T)
    (hc : c.confidence_scale=1) (hs : c.radius_scale=1)
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W)
    {δc δa δe : ℝ} (hδc : 0<δc) (hδc1 : δc≤1)
    (hδa : 0<δa) (hδa1 : δa<1) (hδe : 0<δe) (hδe1 : δe<1)
    (hL : L=CNDNet.paperLc (Fin K) T δc) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ≤δc+δa+δe ∧ ∀ ω∈G,
      ExponentialComposition.intervalConclusion (model h L hW c hm) (center h L hW c)
        (radius h L hW c) (trajectory h L hW c) T W δa δe ω ∧
      ExponentialComposition.pathConclusion (model h L hW c hm) (center h L hW c)
        (radius h L hW c) (trajectory h L hW c) T W δa δe ω := by
  obtain ⟨C,hC,hcover⟩ := unit_scale_confidence_event h L hW c hm hK hT hc hs hδc hδc1 hL
  have hLnonneg : 0≤L := by
    rw [hL]
    exact le_trans zero_le_one (CNDNet.paper_Lc_budget (ι := Fin K) T hδc hδc1).1
  exact conditional_main h L hW c hm hLnonneg (by omega) hb hδa hδa1 hδe hδe1 C hC hcover

theorem unit_scale_actual_main (hK : 2≤K) (hT : 1≤T)
    (hc : c.confidence_scale=1) (hs : c.radius_scale=1)
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W)
    {δc δa δe : ℝ} (hδc : 0<δc) (hδc1 : δc≤1)
    (hδa : 0<δa) (hδa1 : δa<1) (hδe : 0<δe) (hδe1 : δe<1)
    (hL : L=CNDNet.paperLc (Fin K) T δc) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ≤δc+δa+δe ∧
      ∀ ω∈G, ActualConclusions h L hW c hm δa δe ω := by
  obtain ⟨G,hG,hprob,hgood⟩ := unit_scale_main h L hW c hm hK hT hc hs hb
    hδc hδc1 hδa hδa1 hδe hδe1 hL
  exact ⟨G,hG,hprob,fun ω hω => conclusions_transfer h L hW c hm δa δe ω (hgood ω hω)⟩

/-- Original finite-input form: only primitive public-cost span is supplied;
the broadcast span, M1 instance, confidence event, geometry and E9/E10 are
all derived before the E12/E13 physical conclusion. -/
theorem unit_scale_original_main (hK : 2≤K) (hT : 1≤T)
    (hc : c.confidence_scale=1) (hs : c.radius_scale=1)
    {B : ℝ} (hwidth : W=B+2*D)
    (hcost : ∀ t<T, ∀ ω i j, h.publicCost t j ω-h.publicCost t i ω≤B)
    {δc δa δe : ℝ} (hδc : 0<δc) (hδc1 : δc≤1)
    (hδa : 0<δa) (hδa1 : δa<1) (hδe : 0<δe) (hδe1 : δe<1)
    (hL : L=CNDNet.paperLc (Fin K) T δc) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ≤δc+δa+δe ∧
      ∀ ω∈G, ActualConclusions h L hW c hm δa δe ω := by
  exact unit_scale_actual_main h L hW c hm hK hT hc hs (broadcast_span h hwidth hcost)
    hδc hδc1 hδa hδa1 hδe hδe1 hL

end Part2.ExponentialFinite
