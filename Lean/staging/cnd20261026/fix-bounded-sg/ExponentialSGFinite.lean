import staging.cnd20261026.«fix-bounded-sg».ExponentialActual
import staging.cnd20261026.«fix-bounded-sg».ExponentialSGConfidence
import staging.cnd20261026.«fix-bounded-sg».ExponentialSGPayment

/-! Actual finite SG exponential algorithm: original noisy feedback and
new categorical law, derived canonical geometry, actual expert cover cost,
one common interval/path event, and the actual private ledger. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators ProbabilityTheory NNReal
set_option maxHeartbeats 2400000

namespace Part2.ExponentialSGFinite
open CNDProcess CNDHorizon
variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}
  {θ : Fin K → ℝ} {R M D W σ σe : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (h : SGInputs ℱ θ R M D T) (ν : ℝ≥0) (L : ℝ) (hW : 0 ≤ W)
  (c : ExponentialGeometry.Config (K := K) (E := E) T R W)

def maps : DecisionMaps (Fin K) := ExponentialActual.maps (R+M+(ν : ℝ)) L h.R_nonneg hW c

abbrev Protocol := ExponentialSGStochastic.FiniteLaws (maps h ν L hW c) c.data c.prior h
  (μ := μ) (σ := σ) (σe := σe)

def model (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe)) :
    CNDProbability.SGModel ℱ μ θ R M D σ σe :=
  ExponentialSGStochastic.model (maps h ν L hW c) c.data c.prior h hm

def center := ExponentialActual.center (R+M+(ν : ℝ)) L h.R_nonneg hW c h.extend.feedback
def radius := ExponentialActual.radius (R+M+(ν : ℝ)) L h.R_nonneg hW c h.extend.feedback
def trajectory := ExponentialActual.trajectory (R+M+(ν : ℝ)) L h.R_nonneg hW c h.extend.feedback

theorem action_before
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe)) {t : ℕ} (ht : t<T) :
    (model h ν L hW c hm).action t = h.action t :=
  ExponentialSGStochastic.model_action _ _ _ _ hm ht

theorem public_before
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe)) {t : ℕ} (ht : t<T) :
    (model h ν L hW c hm).publicCost t = h.publicCost t :=
  ExponentialSGStochastic.model_public _ _ _ _ hm ht

theorem error_before
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe)) {t : ℕ} (ht : t<T) :
    (model h ν L hW c hm).error t = h.error t :=
  ExponentialSGStochastic.model_error _ _ _ _ hm ht

theorem broadcast_span {B : ℝ}
    (hb : ∀ t<T, ∀ ω i j, h.publicCost t j ω-h.publicCost t i ω≤B)
    (t : ℕ) (ht : t<T) (ω : Ω) (i j : Fin K) :
    h.broadcast t ω j-h.broadcast t ω i≤B+2*D := by
  have hi := abs_le.mp (h.error_bound t ht i ω)
  have hj := abs_le.mp (h.error_bound t ht j ω)
  have hc := hb t ht ω i j
  unfold SGInputs.broadcast
  linarith

theorem physical_before
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    {t : ℕ} (ht : t<T) (i : Fin K) (ω : Ω) :
    ExponentialSGPhysical.physical (model h ν L hW c hm) t i ω = h.physical t i ω := by
  simp only [ExponentialSGPhysical.physical, ExponentialPhysical.physical, model,
    ExponentialSGStochastic.model_public _ _ _ _ hm ht,
    ExponentialSGStochastic.model_drift _ _ _ _ hm ht,
    ExponentialSGStochastic.model_noise _ _ _ _ hm ht, SGInputs.physical]

theorem interval_regret_eq_original
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (u n : ℕ) (hu : u+n≤T) (k : Fin K) (ω : Ω) :
    CNDPayment.intervalSum (fun t ω => ExponentialSGPhysical.physical (model h ν L hW c hm)
      t ((model h ν L hW c hm).action t ω) ω -
      ExponentialSGPhysical.physical (model h ν L hW c hm) t k ω) u n ω =
    CNDPayment.intervalSum (fun t ω => h.physical t (h.action t ω) ω-h.physical t k ω) u n ω := by
  unfold CNDPayment.intervalSum
  apply sum_congr rfl
  intro s hs
  have ht : u+s<T := by have := mem_range.mp hs; omega
  dsimp only
  rw [action_before h ν L hW c hm ht,
    physical_before h ν L hW c hm ht, physical_before h ν L hW c hm ht]

theorem path_regret_eq_original
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (path : ℕ → Fin K) (ω : Ω) :
    (∑ t∈range T, (ExponentialSGPhysical.physical (model h ν L hW c hm)
      t ((model h ν L hW c hm).action t ω) ω -
      ExponentialSGPhysical.physical (model h ν L hW c hm) t (path t) ω)) =
    ∑ t∈range T, (h.physical t (h.action t ω) ω-h.physical t (path t) ω) := by
  apply sum_congr rfl
  intro t ht
  have htT := mem_range.mp ht
  rw [action_before h ν L hW c hm htT,
    physical_before h ν L hW c hm htT, physical_before h ν L hW c hm htT]

def bridge (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe)) :
    ExponentialActual.Bridge (R+M+(ν : ℝ)) L h.R_nonneg hW c h.extend.feedback
      (model h ν L hW c hm).toM1Model where
  p_before t ht := ExponentialSGStochastic.model_p _ _ _ _ hm ht
  broadcast_before t ht ω i := by
    change h.extend.broadcast t ω i = _
    rw [h.extend_broadcast ht]
    rw [public_before h ν L hW c hm ht, error_before h ν L hW c hm ht]
    rfl
  p_after t ht := by
    funext i ω
    simp only [model, ExponentialSGStochastic.model, ExponentialSGStochastic.publicShadow,
      Primitive.stopped, stopP, if_neg ht]
  public_after t ht := by
    funext i ω
    simp only [model, ExponentialSGStochastic.model, ExponentialSGStochastic.publicShadow,
      Primitive.stopped, ExponentialSGStochastic.primitive, SGInputs.extend, if_neg ht]
  error_after t ht := by
    funext i ω
    simp only [model, ExponentialSGStochastic.model, ExponentialSGStochastic.publicShadow,
      Primitive.stopped, ExponentialSGStochastic.primitive, SGInputs.extend, if_neg ht]

def compositionLaws (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (hL : 0 ≤ L) (hWpos : 0 < W)
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j - h.broadcast t ω i ≤ W) :
    ExponentialComposition.Laws (model h ν L hW c hm).toM1Model
      (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) T W := by
  apply ExponentialActual.compositionLaws (R+M+(ν : ℝ)) L h.R_nonneg hW c h.extend.feedback
    (model h ν L hW c hm).toM1Model (bridge h ν L hW c hm)
    (by linarith [h.R_nonneg,h.M_nonneg,ν.coe_nonneg]) hL hWpos
  intro t ht ω i j
  change h.extend.broadcast t ω j-h.extend.broadcast t ω i≤W
  simpa only [h.extend_broadcast ht] using hb t ht ω i j

/-- Arbitrary nonnegative confidence/radius scales: all actual geometry
and expert-envelope hypotheses are discharged by this actual SG recursion.
The exact confidence shortfall remains in the separate gap ledger. -/
theorem actual_gap_main
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (hν : (ν : ℝ)^2 = σ^2+σe^2) (hL : 0 ≤ L) (hWpos : 0 < W)
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j - h.broadcast t ω i ≤ W)
    {δa δn : ℝ} (ha : 0 < δa) (ha1 : δa < 1) (hn : 0 < δn) (hn1 : δn < 1) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δa+δn ∧ ∀ ω ∈ G,
      ExponentialSGPhysical.intervalConclusion (model h ν L hW c hm)
        (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) ν T W δa δn ω ∧
      ExponentialSGPhysical.pathConclusion (model h ν L hW c hm)
        (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) ν T W δa δn ω := by
  exact ExponentialSGPhysical.actual_e12_e13_with_gap (model h ν L hW c hm)
    (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) ν hν
    (compositionLaws h ν L hW c hm hL hWpos hb) hW
    (ExponentialActual.center_measurable _ _ _ _ _ _) (ExponentialActual.radius_measurable _ _ _ _ _ _)
    ha ha1 hn hn1

theorem radius_le_canonical
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (hL : 0 ≤ L) (hs1 : c.radius_scale ≤ 1) (t : ℕ) (i j : Fin K) (ω : Ω) :
    radius h ν L hW c t i j ω ≤
      CNDPayment.actualRadius (model h ν L hW c hm).toM1Model (R+M+(ν : ℝ)) L t i j ω := by
  have hH : 0 ≤ R+M+(ν : ℝ) := by linarith [h.R_nonneg,h.M_nonneg,ν.coe_nonneg]
  by_cases ht : t<T
  · by_cases hz : R=0
    · have hzradius : radius h ν L hW c t i j ω = 0 := by
        change (if t<T then CNDProcess.radius (maps h ν L hW c) c.data
          (ExponentialStochastic.run (maps h ν L hW c) c.data c.prior h.extend.feedback t ω) i j else 0) = 0
        rw [if_pos ht, CNDProcess.radius, if_pos (by rw [c.range_eq]; exact hz)]
      rw [hzradius]
      exact (CNDPayment.actualRadius_bounds (model h ν L hW c hm).toM1Model _ _ hH hL t i j ω).1
    · have hd : c.data.R ≠ 0 := by rwa [c.range_eq]
      change (if t<T then CNDProcess.radius (maps h ν L hW c) c.data
        (ExponentialStochastic.run (maps h ν L hW c) c.data c.prior h.extend.feedback t ω) i j else 0) ≤ _
      rw [if_pos ht, CNDProcess.radius, if_neg hd]
      change CNDPhysical.saturatedRadius R (c.radius_scale * StatisticalMaps.rawPairRadius
        (R+M+(ν : ℝ)) L R (ExponentialStochastic.run (maps h ν L hW c) c.data c.prior h.extend.feedback t ω).1 i j) ≤ _
      rw [ExponentialSGConfidence.computed_rawPairRadius_eq_model
        (maps h ν L hW c) c.data c.prior h hm hd t ht.le ω]
      exact (ExponentialScaledRadius.scaledRadius_bounds (model h ν L hW c hm).toM1Model
        (R+M+(ν : ℝ)) L c.radius_scale hH hL c.radius_nonneg hs1 t i j ω).2
  · simp only [radius, ExponentialActual.radius, if_neg ht]
    exact (CNDPayment.actualRadius_bounds (model h ν L hW c hm).toM1Model _ _ hH hL t i j ω).1

theorem actual_gap_budget_main
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (hν : (ν : ℝ)^2 = σ^2+σe^2) (hL : 0 ≤ L) (hWpos : 0 < W) (hs1 : c.radius_scale ≤ 1)
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j - h.broadcast t ω i ≤ W)
    {δa δn δg δl : ℝ} (ha : 0 < δa) (ha1 : δa < 1) (hn : 0 < δn) (hn1 : δn < 1)
    (hg : 0 < δg) (hl : 0 < δl) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δa+δn+(δg+δl) ∧ ∀ ω ∈ G,
      ExponentialSGPhysical.intervalConclusion (model h ν L hW c hm)
        (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) ν T W δa δn ω ∧
      ExponentialSGPhysical.pathConclusion (model h ν L hW c hm)
        (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) ν T W δa δn ω ∧
      (∀ u n, u+n ≤ T → 0<n →
        CNDPayment.intervalSum (ExponentialPhysical.payment (model h ν L hW c hm).toM1Model
          (radius h ν L hW c)) u n ω ≤
        CNDPayment.paymentEnvelope (model h ν L hW c hm).toM1Model (CNDInformation.canonicalChart (Fin K))
          (R+M+(ν : ℝ)) L T u n δg δl ω) := by
  exact ExponentialSGPayment.actual_e12_e13_with_gap_and_budget (model h ν L hW c hm)
    (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) ν hν
    (compositionLaws h ν L hW c hm hL hWpos hb) hW
    (ExponentialActual.center_measurable _ _ _ _ _ _) (ExponentialActual.radius_measurable _ _ _ _ _ _)
    (R+M+(ν : ℝ)) L (by linarith [h.R_nonneg,h.M_nonneg,ν.coe_nonneg]) hL
    (radius_le_canonical h ν L hW c hm hL hs1) ha ha1 hn hn1 hg hl

theorem canonical_maps_eq (hc : c.confidence_scale = 1) (hs : c.radius_scale = 1) :
    maps h ν L hW c = concreteMaps (R+M+(ν : ℝ)) L R W h.R_nonneg hW := by
  simp only [maps, ExponentialActual.maps, ExponentialGeometry.maps, hc, hs,
    ExponentialScaledMaps.decisionMaps_one]

theorem center_confidence_event {δc : ℝ} (hc : 0<δc) (hc1 : δc≤1)
    (hν : (ν : ℝ)^2 = σ^2+σe^2) (hT : 1≤T) (hK : 2≤K)
    (hcscale : c.confidence_scale=1) (hsscale : c.radius_scale=1)
    (hm : Protocol h ν (4*CNDNet.paperLc (Fin K) T δc) hW c (μ := μ) (σ := σ) (σe := σe)) :
    ∃ C : Set Ω, μ.real Cᶜ ≤ δc ∧ ∀ ω∈C,
      ExponentialPhysical.Covers (θ := θ)
        (center h ν (4*CNDNet.paperLc (Fin K) T δc) hW c)
        (radius h ν (4*CNDNet.paperLc (Fin K) T δc) hW c) T ω := by
  let Lc := CNDNet.paperLc (Fin K) T δc
  have ho := canonical_maps_eq h ν (4*Lc) hW c hcscale hsscale
  have hm' : ExponentialSGStochastic.FiniteLaws (ExponentialSGConfidence.maps h ν Lc W hW)
      c.data c.prior h (μ := μ) (σ := σ) (σe := σe) := by
    change ExponentialSGStochastic.FiniteLaws
      (concreteMaps (R+M+(ν : ℝ)) (4*Lc) R W h.R_nonneg hW) c.data c.prior h
    rw [←ho]
    exact hm
  obtain ⟨C,hC,hcover⟩ := ExponentialSGConfidence.center_confidence_event h c.data c.range_eq c.prior
    ν hν W hW hT hK hc hc1 hm'
  refine ⟨C,hC,?_⟩
  intro ω hω t ht i j
  have hh := hcover ω hω t ht.le i j
  have hcenter (k : Fin K) : center h ν (4*Lc) hW c t k ω =
      ExponentialSGConfidence.center h c.data c.prior ν Lc W hW t ω k := by
    simp only [center, ExponentialActual.center, if_pos ht,
      ExponentialActual.state, ExponentialSGConfidence.center]
    change confidence (maps h ν (4*Lc) hW c) c.data
      (ExponentialStochastic.run (maps h ν (4*Lc) hW c) c.data c.prior h.extend.feedback t ω) k = _
    rw [ho]
    rfl
  have hradius : radius h ν (4*Lc) hW c t i j ω =
      ExponentialSGConfidence.radius h c.data c.prior ν Lc W hW t ω i j := by
    simp only [radius, ExponentialActual.radius, if_pos ht,
      ExponentialActual.state, ExponentialSGConfidence.radius]
    change CNDProcess.radius (maps h ν (4*Lc) hW c) c.data
      (ExponentialStochastic.run (maps h ν (4*Lc) hW c) c.data c.prior h.extend.feedback t ω) i j = _
    rw [ho]
    rfl
  change |(θ i-θ j)-(center h ν (4*Lc) hW c t i ω-center h ν (4*Lc) hW c t j ω)| ≤
    radius h ν (4*Lc) hW c t i j ω
  rw [hcenter i,hcenter j,hradius]
  convert hh using 1 <;> congr 1 <;> ring

def legalIntervalConclusion
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe)) (δa δn : ℝ) (ω : Ω) : Prop :=
  ∀ u n, u+n≤T → 0<n → ∀ k,
    CNDPayment.intervalSum (fun t ω => ExponentialSGPhysical.physical (model h ν L hW c hm)
      t ((model h ν L hW c hm).action t ω) ω -
      ExponentialSGPhysical.physical (model h ν L hW c hm) t k ω) u n ω ≤
    ExponentialComposition.envelope (model h ν L hW c hm).toM1Model
      (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) T W u n k ω +
      ExponentialPhysical.actionBound W T n δa + ExponentialSGPhysical.noiseBound (ι := Fin K) ν T n δn +
      CNDPayment.intervalSum (ExponentialPhysical.payment (model h ν L hW c hm).toM1Model
        (radius h ν L hW c)) u n ω

def legalPathConclusion
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe)) (δa δn : ℝ) (ω : Ω) : Prop :=
  ∀ path : ℕ → Fin K,
    (∑ t∈range T, (ExponentialSGPhysical.physical (model h ν L hW c hm)
      t ((model h ν L hW c hm).action t ω) ω -
      ExponentialSGPhysical.physical (model h ν L hW c hm) t (path t) ω)) ≤
    (∑ j∈(SwitchingRuns.partition path T).labels,
      ExponentialComposition.envelope (model h ν L hW c hm).toM1Model
        (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) T W
        (ExponentialComposition.runStart path T j) (ExponentialComposition.runLength path T j)
        (SwitchingRuns.label path T j) ω) +
      ExponentialSGPhysical.noiseCoefficient (ι := Fin K) ν W T δa δn *
        Real.sqrt ((T : ℝ) * ((ExponentialComposition.switchCount T path+1 : ℕ) : ℝ)) +
      CNDPayment.intervalSum (ExponentialPhysical.payment (model h ν L hW c hm).toM1Model
        (radius h ν L hW c)) 0 T ω

def intervalBound
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (δa δn : ℝ) (withGap : Bool) (u n : ℕ) (k : Fin K) (ω : Ω) : ℝ :=
  ExponentialComposition.envelope (model h ν L hW c hm).toM1Model
    (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) T W u n k ω +
    ExponentialPhysical.actionBound W T n δa + ExponentialSGPhysical.noiseBound (ι := Fin K) ν T n δn +
    CNDPayment.intervalSum (ExponentialPhysical.payment (model h ν L hW c hm).toM1Model
      (radius h ν L hW c)) u n ω +
    (if withGap then ExponentialGap.gapLedger (θ := θ) (center h ν L hW c) (radius h ν L hW c) u n ω else 0)

def pathBound
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (δa δn : ℝ) (withGap : Bool) (path : ℕ → Fin K) (ω : Ω) : ℝ :=
  (∑ j∈(SwitchingRuns.partition path T).labels,
    ExponentialComposition.envelope (model h ν L hW c hm).toM1Model
      (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) T W
      (ExponentialComposition.runStart path T j) (ExponentialComposition.runLength path T j)
      (SwitchingRuns.label path T j) ω) +
    ExponentialSGPhysical.noiseCoefficient (ι := Fin K) ν W T δa δn *
      Real.sqrt ((T : ℝ)*((ExponentialComposition.switchCount T path+1 : ℕ) : ℝ)) +
    CNDPayment.intervalSum (ExponentialPhysical.payment (model h ν L hW c hm).toM1Model
      (radius h ν L hW c)) 0 T ω +
    (if withGap then ExponentialGap.gapLedger (θ := θ) (center h ν L hW c) (radius h ν L hW c) 0 T ω else 0)

/-- Directly on the original finite physical losses and selected actions. -/
def originalConclusions
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (δa δn : ℝ) (withGap : Bool) (ω : Ω) : Prop :=
  (∀ u n, u+n≤T → 0<n → ∀ k,
    CNDPayment.intervalSum (fun t ω => h.physical t (h.action t ω) ω-h.physical t k ω) u n ω ≤
      intervalBound h ν L hW c hm δa δn withGap u n k ω) ∧
  (∀ path : ℕ → Fin K,
    (∑ t∈range T, (h.physical t (h.action t ω) ω-h.physical t (path t) ω)) ≤
      pathBound h ν L hW c hm δa δn withGap path ω)

theorem original_of_gap
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe)) (δa δn : ℝ) (ω : Ω)
    (hi : ExponentialSGPhysical.intervalConclusion (model h ν L hW c hm)
      (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) ν T W δa δn ω)
    (hp : ExponentialSGPhysical.pathConclusion (model h ν L hW c hm)
      (center h ν L hW c) (radius h ν L hW c) (trajectory h ν L hW c) ν T W δa δn ω) :
    originalConclusions h ν L hW c hm δa δn true ω := by
  constructor
  · intro u n hu hn k
    have hh := hi u n hu hn k
    rw [interval_regret_eq_original h ν L hW c hm u n hu k ω] at hh
    exact hh
  · intro path
    have hh := hp path
    rw [path_regret_eq_original h ν L hW c hm path ω] at hh
    exact hh

theorem original_of_legal
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe)) (δa δn : ℝ) (ω : Ω)
    (hi : legalIntervalConclusion h ν L hW c hm δa δn ω)
    (hp : legalPathConclusion h ν L hW c hm δa δn ω) :
    originalConclusions h ν L hW c hm δa δn false ω := by
  constructor
  · intro u n hu hn k
    have hh := hi u n hu hn k
    rw [interval_regret_eq_original h ν L hW c hm u n hu k ω] at hh
    simpa only [intervalBound, Bool.false_eq_true, if_false, add_zero] using hh
  · intro path
    have hh := hp path
    rw [path_regret_eq_original h ν L hW c hm path ω] at hh
    simpa only [pathBound, Bool.false_eq_true, if_false, add_zero] using hh

/-- The legal canonical branch has no gap ledger and no assumed E11 event.
The confidence event is proved from this same actual SG score/recursion. -/
theorem actual_legal_main {δc : ℝ} (hc : 0<δc) (hc1 : δc≤1)
    (hν : (ν : ℝ)^2 = σ^2+σe^2) (hT : 1≤T) (hK : 2≤K) (hWpos : 0<W)
    (hcscale : c.confidence_scale=1) (hsscale : c.radius_scale=1)
    (hm : Protocol h ν (4*CNDNet.paperLc (Fin K) T δc) hW c (μ := μ) (σ := σ) (σe := σe))
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W)
    {δa δn : ℝ} (ha : 0<δa) (ha1 : δa<1) (hn : 0<δn) (hn1 : δn<1) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc+δa+δn ∧ ∀ ω∈G,
      legalIntervalConclusion h ν (4*CNDNet.paperLc (Fin K) T δc) hW c hm δa δn ω ∧
      legalPathConclusion h ν (4*CNDNet.paperLc (Fin K) T δc) hW c hm δa δn ω := by
  let L := 4*CNDNet.paperLc (Fin K) T δc
  let m := model h ν L hW c hm
  let a := center h ν L hW c
  let r := radius h ν L hW c
  let v := trajectory h ν L hW c
  have hL : 0≤L := by
    have hl := (CNDNet.paper_Lc_budget (ι := Fin K) T hc hc1).1
    dsimp only [L]
    exact mul_nonneg (by norm_num) (zero_le_one.trans hl)
  have hv := compositionLaws h ν L hW c hm hL hWpos hb
  obtain ⟨C,hC,hcover⟩ := center_confidence_event h ν hW c hc hc1 hν hT hK hcscale hsscale hm
  obtain ⟨G,hG,hprob,hgood⟩ := ExponentialSGPhysical.conditional_e12_e13 m a r ν hν hW T
    (ExponentialActual.center_measurable _ _ _ _ _ _) (ExponentialActual.radius_measurable _ _ _ _ _ _)
    hv.support_span ha ha1 hn hn1 C hC hcover
    (ExponentialComposition.envelope m.toM1Model a r v T W)
    (ExponentialComposition.actual_interval_envelope m.toM1Model a r v hv)
  refine ⟨G,hG,hprob,?_⟩
  intro ω hω
  refine ⟨(hgood ω hω).1,?_⟩
  intro path
  have hp := (hgood ω hω).2 (SwitchingRuns.partition path T)
    (ExponentialComposition.runStart path T) (ExponentialComposition.runLength path T)
    (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).1)
    (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).2.1)
    (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).2.2)
    path (SwitchingRuns.label path T)
    (fun j hj t ht => SwitchingRuns.block_constant path T j hj ht)
  rw [ExponentialComposition.maximal_run_card path T (by omega)] at hp
  exact hp

theorem actual_legal_budget_main {δc : ℝ} (hc : 0<δc) (hc1 : δc≤1)
    (hν : (ν : ℝ)^2 = σ^2+σe^2) (hT : 1≤T) (hK : 2≤K) (hWpos : 0<W)
    (hcscale : c.confidence_scale=1) (hsscale : c.radius_scale=1)
    (hm : Protocol h ν (4*CNDNet.paperLc (Fin K) T δc) hW c (μ := μ) (σ := σ) (σe := σe))
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W)
    {δa δn δg δl : ℝ} (ha : 0<δa) (ha1 : δa<1) (hn : 0<δn) (hn1 : δn<1)
    (hg : 0<δg) (hl : 0<δl) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc+δa+δn+(δg+δl) ∧ ∀ ω∈G,
      legalIntervalConclusion h ν (4*CNDNet.paperLc (Fin K) T δc) hW c hm δa δn ω ∧
      legalPathConclusion h ν (4*CNDNet.paperLc (Fin K) T δc) hW c hm δa δn ω ∧
      (∀ u n, u+n≤T → 0<n →
        CNDPayment.intervalSum
          (ExponentialPhysical.payment (model h ν (4*CNDNet.paperLc (Fin K) T δc) hW c hm).toM1Model
            (radius h ν (4*CNDNet.paperLc (Fin K) T δc) hW c)) u n ω ≤
        CNDPayment.paymentEnvelope (model h ν (4*CNDNet.paperLc (Fin K) T δc) hW c hm).toM1Model
          (CNDInformation.canonicalChart (Fin K)) (R+M+(ν : ℝ))
          (4*CNDNet.paperLc (Fin K) T δc) T u n δg δl ω) := by
  classical
  let L := 4*CNDNet.paperLc (Fin K) T δc
  let m := model h ν L hW c hm
  let r := radius h ν L hW c
  have hL : 0≤L := by
    have hlc := (CNDNet.paper_Lc_budget (ι := Fin K) T hc hc1).1
    dsimp only [L]
    exact mul_nonneg (by norm_num) (zero_le_one.trans hlc)
  obtain ⟨C,hC,hprob,hgood⟩ := actual_legal_main h ν hW c hc hc1 hν hT hK hWpos
    hcscale hsscale hm hb ha ha1 hn hn1
  let Bad : Set Ω := {ω | ∃ u n, u+n≤T ∧ 0<n ∧
    CNDPayment.paymentEnvelope m.toM1Model (CNDInformation.canonicalChart (Fin K))
      (R+M+(ν : ℝ)) L T u n δg δl ω < CNDPayment.intervalSum (CNDPayment.observablePayment m.toM1Model r) u n ω}
  have hBad : μ.real Bad ≤ δg+δl := ExponentialScaledRadius.dominatedPayment_envelope_delta
    m.toM1Model r (R+M+(ν : ℝ)) L (by linarith [h.R_nonneg,h.M_nonneg,ν.coe_nonneg]) hL
    (radius_le_canonical h ν L hW c hm hL (by rw [hsscale])) T hg hl
  let B := toMeasurable μ (Cᶜ ∪ Bad)
  refine ⟨Bᶜ,(measurableSet_toMeasurable μ _).compl,?_,?_⟩
  · have hbnd := (measureReal_union_le Cᶜ Bad).trans (add_le_add hprob hBad)
    simpa only [B,compl_compl,measureReal_def,measure_toMeasurable] using hbnd
  · intro ω hω
    have hnot : ω∉Cᶜ∪Bad := fun hw => hω (subset_toMeasurable μ _ hw)
    have hωC : ω∈C := by by_contra hw; exact hnot (Or.inl hw)
    refine ⟨(hgood ω hωC).1,(hgood ω hωC).2,?_⟩
    intro u n hu hn'
    have hp : CNDPayment.intervalSum (CNDPayment.observablePayment m.toM1Model r) u n ω ≤
        CNDPayment.paymentEnvelope m.toM1Model (CNDInformation.canonicalChart (Fin K))
          (R+M+(ν : ℝ)) L T u n δg δl ω :=
      le_of_not_gt (fun hx => hnot (Or.inr ⟨u,n,hu,hn',hx⟩))
    exact hp

def paymentConclusion
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (δg δl : ℝ) (ω : Ω) : Prop :=
  ∀ u n, u+n≤T → 0<n →
    CNDPayment.intervalSum (ExponentialPhysical.payment (model h ν L hW c hm).toM1Model
      (radius h ν L hW c)) u n ω ≤
    CNDPayment.paymentEnvelope (model h ν L hW c hm).toM1Model (CNDInformation.canonicalChart (Fin K))
      (R+M+(ν : ℝ)) L T u n δg δl ω

/-- Thin original-feedback corollary: only the proved prefix identities
are used to replace the left sides by the original SG physical losses. -/
theorem original_gap_budget_main
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (hν : (ν : ℝ)^2 = σ^2+σe^2) (hL : 0≤L) (hWpos : 0<W) (hs1 : c.radius_scale≤1)
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W)
    {δa δn δg δl : ℝ} (ha : 0<δa) (ha1 : δa<1) (hn : 0<δn) (hn1 : δn<1)
    (hg : 0<δg) (hl : 0<δl) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ≤δa+δn+(δg+δl) ∧ ∀ ω∈G,
      originalConclusions h ν L hW c hm δa δn true ω ∧ paymentConclusion h ν L hW c hm δg δl ω := by
  obtain ⟨G,hG,hprob,hgood⟩ := actual_gap_budget_main h ν L hW c hm hν hL hWpos hs1 hb
    ha ha1 hn hn1 hg hl
  exact ⟨G,hG,hprob,fun ω hω => ⟨original_of_gap h ν L hW c hm δa δn ω
    (hgood ω hω).1 (hgood ω hω).2.1,(hgood ω hω).2.2⟩⟩

theorem original_legal_budget_main {δc : ℝ} (hc : 0<δc) (hc1 : δc≤1)
    (hν : (ν : ℝ)^2 = σ^2+σe^2) (hT : 1≤T) (hK : 2≤K) (hWpos : 0<W)
    (hcscale : c.confidence_scale=1) (hsscale : c.radius_scale=1)
    (hm : Protocol h ν (4*CNDNet.paperLc (Fin K) T δc) hW c (μ := μ) (σ := σ) (σe := σe))
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W)
    {δa δn δg δl : ℝ} (ha : 0<δa) (ha1 : δa<1) (hn : 0<δn) (hn1 : δn<1)
    (hg : 0<δg) (hl : 0<δl) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ≤δc+δa+δn+(δg+δl) ∧ ∀ ω∈G,
      originalConclusions h ν (4*CNDNet.paperLc (Fin K) T δc) hW c hm δa δn false ω ∧
      paymentConclusion h ν (4*CNDNet.paperLc (Fin K) T δc) hW c hm δg δl ω := by
  obtain ⟨G,hG,hprob,hgood⟩ := actual_legal_budget_main h ν hW c hc hc1 hν hT hK hWpos
    hcscale hsscale hm hb ha ha1 hn hn1 hg hl
  exact ⟨G,hG,hprob,fun ω hω => ⟨original_of_legal h ν (4*CNDNet.paperLc (Fin K) T δc) hW c hm
    δa δn ω (hgood ω hω).1 (hgood ω hω).2.1,(hgood ω hω).2.2⟩⟩

theorem support_span_of_proxy_nonpos (p l : Fin K → ℝ)
    (hp : ∀ i, 0≤p i) (hs : ∑ i, p i=1)
    (hl : ∀ k, (∑ i, p i*l i)-l k≤0)
    (i j : Fin K) (hi : 0<p i) (hj : 0<p j) : |l i-l j|≤0 := by
  let avg := ∑ i, p i*l i
  have hd (k : Fin K) : 0≤l k-avg := by have hk := hl k; dsimp only [avg]; linarith
  have hnonneg (k : Fin K) : 0≤p k*(l k-avg) := mul_nonneg (hp k) (hd k)
  have hsum : (∑ k, p k*(l k-avg))=0 := by
    simp only [mul_sub, sum_sub_distrib, ←sum_mul, hs, one_mul]
    dsimp only [avg]
    ring
  have heq (k : Fin K) (hk : 0<p k) : l k=avg := by
    have ht := single_le_sum (fun k _ => hnonneg k) (mem_univ k)
    rw [hsum] at ht
    have hd' : l k-avg≤0 := (mul_le_mul_left hk).mp (by simpa only [mul_zero] using ht)
    linarith [hd k]
  rw [heq i hi, heq j hj, sub_self, abs_zero]

/-- The actual W=0 branch skips expert updates. Its proxy regret is
nonpositive by canonical optimality, so no positive-width expert envelope
or exponential update law is required. -/
theorem actual_zero_width_main
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (hν : (ν : ℝ)^2 = σ^2+σe^2) (hL : 0≤L) (hw0 : W=0) (hT : 0<T)
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W)
    {δa δn : ℝ} (ha : 0<δa) (ha1 : δa<1) (hn : 0<δn) (hn1 : δn<1) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ≤δa+δn ∧ ∀ ω∈G,
      (∀ u n, u+n≤T → 0<n → ∀ k,
        CNDPayment.intervalSum (fun t ω => ExponentialSGPhysical.physical (model h ν L hW c hm)
          t ((model h ν L hW c hm).action t ω) ω -
          ExponentialSGPhysical.physical (model h ν L hW c hm) t k ω) u n ω ≤
        ExponentialSGPhysical.noiseBound (ι := Fin K) ν T n δn +
          CNDPayment.intervalSum (ExponentialPhysical.payment (model h ν L hW c hm).toM1Model
            (radius h ν L hW c)) u n ω +
          ExponentialGap.gapLedger (θ := θ) (center h ν L hW c) (radius h ν L hW c) u n ω) ∧
      (∀ path : ℕ → Fin K,
        (∑ t∈range T, (ExponentialSGPhysical.physical (model h ν L hW c hm)
          t ((model h ν L hW c hm).action t ω) ω -
          ExponentialSGPhysical.physical (model h ν L hW c hm) t (path t) ω)) ≤
        ExponentialSGPhysical.noiseCoefficient (ι := Fin K) ν 0 T δa δn *
          Real.sqrt ((T : ℝ)*((ExponentialComposition.switchCount T path+1 : ℕ) : ℝ)) +
          CNDPayment.intervalSum (ExponentialPhysical.payment (model h ν L hW c hm).toM1Model
            (radius h ν L hW c)) 0 T ω +
          ExponentialGap.gapLedger (θ := θ) (center h ν L hW c) (radius h ν L hW c) 0 T ω) := by
  let m := model h ν L hW c hm
  let a := center h ν L hW c
  let r := radius h ν L hW c
  let rplus := ExponentialGap.analysisRadius (θ := θ) a r
  have hbridge := bridge h ν L hW c hm
  have hloss (t : ℕ) (ht : t<T) (ω : Ω) (i : Fin K) :
      ExponentialPhysical.loss m.toM1Model a r t i ω =
        processLoss (maps h ν L hW c) c.data t
          (ExponentialStochastic.run (maps h ν L hW c) c.data c.prior h.extend.feedback t ω)
          (h.extend.broadcast t ω) i :=
    ExponentialActual.loss_before _ _ _ _ _ _ _ hbridge t ht ω i
  have hlossAfter (t : ℕ) (ht : ¬t<T) (ω : Ω) (i : Fin K) :
      ExponentialPhysical.loss m.toM1Model a r t i ω = 0 :=
    ExponentialActual.loss_after _ _ _ _ _ _ _ hbridge t ht ω i
  have ham := ExponentialActual.center_measurable (R+M+(ν : ℝ)) L h.R_nonneg hW c h.extend.feedback
  have hrm := ExponentialActual.radius_measurable (R+M+(ν : ℝ)) L h.R_nonneg hW c h.extend.feedback
  have hrplus : ∀ t i j, Measurable[ℱ t] (rplus t i j) :=
    fun t i j => (hrm t i j).add (ExponentialGap.gap_measurable a r ham hrm t)
  have hproxy (u n : ℕ) (hu : u+n≤T) (k : Fin K) (ω : Ω) :
      CNDPayment.intervalSum (ExponentialPhysical.proxyRegret m.toM1Model a rplus k) u n ω≤0 := by
    unfold CNDPayment.intervalSum
    apply sum_nonpos
    intro s hs
    have ht : u+s<T := by have := mem_range.mp hs; omega
    rw [ExponentialGap.proxyRegret_analysisRadius]
    unfold ExponentialPhysical.proxyRegret
    simp_rw [hloss (u+s) ht ω]
    rw [hbridge.p_before (u+s) ht]
    exact ExponentialGeometry.zero_width_proxy_nonpos (R+M+(ν : ℝ)) L R W h.R_nonneg hW c h.extend.feedback
      (by linarith [h.R_nonneg,h.M_nonneg,ν.coe_nonneg]) hL hw0 (u+s) ω k
      (by intro i j; change h.extend.broadcast (u+s) ω j-h.extend.broadcast (u+s) ω i≤W
          simpa only [h.extend_broadcast ht] using hb (u+s) ht ω i j)
  have hspan : ∀ t ω i j, 0<m.p t i ω → 0<m.p t j ω →
      |ExponentialPhysical.loss m.toM1Model a rplus t i ω-
        ExponentialPhysical.loss m.toM1Model a rplus t j ω|≤2*W := by
    apply ExponentialGap.support_span_analysisRadius m.toM1Model a r W
    intro t ω i j hi hj
    by_cases ht : t<T
    · simp_rw [hloss t ht ω]
      rw [hbridge.p_before t ht] at hi hj
      let o := maps h ν L hW c
      let s := ExponentialStochastic.run o c.data c.prior h.extend.feedback t ω
      have hp := ExponentialStochastic.runProbability_simplex o c.data c.prior h.extend.feedback t ω
      have hh := support_span_of_proxy_nonpos
        (fun k => probability o c.data t s k) (processLoss o c.data t s (h.extend.broadcast t ω)) hp.1 hp.2
        (fun k => ExponentialGeometry.zero_width_proxy_nonpos (R+M+(ν : ℝ)) L R W h.R_nonneg hW c h.extend.feedback
          (by linarith [h.R_nonneg,h.M_nonneg,ν.coe_nonneg]) hL hw0 t ω k
          (by intro i j; change h.extend.broadcast t ω j-h.extend.broadcast t ω i≤W
              simpa only [h.extend_broadcast ht] using hb t ht ω i j)) i j hi hj
      simpa only [hw0, mul_zero] using hh
    · simp_rw [hlossAfter t ht ω]
      simp [hw0]
  obtain ⟨G,hG,hprob,hgood⟩ := ExponentialSGPhysical.conditional_e12_e13 m a rplus ν hν hW T
    ham hrplus hspan (δc:=0) ha ha1 hn hn1 Set.univ (by simp)
    (fun ω _ => ExponentialGap.analysisRadius_covers a r T ω) (fun _ _ _ _ => 0) hproxy
  refine ⟨G,hG,by simpa using hprob,?_⟩
  intro ω hω
  constructor
  · intro u n hu hn' k
    have hi := (hgood ω hω).1 u n hu hn' k
    dsimp only [rplus] at hi
    simpa only [ExponentialPhysical.actionBound, hw0, zero_mul, zero_add,
      ExponentialGap.payment_interval_analysisRadius, add_assoc] using hi
  · intro path
    have hp := (hgood ω hω).2 (SwitchingRuns.partition path T)
      (ExponentialComposition.runStart path T) (ExponentialComposition.runLength path T)
      (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).1)
      (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).2.1)
      (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).2.2)
      path (SwitchingRuns.label path T)
      (fun j hj t ht => SwitchingRuns.block_constant path T j hj ht)
    rw [ExponentialComposition.maximal_run_card path T hT] at hp
    dsimp only [rplus] at hp
    simpa only [sum_const_zero, zero_add, hw0, ExponentialGap.payment_interval_analysisRadius, add_assoc] using hp

end Part2.ExponentialSGFinite
