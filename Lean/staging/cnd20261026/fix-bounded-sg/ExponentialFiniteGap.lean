import staging.cnd20261026.«fix-bounded-sg».ExponentialFiniteConfidence
import staging.cnd20261026.«fix-bounded-sg».ExponentialGap
import staging.cnd20261026.«fix-bounded-sg».ExponentialScaledRadius

/-! Actual bounded-feedback exponential algorithm with arbitrary configured
confidence scale and nonnegative radius scale. The expert laws are derived
from this one actual run; no E11 or final regret bound is an input. -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 2400000

namespace Part2.ExponentialFiniteGap
open CNDProcess CNDHorizon ExponentialFinite

variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)]
  {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}
  {θ : Fin K → ℝ} {R M D W : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (h : BoundedInputs ℱ θ R M D T) (L : ℝ) (hW : 0 < W)
  (c : ExponentialFinite.Config (K := K) (E := E) T R W)

def actualLedger (hm : Protocol h L hW c (μ := μ)) (u n : ℕ) (ω : Ω) : ℝ :=
  CNDPayment.intervalSum
    (ExponentialPhysical.payment (model h L hW c hm) (radius h L hW c)) u n ω

/-- The empty interval has budget zero; positive lengths use the original
canonical payment envelope on this exact model and execution probabilities. -/
def budgetLedger (hm : Protocol h L hW c (μ := μ)) (δg δl : ℝ)
    (u n : ℕ) (ω : Ω) : ℝ :=
  if n = 0 then 0 else CNDPayment.paymentEnvelope (model h L hW c hm)
    (CNDInformation.canonicalChart (Fin K)) (R+M+D) L T u n δg δl ω

/-- Both left sides use the original finite physical losses and actions.
The comparator path and its actual switch count can be chosen after omega. -/
def Conclusions (hm : Protocol h L hW c (μ := μ)) (δa δe : ℝ)
    (withGap : Bool) (ledger : ℕ → ℕ → Ω → ℝ) (ω : Ω) : Prop :=
  (∀ u n, u+n ≤ T → 0 < n → ∀ k,
    (∑ t ∈ Ico u (u+n), (h.physical t (h.action t ω) ω - h.physical t k ω)) ≤
      ExponentialComposition.envelope (model h L hW c hm) (center h L hW c)
        (radius h L hW c) (trajectory h L hW c) T W u n k ω +
      ExponentialPhysical.actionBound W T n δa +
      ExponentialPhysical.encodingBound (ι := Fin K) (D := D) T n δe + ledger u n ω +
      (if withGap then ExponentialGap.gapLedger (θ := θ)
        (center h L hW c) (radius h L hW c) u n ω else 0)) ∧
  (∀ path : ℕ → Fin K,
    (∑ t ∈ range T, (h.physical t (h.action t ω) ω - h.physical t (path t) ω)) ≤
      (∑ j ∈ (SwitchingRuns.partition path T).labels,
        ExponentialComposition.envelope (model h L hW c hm) (center h L hW c)
          (radius h L hW c) (trajectory h L hW c) T W
          (ExponentialComposition.runStart path T j) (ExponentialComposition.runLength path T j)
          (SwitchingRuns.label path T j) ω) +
      ExponentialPhysical.noiseCoefficient (ι := Fin K) (D := D) W T δa δe *
        Real.sqrt ((T : ℝ) * ((ExponentialComposition.switchCount T path+1 : ℕ) : ℝ)) +
      ledger 0 T ω +
      (if withGap then ExponentialGap.gapLedger (θ := θ)
        (center h L hW c) (radius h L hW c) 0 T ω else 0))

def ActualConclusions (hm : Protocol h L hW c (μ := μ)) (δa δe : ℝ) (ω : Ω) : Prop :=
  Conclusions h L hW c hm δa δe true (actualLedger h L hW c hm) ω

def BudgetConclusions (hm : Protocol h L hW c (μ := μ)) (δa δe δg δl : ℝ) (ω : Ω) : Prop :=
  Conclusions h L hW c hm δa δe true (budgetLedger h L hW c hm δg δl) ω

def UnitBudgetConclusions (hm : Protocol h L hW c (μ := μ))
    (δa δe δg δl : ℝ) (ω : Ω) : Prop :=
  Conclusions h L hW c hm δa δe false (budgetLedger h L hW c hm δg δl) ω

theorem conclusions_mono (hm : Protocol h L hW c (μ := μ)) (δa δe : ℝ)
    (withGap : Bool) (ledger ledger' : ℕ → ℕ → Ω → ℝ) (ω : Ω)
    (hle : ∀ u n, u+n ≤ T → ledger u n ω ≤ ledger' u n ω)
    (hc : Conclusions h L hW c hm δa δe withGap ledger ω) :
    Conclusions h L hW c hm δa δe withGap ledger' ω := by
  constructor
  · intro u n hu hn k
    exact (hc.1 u n hu hn k).trans (by linarith [hle u n hu])
  · intro path
    exact (hc.2 path).trans (by linarith [hle 0 T (by omega)])

/-- The final expert Laws are derived from actual protocol equations and
geometry; neither Laws, E11 nor a target expert-regret bound is an input. -/
theorem original_gap_main (hm : Protocol h L hW c (μ := μ)) (hL : 0 ≤ L)
    (hb : ∀ t < T, ∀ ω i j, h.broadcast t ω j - h.broadcast t ω i ≤ W)
    {δa δe : ℝ} (ha : 0 < δa) (ha1 : δa < 1) (he : 0 < δe) (he1 : δe < 1) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δa+δe ∧
      ∀ ω ∈ G, ActualConclusions h L hW c hm δa δe ω := by
  obtain ⟨G,hG,hprob,hgood⟩ := ExponentialGap.actual_e12_e13_with_gap
    (model h L hW c hm) (center h L hW c) (radius h L hW c) (trajectory h L hW c)
    (compositionLaws h L hW c hm hL hb) hW.le
    (center_measurable h L hW c) (radius_measurable h L hW c) ha ha1 he he1
  refine ⟨G,hG,hprob,?_⟩
  intro ω hω
  constructor
  · intro u n hu hn k
    have hi := (hgood ω hω).1 u n hu hn k
    rw [interval_physical_eq h L hW c hm u n hu k ω] at hi
    exact hi
  · intro path
    have hp := (hgood ω hω).2 path
    rw [path_physical_eq h L hW c hm path ω] at hp
    exact hp

/-- The actual state statistics identify the same model.p radius. Scaling
is inside saturation; the argument uses no unit confidence-scale premise. -/
theorem radius_le_canonical (hm : Protocol h L hW c (μ := μ))
    (hL : 0 ≤ L) (hs1 : c.radius_scale ≤ 1) (t : ℕ) (i j : Fin K) (ω : Ω) :
    radius h L hW c t i j ω ≤
      CNDPayment.actualRadius (model h L hW c hm) (R+M+D) L t i j ω := by
  have hH : 0 ≤ R+M+D := by linarith [h.R_nonneg,h.M_nonneg,h.D_nonneg]
  by_cases ht : t < T
  · by_cases hz : R = 0
    · have hzradius : radius h L hW c t i j ω = 0 := by
        rw [ExponentialFinite.radius, if_pos ht, CNDProcess.radius,
          if_pos (by rw [c.range_eq]; exact hz)]
      rw [hzradius]
      exact (CNDPayment.actualRadius_bounds (model h L hW c hm) _ _ hH hL t i j ω).1
    · have hd : c.data.R ≠ 0 := by rwa [c.range_eq]
      rw [ExponentialFinite.radius, if_pos ht, CNDProcess.radius, if_neg hd]
      change CNDPhysical.saturatedRadius R (c.radius_scale *
        StatisticalMaps.rawPairRadius (R+M+D) L R (state h L hW c t ω).1 i j) ≤ _
      rw [ExponentialFinite.computed_pairRadius_eq_model h L hW c hm hd t ht.le ω]
      exact (ExponentialScaledRadius.scaledRadius_bounds (model h L hW c hm)
        (R+M+D) L c.radius_scale hH hL c.radius_nonneg hs1 t i j ω).2
  · simp only [ExponentialFinite.radius, if_neg ht]
    exact (CNDPayment.actualRadius_bounds (model h L hW c hm) _ _ hH hL t i j ω).1

def PaymentConclusion (hm : Protocol h L hW c (μ := μ)) (δg δl : ℝ) (ω : Ω) : Prop :=
  ∀ u n, u+n ≤ T → 0 < n → actualLedger h L hW c hm u n ω ≤
    CNDPayment.paymentEnvelope (model h L hW c hm) (CNDInformation.canonicalChart (Fin K))
      (R+M+D) L T u n δg δl ω

/-- Add the same-p payment budget to an already proved common event.
This is shared only by the two actual-algorithm corollaries below. -/
theorem payment_event (hm : Protocol h L hW c (μ := μ)) (hL : 0 ≤ L)
    (hs1 : c.radius_scale ≤ 1) (withGap : Bool) (δbase δa δe : ℝ)
    (C : Set Ω) (hC : MeasurableSet C) (hprob : μ.real Cᶜ ≤ δbase)
    (hgood : ∀ ω ∈ C,
      Conclusions h L hW c hm δa δe withGap (actualLedger h L hW c hm) ω)
    {δg δl : ℝ} (hg : 0 < δg) (hl : 0 < δl) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δbase+(δg+δl) ∧ ∀ ω ∈ G,
      Conclusions h L hW c hm δa δe withGap (actualLedger h L hW c hm) ω ∧
      Conclusions h L hW c hm δa δe withGap (budgetLedger h L hW c hm δg δl) ω ∧
      PaymentConclusion h L hW c hm δg δl ω := by
  classical
  let m := model h L hW c hm
  let r := radius h L hW c
  let Bad : Set Ω := {ω | ∃ u n, u+n ≤ T ∧ 0 < n ∧
    CNDPayment.paymentEnvelope m (CNDInformation.canonicalChart (Fin K)) (R+M+D) L T u n δg δl ω <
      CNDPayment.intervalSum (CNDPayment.observablePayment m r) u n ω}
  have hBad : μ.real Bad ≤ δg+δl := ExponentialScaledRadius.dominatedPayment_envelope_delta
    m r (R+M+D) L (by linarith [h.R_nonneg,h.M_nonneg,h.D_nonneg]) hL
    (radius_le_canonical h L hW c hm hL hs1) T hg hl
  let B := toMeasurable μ (Cᶜ ∪ Bad)
  refine ⟨Bᶜ,(measurableSet_toMeasurable μ _).compl,?_,?_⟩
  · have hbnd := (measureReal_union_le Cᶜ Bad).trans (add_le_add hprob hBad)
    simpa only [B,compl_compl,measureReal_def,measure_toMeasurable] using hbnd
  · intro ω hω
    have hnot : ω ∉ Cᶜ ∪ Bad := fun hw => hω (subset_toMeasurable μ _ hw)
    have hωC : ω ∈ C := by by_contra hw; exact hnot (Or.inl hw)
    have hpay : PaymentConclusion h L hW c hm δg δl ω := by
      intro u n hu hn
      exact le_of_not_gt (fun hx => hnot (Or.inr ⟨u,n,hu,hn,hx⟩))
    refine ⟨hgood ω hωC, ?_, hpay⟩
    apply conclusions_mono h L hW c hm δa δe withGap
      (actualLedger h L hW c hm) (budgetLedger h L hW c hm δg δl) ω _ (hgood ω hωC)
    intro u n hu
    by_cases hn : n = 0
    · simp [hn,actualLedger,budgetLedger,CNDPayment.intervalSum]
    · simpa only [budgetLedger,if_neg hn] using hpay u n hu (Nat.pos_of_ne_zero hn)

/-- The actual private ledger, its canonical budget, and both original
physical regret conclusions all hold on one measurable event. -/
theorem original_gap_budget_main (hm : Protocol h L hW c (μ := μ)) (hL : 0 ≤ L)
    (hs1 : c.radius_scale ≤ 1)
    (hb : ∀ t < T, ∀ ω i j, h.broadcast t ω j - h.broadcast t ω i ≤ W)
    {δa δe δg δl : ℝ} (ha : 0 < δa) (ha1 : δa < 1) (he : 0 < δe) (he1 : δe < 1)
    (hg : 0 < δg) (hl : 0 < δl) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δa+δe+(δg+δl) ∧ ∀ ω ∈ G,
      ActualConclusions h L hW c hm δa δe ω ∧
      BudgetConclusions h L hW c hm δa δe δg δl ω ∧
      PaymentConclusion h L hW c hm δg δl ω := by
  obtain ⟨C,hC,hprob,hgood⟩ := original_gap_main h L hW c hm hL hb ha ha1 he he1
  exact payment_event h L hW c hm hL hs1 true (δa+δe) δa δe C hC hprob hgood hg hl

/-- Unit scales use the confidence cube proved for this same run; the
physical bounds have zero gap and do not assume an E11 event. -/
theorem unit_scale_budget_main (hm : Protocol h L hW c (μ := μ))
    (hK : 2 ≤ K) (hT : 1 ≤ T)
    (hc : c.confidence_scale = 1) (hs : c.radius_scale = 1)
    (hb : ∀ t < T, ∀ ω i j, h.broadcast t ω j - h.broadcast t ω i ≤ W)
    {δc δa δe δg δl : ℝ} (hδc : 0 < δc) (hδc1 : δc ≤ 1)
    (ha : 0 < δa) (ha1 : δa < 1) (he : 0 < δe) (he1 : δe < 1)
    (hg : 0 < δg) (hl : 0 < δl) (hL : L = CNDNet.paperLc (Fin K) T δc) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc+δa+δe+(δg+δl) ∧ ∀ ω ∈ G,
      Conclusions h L hW c hm δa δe false (actualLedger h L hW c hm) ω ∧
      UnitBudgetConclusions h L hW c hm δa δe δg δl ω ∧
      PaymentConclusion h L hW c hm δg δl ω := by
  have hLn : 0 ≤ L := by
    rw [hL]
    exact le_trans zero_le_one (CNDNet.paper_Lc_budget (ι := Fin K) T hδc hδc1).1
  obtain ⟨C,hC,hprob,hgood⟩ := ExponentialFinite.unit_scale_actual_main h L hW c hm
    hK hT hc hs hb hδc hδc1 ha ha1 he he1 hL
  have hzero : ∀ ω ∈ C,
      Conclusions h L hW c hm δa δe false (actualLedger h L hW c hm) ω := by
    intro ω hω
    constructor
    · intro u n hu hn k
      have hi := (hgood ω hω).1 u n hu hn k
      simpa only [Bool.false_eq_true,if_false,add_zero] using hi
    · intro path
      have hp := (hgood ω hω).2 path
      simpa only [Bool.false_eq_true,if_false,add_zero] using hp
  exact payment_event h L hW c hm hLn (by rw [hs]) false (δc+δa+δe) δa δe
    C hC hprob hzero hg hl

end Part2.ExponentialFiniteGap
