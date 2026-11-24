import staging.cnd20261026.«fix-bounded-sg».ExponentialSGPhysical
import staging.cnd20261026.«fix-bounded-sg».ExponentialScaledRadius

/-! The actual SG exponential intervals, post-hoc switching paths and the
same-p canonical private payment envelope share one event. The gap ledger
is retained separately; no small-gap or confidence-success premise is used. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory NNReal

namespace Part2.ExponentialSGPayment
variable {Ω ι E : Type*} [m₀ : MeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype E] [DecidableEq E] [Nonempty E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}
variable (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
  (a : ℕ → ι → Ω → ℝ) (r : ℕ → ι → ι → Ω → ℝ)
  (v : ExponentialComposition.Trajectory E ι Ω)

theorem payment_eq_observable (t : ℕ) (ω : Ω) :
    ExponentialPhysical.payment h.toM1Model r t ω =
      CNDPayment.observablePayment h.toM1Model r t ω := rfl

theorem actual_e12_e13_with_gap_and_budget
    (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    {T : ℕ} {W : ℝ} (hv : ExponentialComposition.Laws h.toM1Model a r v T W)
    (hW : 0 ≤ W)
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j))
    (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hrle : ∀ t i j ω, r t i j ω ≤ CNDPayment.actualRadius h.toM1Model H L t i j ω)
    {δa δn δg δl : ℝ} (hδa : 0 < δa) (hδa1 : δa < 1)
    (hδn : 0 < δn) (hδn1 : δn < 1) (hδg : 0 < δg) (hδl : 0 < δl) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δa+δn+(δg+δl) ∧ ∀ ω ∈ G,
      ExponentialSGPhysical.intervalConclusion h a r v ν T W δa δn ω ∧
      ExponentialSGPhysical.pathConclusion h a r v ν T W δa δn ω ∧
      (∀ u n, u+n ≤ T → 0 < n →
        CNDPayment.intervalSum (ExponentialPhysical.payment h.toM1Model r) u n ω ≤
          CNDPayment.paymentEnvelope h.toM1Model (CNDInformation.canonicalChart ι)
            H L T u n δg δl ω) := by
  classical
  obtain ⟨C,hC,hprob,hgood⟩ := ExponentialSGPhysical.actual_e12_e13_with_gap
    h a r v ν hν hv hW ha hr hδa hδa1 hδn hδn1
  let Bad : Set Ω := {ω | ∃ u n, u+n ≤ T ∧ 0 < n ∧
    CNDPayment.paymentEnvelope h.toM1Model (CNDInformation.canonicalChart ι) H L T u n δg δl ω <
      CNDPayment.intervalSum (CNDPayment.observablePayment h.toM1Model r) u n ω}
  have hBad : μ.real Bad ≤ δg+δl :=
    ExponentialScaledRadius.dominatedPayment_envelope_delta h.toM1Model r H L hH hL hrle T hδg hδl
  let B := toMeasurable μ (Cᶜ ∪ Bad)
  refine ⟨Bᶜ, (measurableSet_toMeasurable μ _).compl, ?_, ?_⟩
  · have hb := (measureReal_union_le Cᶜ Bad).trans (add_le_add hprob hBad)
    simpa only [B, compl_compl, measureReal_def, measure_toMeasurable] using hb
  · intro ω hω
    have hb : ω ∉ Cᶜ ∪ Bad := fun hw => hω (subset_toMeasurable μ _ hw)
    have hc : ω ∈ C := by by_contra hw; exact hb (Or.inl hw)
    refine ⟨(hgood ω hc).1, (hgood ω hc).2, ?_⟩
    intro u n hu hn
    have hp : CNDPayment.intervalSum (CNDPayment.observablePayment h.toM1Model r) u n ω ≤
        CNDPayment.paymentEnvelope h.toM1Model (CNDInformation.canonicalChart ι) H L T u n δg δl ω :=
      le_of_not_gt (fun hx => hb (Or.inr ⟨u,n,hu,hn,hx⟩))
    simpa only [CNDPayment.intervalSum, payment_eq_observable] using hp

end Part2.ExponentialSGPayment
