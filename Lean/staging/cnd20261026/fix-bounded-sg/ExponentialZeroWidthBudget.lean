import staging.cnd20261026.«fix-bounded-sg».ExponentialZeroWidth

/-! When the proxy loss has zero range, the action bound vanishes. These
corollaries charge only the encoding or noise failure budget. -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators ProbabilityTheory NNReal

namespace Part2.ExponentialZeroWidthBudget
open CNDProcess CNDHorizon ExponentialZeroWidth

private theorem event_without_slack {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : Ω → Prop) (δ : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ G : Set Ω,
      MeasurableSet G ∧ μ.real Gᶜ ≤ δ + ε ∧ ∀ ω ∈ G, P ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δ ∧ ∀ ω ∈ G, P ω := by
  classical
  let bad : Set Ω := {ω | ¬P ω}
  have hbad : μ.real bad ≤ δ := by
    by_contra! hlt
    let ε := min ((μ.real bad - δ) / 2) (1 / 2)
    have hε : 0 < ε := lt_min (by linarith) (by norm_num)
    have hε₁ : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
    obtain ⟨G, _, hfail, hP⟩ := h ε hε hε₁
    have hsub : bad ⊆ Gᶜ := fun ω hb hg => hb (hP ω hg)
    have hle := (measureReal_mono (μ := μ) hsub).trans hfail
    have hε₂ : ε ≤ (μ.real bad - δ) / 2 := min_le_left _ _
    linarith
  refine ⟨(toMeasurable μ bad)ᶜ, (measurableSet_toMeasurable μ _).compl, ?_, ?_⟩
  · simpa only [compl_compl, measureReal_def, measure_toMeasurable] using hbad
  · intro ω hω
    by_contra hp
    exact hω (subset_toMeasurable μ bad hp)

variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}
  {θ : Fin K → ℝ} {R M D : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]

section CommonEvents
variable (H L cs rs : ℝ) (hR : 0 ≤ R) (d : ExpertData (Fin K) E)
  (prior : E → ℝ) (f : Feedback (ι := Fin K) ℱ)

theorem bounded_common_event_with_gap
    (m : CNDProbability.M1Model ℱ μ θ R M D)
    (hm : Bridge H L R cs rs hR d prior f m T)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hrs : 0 ≤ rs)
    (hb : ∀ t < T, ∀ ω i j, f.broadcast t ω j - f.broadcast t ω i ≤ 0)
    {δe : ℝ} (hδe : 0 < δe) (hδe₁ : δe < 1) :
    let a := center H L R cs rs hR d prior f T
    let r := radius H L R cs rs hR d prior f T
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δe ∧ ∀ ω ∈ G,
      ExponentialPhysical.Event m a (ExponentialGap.analysisRadius (θ := θ) a r) 0 T 0 δe ω ∧
      (∀ u n, u + n ≤ T → 0 < n → ∀ k : Fin K,
        CNDPayment.intervalSum (fun t ω => ExponentialPhysical.physical m t (m.action t ω) ω -
          ExponentialPhysical.physical m t k ω) u n ω ≤
        ExponentialPhysical.encodingBound (ι := Fin K) (D := D) T n δe +
          CNDPayment.intervalSum (ExponentialPhysical.payment m r) u n ω +
          ExponentialGap.gapLedger (θ := θ) a r u n ω) := by
  dsimp only
  apply event_without_slack
  intro ε hε hε₁
  obtain ⟨G, hG, hfail, hgood⟩ := ExponentialZeroWidth.common_event_with_gap
    H L R cs rs hR d prior f m hm hH hL hrs hb hε hε₁ hδe hδe₁
  refine ⟨G, hG, by linarith, ?_⟩
  intro ω hω
  obtain ⟨hevent, hinterval⟩ := hgood ω hω
  refine ⟨?_, hinterval⟩
  simpa only [ExponentialPhysical.Event, ExponentialPhysical.actionBound, zero_mul] using hevent

theorem sg_common_event_with_gap {σ σe : ℝ}
    (s : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (hs : Bridge H L R cs rs hR d prior f s.toM1Model T)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hrs : 0 ≤ rs)
    (hb : ∀ t < T, ∀ ω i j, f.broadcast t ω j - f.broadcast t ω i ≤ 0)
    (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    {δn : ℝ} (hδn : 0 < δn) (hδn₁ : δn < 1) :
    let a := center H L R cs rs hR d prior f T
    let r := radius H L R cs rs hR d prior f T
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δn ∧ ∀ ω ∈ G,
      ExponentialSGPhysical.Event s a (ExponentialGap.analysisRadius (θ := θ) a r) ν 0 T 0 δn ω ∧
      (∀ u n, u + n ≤ T → 0 < n → ∀ k : Fin K,
        CNDPayment.intervalSum (fun t ω => ExponentialSGPhysical.physical s t (s.action t ω) ω -
          ExponentialSGPhysical.physical s t k ω) u n ω ≤
        ExponentialSGPhysical.noiseBound (ι := Fin K) ν T n δn +
          CNDPayment.intervalSum (ExponentialPhysical.payment s.toM1Model r) u n ω +
          ExponentialGap.gapLedger (θ := θ) a r u n ω) := by
  dsimp only
  apply event_without_slack
  intro ε hε hε₁
  obtain ⟨G, hG, hfail, hgood⟩ := ExponentialZeroWidth.sg_common_event_with_gap
    H L R cs rs hR d prior f s hs hH hL hrs hb ν hν hε hε₁ hδn hδn₁
  refine ⟨G, hG, by linarith, ?_⟩
  intro ω hω
  obtain ⟨hevent, hinterval⟩ := hgood ω hω
  refine ⟨?_, hinterval⟩
  simpa only [ExponentialSGPhysical.Event, ExponentialPhysical.actionBound, zero_mul] using hevent
end CommonEvents

open ExponentialSGFinite in
/-- The finite SG zero-width conclusion holds on one event of failure
probability at most the noise budget alone. -/
theorem sg_actual_zero_width_main {W σ σe : ℝ}
    (h : SGInputs ℱ θ R M D T) (ν : ℝ≥0) (L : ℝ) (hW : 0 ≤ W)
    (c : ExponentialGeometry.Config (K := K) (E := E) T R W)
    (hm : Protocol h ν L hW c (μ := μ) (σ := σ) (σe := σe))
    (hν : (ν : ℝ)^2 = σ^2 + σe^2) (hL : 0 ≤ L) (hw0 : W = 0) (hT : 0 < T)
    (hb : ∀ t < T, ∀ ω i j, h.broadcast t ω j - h.broadcast t ω i ≤ W)
    {δn : ℝ} (hδn : 0 < δn) (hδn₁ : δn < 1) :
    let m := model h ν L hW c hm
    let a := ExponentialSGFinite.center h ν L hW c
    let r := ExponentialSGFinite.radius h ν L hW c
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δn ∧ ∀ ω ∈ G,
      (∀ u n, u + n ≤ T → 0 < n → ∀ k,
        CNDPayment.intervalSum (fun t ω => ExponentialSGPhysical.physical m t (m.action t ω) ω -
          ExponentialSGPhysical.physical m t k ω) u n ω ≤
        ExponentialSGPhysical.noiseBound (ι := Fin K) ν T n δn +
          CNDPayment.intervalSum (ExponentialPhysical.payment m.toM1Model r) u n ω +
          ExponentialGap.gapLedger (θ := θ) a r u n ω) ∧
      (∀ path : ℕ → Fin K,
        (∑ t ∈ range T, (ExponentialSGPhysical.physical m t (m.action t ω) ω -
          ExponentialSGPhysical.physical m t (path t) ω)) ≤
        ExponentialSGPhysical.noiseCoefficient (ι := Fin K) ν 0 T 0 δn *
          Real.sqrt ((T : ℝ) * ((ExponentialComposition.switchCount T path + 1 : ℕ) : ℝ)) +
          CNDPayment.intervalSum (ExponentialPhysical.payment m.toM1Model r) 0 T ω +
          ExponentialGap.gapLedger (θ := θ) a r 0 T ω) := by
  dsimp only
  apply event_without_slack
  intro ε hε hε₁
  obtain ⟨G, hG, hfail, hgood⟩ := ExponentialSGFinite.actual_zero_width_main
    h ν L hW c hm hν hL hw0 hT hb hε hε₁ hδn hδn₁
  refine ⟨G, hG, by linarith, ?_⟩
  intro ω hω
  simpa only [ExponentialSGPhysical.noiseCoefficient, zero_mul, zero_add] using hgood ω hω

end Part2.ExponentialZeroWidthBudget
