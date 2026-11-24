import staging.cnd20261026.«fix-bounded-sg».BoundedConfidence
import staging.cnd20261026.«fix-bounded-sg».BoundedPublic

noncomputable section
open MeasureTheory Finset
open scoped BigOperators

namespace Part2.CNDHorizon.BoundedEvents

variable {K d T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
open CNDProcess CNDHorizon.BoundedPublic

/-- All four simultaneous conclusions refer to one original, computed run. -/
def MainEvent (h : PotentialInputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B)
    (δc δg δl δa δe : ℝ)
    (hm : CNDHorizon.Bounded.Laws
      (concreteMaps (R + M + D) (CNDNet.paperLc (Fin K) T δc) R (B + 2 * D)
        h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B + 2 * D) R) h μ T)
    (ω : Ω) : Prop :=
  let L := CNDNet.paperLc (Fin K) T δc
  let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
  (∀ n ≤ T, ∀ i j : Fin K,
    |(θ i - CNDHorizon.BoundedConfidence.actualCenter d h (public_width_nonneg h hB) L n ω i) -
      (θ j - CNDHorizon.BoundedConfidence.actualCenter d h (public_width_nonneg h hB) L n ω j)| ≤
        CNDHorizon.BoundedConfidence.actualRadius d h (public_width_nonneg h hB) L n ω i j) ∧
  (∀ u n : ℕ, u + n ≤ T → 0 < n →
    CNDPayment.intervalSum
      (CNDPayment.observablePayment m (CNDPayment.actualRadius m (R + M + D) L)) u n ω ≤
    CNDPayment.paymentEnvelope m (CNDInformation.canonicalChart (Fin K))
      (R + M + D) L T u n δg δl ω) ∧
  (∀ u n : ℕ, u + n ≤ T → 0 < n →
    CNDPayment.intervalSum
      (CNDPayment.actualPublicResidual m (actualPublicLoss (d := d) h B L hB)) u n ω ≤
      (B + 2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa))) ∧
  (∀ k : Fin K, ∀ u n : ℕ, u + n ≤ T → 0 < n →
    CNDPayment.intervalSum (CNDPayment.encodingDifference m k) u n ω ≤
      (2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((K : ℝ) * (T : ℝ)^2 / δe)))

/-- Measurable common good event, without a confidence, payment or tail field
in the model. A measurable hull also covers the nonmeasurable CI witness. -/
theorem original_run_main_event
    (h : PotentialInputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B)
    (hK : 2 ≤ K) (hT0 : 1 ≤ T) (hT : T ≤ 2^d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    {δc δg δl δa δe : ℝ} (hδc : 0 < δc) (hδc1 : δc ≤ 1)
    (hδg : 0 < δg) (hδl : 0 < δl)
    (hδa : 0 < δa) (hδa1 : δa < 1) (hδe : 0 < δe) (hδe1 : δe < 1)
    (hm : CNDHorizon.Bounded.Laws
      (concreteMaps (R + M + D) (CNDNet.paperLc (Fin K) T δc) R (B + 2 * D)
        h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B + 2 * D) R) h μ T) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc + δg + δl + δa + δe ∧
      ∀ ω ∈ G, MainEvent (d := d) (T := T) h B hB δc δg δl δa δe hm ω := by
  classical
  let L := CNDNet.paperLc (Fin K) T δc
  let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
  let Bad : Set Ω := {ω |
    (∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      CNDPayment.paymentEnvelope m (CNDInformation.canonicalChart (Fin K))
        (R + M + D) L T u n δg δl ω <
      CNDPayment.intervalSum
        (CNDPayment.observablePayment m (CNDPayment.actualRadius m (R + M + D) L)) u n ω) ∨
    (∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      (B + 2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa)) <
      CNDPayment.intervalSum
        (CNDPayment.actualPublicResidual m (actualPublicLoss (d := d) h B L hB)) u n ω) ∨
    (∃ k : Fin K, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      (2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((K : ℝ) * (T : ℝ)^2 / δe)) <
      CNDPayment.intervalSum (CNDPayment.encodingDifference m k) u n ω)}
  obtain ⟨C, hC, hcover⟩ := CNDHorizon.BoundedConfidence.actual_center_confidence_event d h
    (public_width_nonneg h hB) μ T hT0 hK hδc hδc1 hm
  have hL : 0 ≤ L := le_trans (by norm_num) (CNDNet.paper_Lc_budget (ι := Fin K) T hδc hδc1).1
  have hBad : μ.real Bad ≤ δg + δl + δa + δe :=
    actual_public_payment_encoding_joint_delta h B L hB hL hK hT hc hm
      hδg hδl hδa hδa1 hδe hδe1
  let E := toMeasurable μ (Cᶜ ∪ Bad)
  refine ⟨Eᶜ, (measurableSet_toMeasurable μ _).compl, ?_, ?_⟩
  · have hbound := (measureReal_union_le Cᶜ Bad).trans (add_le_add hC hBad)
    simpa only [E, compl_compl, measureReal_def, measure_toMeasurable, add_assoc]
      using hbound
  · intro ω hω
    have hnot : ω ∉ Cᶜ ∪ Bad := fun hw => hω (subset_toMeasurable μ _ hw)
    have hωC : ω ∈ C := by
      by_contra hw
      exact hnot (Or.inl hw)
    have hωB : ω ∉ Bad := fun hw => hnot (Or.inr hw)
    refine ⟨hcover ω hωC, ?_, ?_, ?_⟩
    · intro u n hu hn
      exact le_of_not_gt fun hb => hωB (Or.inl ⟨u,n,hu,hn,hb⟩)
    · intro u n hu hn
      exact le_of_not_gt fun hb => hωB (Or.inr (Or.inl ⟨u,n,hu,hn,hb⟩))
    · intro k u n hu hn
      exact le_of_not_gt fun hb => hωB (Or.inr (Or.inr ⟨k,u,n,hu,hn,hb⟩))

end Part2.CNDHorizon.BoundedEvents
