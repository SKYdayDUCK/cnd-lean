import staging.cnd20261026.«fix-bounded-sg».SGPublic
import staging.cnd20261025.sg.NoiseEvents

noncomputable section
open MeasureTheory Finset
open scoped BigOperators NNReal

namespace Part2.CNDHorizon.SGMain

variable {K d T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {σ σe : ℝ}
variable (ν : ℝ≥0)
open CNDProcess CNDProcess.SG CNDSGMain

/-- All four simultaneous conclusions refer to one original, computed run. -/
def MainEvent (h : Inputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B)
    (δc δg δl δa δn : ℝ)
    (hm : CNDHorizon.SG.Laws
      (maps (K := K) ν (CNDNet.paperLc (Fin K) T δc) R M (B + 2 * D)
        h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B + 2 * D) R) h μ σ σe T)
    (ω : Ω) : Prop :=
  let L := CNDNet.paperLc (Fin K) T δc
  let m := shadow ν h B (CNDNet.paperLc (Fin K) T δc) hB hm
  (∀ n ≤ T, ∀ i j : Fin K,
    |(θ i - center (d := d) h ν L (public_width_nonneg h hB) n ω i) -
      (θ j - center (d := d) h ν L (public_width_nonneg h hB) n ω j)| ≤
        radius (d := d) h ν L (public_width_nonneg h hB) n ω i j) ∧
  (∀ u n : ℕ, u + n ≤ T → 0 < n →
    CNDPayment.intervalSum
      (CNDPayment.observablePayment m (CNDPayment.actualRadius m (R + M + (ν : ℝ)) (4*L))) u n ω ≤
    CNDPayment.paymentEnvelope m (CNDInformation.canonicalChart (Fin K))
      (R + M + (ν : ℝ)) (4*L) T u n δg δl ω) ∧
  (∀ u n : ℕ, u + n ≤ T → 0 < n →
    CNDPayment.intervalSum
      (CNDPayment.actualPublicResidual m (actualPublicLoss (d := d) ν h B L hB)) u n ω ≤
      (B + 2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa))) ∧
  (∀ k : Fin K, ∀ u n : ℕ, u + n ≤ T → 0 < n →
    CNDPayment.intervalSum (noiseDifference (CNDHorizon.SG.actualModel h ν L (B+2*D) (public_width_nonneg h hB) hm) k) u n ω ≤
      (2 * (ν : ℝ)) * Real.sqrt (2 * (n : ℝ) * Real.log ((K : ℝ) * (T : ℝ)^2 / δn)))

/-- Measurable common good event, without a confidence, payment or tail field
in the model. A measurable hull also covers the nonmeasurable CI witness. -/
theorem original_run_main_event (hν : (ν:ℝ)^2=σ^2+σe^2)
    (h : Inputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B)
    (hK : 2 ≤ K) (hT0 : 1 ≤ T) (hT : T ≤ 2^d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    {δc δg δl δa δn : ℝ} (hδc : 0 < δc) (hδc1 : δc ≤ 1)
    (hδg : 0 < δg) (hδl : 0 < δl)
    (hδa : 0 < δa) (hδa1 : δa < 1) (hδn : 0 < δn) (hδn1 : δn < 1)
    (hm : CNDHorizon.SG.Laws
      (maps (K := K) ν (CNDNet.paperLc (Fin K) T δc) R M (B + 2 * D)
        h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B + 2 * D) R) h μ σ σe T) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc + δg + δl + δa + δn ∧
      ∀ ω ∈ G, MainEvent (d := d) (T := T) ν h B hB δc δg δl δa δn hm ω := by
  classical
  let L := CNDNet.paperLc (Fin K) T δc
  let m := shadow ν h B (CNDNet.paperLc (Fin K) T δc) hB hm
  let Bad : Set Ω := {ω |
    (∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      CNDPayment.paymentEnvelope m (CNDInformation.canonicalChart (Fin K))
        (R + M + (ν : ℝ)) (4*L) T u n δg δl ω <
      CNDPayment.intervalSum
        (CNDPayment.observablePayment m (CNDPayment.actualRadius m (R + M + (ν : ℝ)) (4*L))) u n ω) ∨
    (∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      (B + 2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa)) <
      CNDPayment.intervalSum
        (CNDPayment.actualPublicResidual m (actualPublicLoss (d := d) ν h B L hB)) u n ω) ∨
    (∃ k : Fin K, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      (2 * (ν : ℝ)) * Real.sqrt (2 * (n : ℝ) * Real.log ((K : ℝ) * (T : ℝ)^2 / δn)) <
      CNDPayment.intervalSum (noiseDifference (CNDHorizon.SG.actualModel h ν L (B+2*D) (public_width_nonneg h hB) hm) k) u n ω)}
  obtain ⟨C, hC, hcover⟩ := center_confidence_event (d := d) h ν hν
    (public_width_nonneg h hB) T hT0 hK hδc hδc1 hm
  have hL : 0 ≤ L := le_trans (by norm_num) (CNDNet.paper_Lc_budget (ι := Fin K) T hδc hδc1).1
  have hBad : μ.real Bad ≤ δg + δl + δa + δn := by
    have hp := payment_all_intervals_delta ν h B L hB hL T hm hδg hδl
    have ha := public_all_intervals_delta ν h B L hB hL hK hT hc hm hδa hδa1
    have hn := noise_all_intervals_delta
      (CNDHorizon.SG.actualModel h ν L (B+2*D) (public_width_nonneg h hB) hm) ν hν T hδn hδn1
    have hs := (measureReal_union_le _ _).trans
      (add_le_add hp ((measureReal_union_le _ _).trans (add_le_add ha hn)))
    simpa only [Bad,Fintype.card_fin,add_assoc] using hs
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

end Part2.CNDHorizon.SGMain
