import staging.cnd20261024.payment.PaymentMinimum
import staging.cnd20261024.payment.IntervalNoiseTails
import staging.cnd20261024.process.RadiusHistory
import TangentChart

noncomputable section
open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators
set_option maxHeartbeats 800000

namespace Part2.CNDPayment
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}
variable (h : CNDProbability.M1Model ℱ μ θ R M D)

/-- Original radius predictability follows from the actual inverse-information
map and the original predictable p; it is not a model field. -/
theorem actualRadius_measurable (H L : ℝ) (t : ℕ) (i j : ι) :
    Measurable[ℱ t] (actualRadius h H L t i j) :=
  CNDProcess.actualSaturatedRadius_history_measurable ℱ h.p h.p_measurable t H L R i j

theorem canonicalPayment_global_delta
    (H Lc : ℝ) (hH : 0 ≤ H) (hLc : 0 ≤ Lc) (T : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | 4 * actualQ h (CNDInformation.canonicalChart ι) H Lc 0 T ω +
      (4 * R / CNDPhysical.c0) * Real.log (1 / δ) <
      intervalSum (observablePayment h (actualRadius h H Lc)) 0 T ω} ≤ δ :=
  actualPayment_global_delta h _ CNDInformation.canonicalChart_is_tangentChart H Lc hH hLc
    (actualRadius_measurable h H Lc) T hδ

theorem canonicalPayment_all_intervals_delta
    (H Lc : ℝ) (hH : 0 ≤ H) (hLc : 0 ≤ Lc) (T : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      4 * actualQ h (CNDInformation.canonicalChart ι) H Lc u n ω +
      (4 * R / CNDPhysical.c0) * Real.log ((T : ℝ) ^ 2 / δ) <
      intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} ≤ δ :=
  actualPayment_all_intervals_delta h _ CNDInformation.canonicalChart_is_tangentChart H Lc hH hLc
    (actualRadius_measurable h H Lc) T hδ

/-- Full original observable-payment statement (8), including the global
minimum term, for the actual saturated radius on the actual M1 sample space. -/
theorem canonicalPayment_envelope_delta
    (H Lc : ℝ) (hH : 0 ≤ H) (hLc : 0 ≤ Lc)
    (T : ℕ) {δg δl : ℝ} (hδg : 0 < δg) (hδl : 0 < δl) :
    μ.real {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      paymentEnvelope h (CNDInformation.canonicalChart ι) H Lc T u n δg δl ω <
        intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} ≤ δg + δl :=
  actualPayment_envelope_delta h _ CNDInformation.canonicalChart_is_tangentChart H Lc hH hLc
    (actualRadius_measurable h H Lc) T hδg hδl

/-- The three probability blocks are intersected only after concentration.
Their noises may be dependent, and no confidence-success event changes μ. -/
theorem payment_public_encoding_joint_delta [Nonempty ι]
    (l : ℕ → ι → Ω → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hlm : ∀ t i, Measurable[h.encoded t] (l t i))
    (hspan : ∀ t ω i j, 0 < h.p t i ω → 0 < h.p t j ω → |l t i ω - l t j ω| ≤ 2 * W)
    (H Lc : ℝ) (hH : 0 ≤ H) (hLc : 0 ≤ Lc) (T : ℕ)
    {δg δl δa δe : ℝ} (hδg : 0 < δg) (hδl : 0 < δl)
    (hδa0 : 0 < δa) (hδa1 : δa < 1) (hδe0 : 0 < δe) (hδe1 : δe < 1) :
    μ.real {ω |
      (∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
        paymentEnvelope h (CNDInformation.canonicalChart ι) H Lc T u n δg δl ω <
          intervalSum (observablePayment h (actualRadius h H Lc)) u n ω) ∨
      (∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
        W * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ) ^ 2 / δa)) <
          intervalSum (actualPublicResidual h l) u n ω) ∨
      (∃ k : ι, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
        (2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((Fintype.card ι : ℝ) * (T : ℝ) ^ 2 / δe)) <
          intervalSum (encodingDifference h k) u n ω)} ≤ δg + δl + δa + δe := by
  have hp := canonicalPayment_envelope_delta h H Lc hH hLc T hδg hδl
  have ha := public_all_intervals_delta h l hW hlm hspan T hδa0 hδa1
  have he := encoding_all_intervals_delta h T hδe0 hδe1
  apply (measureReal_union_le _ _).trans
  have htail := add_le_add hp ((measureReal_union_le _ _).trans (add_le_add ha he))
  simpa only [add_assoc] using htail

end Part2.CNDPayment
