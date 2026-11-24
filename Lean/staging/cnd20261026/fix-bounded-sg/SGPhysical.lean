import staging.cnd20261026.«fix-bounded-sg».SGPublic
import staging.cnd20261025.sg.NoiseEvents
import CNDPhysicalRegret

/-! Pointwise and interval conversion on the actual original CND run.
Coverage is an explicit eventwise input only to these deterministic helpers;
the final original-space probability assembly supplies it from ConfidenceBridge. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory NNReal
set_option maxHeartbeats 1200000

namespace Part2.CNDHorizon.SGMain
open CNDProcess CNDProcess.SG CNDSGMain
variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {σ σe : ℝ}

variable (ν : ℝ≥0) (h : Inputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B)
  (hm : CNDHorizon.SG.Laws
    (maps (K := K) ν L R M (B + 2 * D) h.R_nonneg (public_width_nonneg h hB))
    (treeData d K (B + 2 * D) R) h μ σ σe T)

/-- The finite physical-conversion surrogate is exactly the actual public
loss computed by the concrete recursive run, including its moving gauge. -/
theorem actual_surrogate_eq_loss (t : ℕ) (ht : t<T) (ω : Ω) (i : Fin K) :
    let m := shadow ν h B L hB hm
    CNDPhysicalRegret.surrogate
      (center (d := d) h ν L (public_width_nonneg h hB) t ω)
      (fun j => m.p t j ω) (fun j => h.publicCost t j ω) (fun j => h.error t j ω)
      (radius (d := d) h ν L (public_width_nonneg h hB) t ω) i =
      actualPublicLoss (d := d) ν h B L hB t i ω := by
  dsimp only
  simp only [shadow,CNDHorizon.SG.actualModel,CNDHorizon.SG.model,CNDHorizon.SG.publicShadow,
    Primitive.stopped,CNDHorizon.SG.primitive,stopP,if_pos ht]

  let o := concreteMaps (K := K) (R + M + (ν : ℝ)) (4*L) R (B + 2 * D) h.R_nonneg (public_width_nonneg h hB)
  let a := treeData d K (B + 2 * D) R
  let s := run o a h.feedback t ω
  change (confidence o a s i - (∑ j, probability o a t s j * confidence o a s j) -
      (∑ j, probability o a t s j * CNDProcess.radius o a s i j)) +
      (h.publicCost t i ω + h.error t i ω) =
    (confidence o a s i - (∑ j, CNDProcess.radius o a s i j * probability o a t s j) -
      (∑ j, probability o a t s j * confidence o a s j)) +
      (h.publicCost t i ω + h.error t i ω)
  have he : (∑ j, CNDProcess.radius o a s i j * probability o a t s j) =
      ∑ j, probability o a t s j * CNDProcess.radius o a s i j :=
    sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he]
  ring

/-- The selected finite-conversion payment uses the same original saturated
radius and computed p as the unconditional payment concentration theorem. -/
theorem actual_payment_eq_observable (t : ℕ) (ht : t<T) (ω : Ω) :
    let m := shadow ν h B L hB hm
    CNDPhysicalRegret.payment
      (radius (d := d) h ν L (public_width_nonneg h hB) t ω)
      (fun j => m.p t j ω) (h.action t ω) =
    CNDPayment.observablePayment m (CNDPayment.actualRadius m (R + M + (ν : ℝ)) (4*L)) t ω := by
  dsimp only
  rw [radius_eq_model h ν L (public_width_nonneg h hB) hm t (Nat.le_of_lt ht) ω]
  simp only [CNDPayment.observablePayment,shadow,CNDHorizon.SG.actualModel,CNDHorizon.SG.model,
    CNDHorizon.SG.publicShadow,Primitive.stopped,CNDHorizon.SG.primitive,stop,if_pos ht]
  rfl

/-- Original one-step physical regret is bounded by the actual proxy regret,
actual public sampling residual, observable payment, and encoding difference.
No target decomposition or private-deficit bound is assumed. -/
theorem actual_physical_step_le (t : ℕ) (ht : t<T) (ω : Ω) (k : Fin K)
    (hcover : ∀ i j,
      |(θ i - center (d := d) h ν L (public_width_nonneg h hB) t ω i) -
        (θ j - center (d := d) h ν L (public_width_nonneg h hB) t ω j)| ≤
      radius (d := d) h ν L (public_width_nonneg h hB) t ω i j) :
    let m := shadow ν h B L hB hm
    h.physical t (h.action t ω) ω - h.physical t k ω ≤
      ((∑ j, m.p t j ω * actualPublicLoss (d := d) ν h B L hB t j ω) -
        actualPublicLoss (d := d) ν h B L hB t k ω) +
      CNDPayment.actualPublicResidual m (actualPublicLoss (d := d) ν h B L hB) t ω +
      CNDPayment.observablePayment m (CNDPayment.actualRadius m (R + M + (ν : ℝ)) (4*L)) t ω +
      noiseDifference (CNDHorizon.SG.actualModel h ν L (B+2*D) (public_width_nonneg h hB) hm) k t ω := by
  let m := shadow ν h B L hB hm
  let c := center (d := d) h ν L (public_width_nonneg h hB) t ω
  let r := radius (d := d) h ν L (public_width_nonneg h hB) t ω
  let p := fun j => m.p t j ω
  have hc : ∀ i j, |(θ i - θ j) - (c i - c j)| ≤ r i j := by
    intro i j
    convert hcover i j using 1 <;> congr 1 <;> ring
  have hi := (CNDPhysicalRegret.confidence_controls_actual_deficit θ c p r
    (fun j => m.p_nonneg t ω j) (m.p_sum t ω) hc (h.action t ω)).2
  have hk := (CNDPhysicalRegret.confidence_controls_actual_deficit θ c p r
    (fun j => m.p_nonneg t ω j) (m.p_sum t ω) hc k).1
  have hid := CNDPhysicalRegret.physical_identity θ c p
    (fun j => h.publicCost t j ω) (fun j => h.error t j ω) (fun j => h.noise t ω j) r
    (h.drift t ω) (h.action t ω) k
  have heq (i : Fin K) : CNDPhysicalRegret.surrogate c p
      (fun j => h.publicCost t j ω) (fun j => h.error t j ω) r i =
      actualPublicLoss (d := d) ν h B L hB t i ω := actual_surrogate_eq_loss ν h B L hB hm t ht ω i
  simp_rw [heq] at hid
  have hpayment := actual_payment_eq_observable ν h B L hB hm t ht ω
  change CNDPhysicalRegret.payment r p (h.action t ω) = _ at hpayment
  rw [hpayment] at hi
  change h.publicCost t (h.action t ω) ω + θ (h.action t ω) + h.drift t ω + h.noise t ω (h.action t ω) -
    (h.publicCost t k ω + θ k + h.drift t ω + h.noise t ω k) ≤ _
  simp only [CNDPhysicalRegret.physical, CNDPhysicalRegret.avg, add_zero] at hid
  simp only [CNDPayment.actualPublicResidual,noiseDifference,CNDProbability.SGModel.combinedNoise,shadow,CNDHorizon.SG.actualModel,
    CNDHorizon.SG.model,CNDHorizon.SG.publicShadow,Primitive.stopped,CNDHorizon.SG.primitive,stop,if_pos ht]
  change _ ≤ ((∑ j, p j * actualPublicLoss (d := d) ν h B L hB t j ω) -
    actualPublicLoss (d := d) ν h B L hB t k ω) +
    (actualPublicLoss (d := d) ν h B L hB t (h.action t ω) ω -
      ∑ j, p j * actualPublicLoss (d := d) ν h B L hB t j ω) +
    CNDPayment.observablePayment m (CNDPayment.actualRadius m (R + M + (ν : ℝ)) (4*L)) t ω +
    ((h.noise t ω (h.action t ω)-h.error t (h.action t ω) ω)-(h.noise t ω k-h.error t k ω))
  linarith

theorem actual_proxy_interval_le (hL : 0 ≤ L) (hK : 2 ≤ K) (hT : T ≤ 2 ^ d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    (u n : ℕ) (hu : u + n ≤ T) (k : Fin K) (ω : Ω) :
    let m := shadow ν h B L hB hm
    (∑ t ∈ Ico u (u + n),
      ((∑ j, m.p t j ω * actualPublicLoss (d := d) ν h B L hB t j ω) -
        actualPublicLoss (d := d) ν h B L hB t k ω)) ≤
      32 * (B + 2 * D) * Real.sqrt ((n : ℝ) * CNDProd.logExperts d K) := by
  dsimp only
  have he : (∑ t ∈ Ico u (u+n), ((∑ j, (shadow ν h B L hB hm).p t j ω *
      actualPublicLoss (d:=d) ν h B L hB t j ω) - actualPublicLoss (d:=d) ν h B L hB t k ω)) =
      ∑ t ∈ Ico u (u+n), ((∑ j, runProbability
        (maps ν L R M (B+2*D) h.R_nonneg (public_width_nonneg h hB))
        (treeData d K (B+2*D) R) h.feedback t j ω * actualPublicLoss (d:=d) ν h B L hB t j ω) -
        actualPublicLoss (d:=d) ν h B L hB t k ω) := by
    apply sum_congr rfl
    intro t ht
    have htT : t<T := lt_of_lt_of_le (mem_Ico.mp ht).2 hu
    simp only [shadow,CNDHorizon.SG.actualModel,CNDHorizon.SG.model,CNDHorizon.SG.publicShadow,
      Primitive.stopped,CNDHorizon.SG.primitive,stopP,if_pos htT]
  rw [he]
  have hb : ∀ t < T, ∀ i j, h.broadcast t ω j - h.broadcast t ω i ≤ B + 2 * D :=
    fun t ht i j => actual_broadcast_span h B hc ht ω i j
  have hH : 0 ≤ R + M + (ν:ℝ) := by linarith [h.R_nonneg, h.M_nonneg, ν.coe_nonneg]
  by_cases hz : B + 2 * D = 0
  · have hzbound := actual_zero_width_proxy_interval (d := d) (T := T)
      (R + M + (ν : ℝ)) (4*L) R hH (by positivity) h.R_nonneg h.feedback ω
      (by simpa only [hz] using hb) u (u+n) hu k
    simpa only [actualPublicLoss, maps, hz, zero_mul, mul_zero, shadow, CNDHorizon.SG.actualModel,
      CNDHorizon.SG.model, CNDHorizon.SG.publicShadow, Inputs.feedback] using hzbound
  · have ht := actual_proxy_interval hK hT (R + M + (ν : ℝ)) (4*L) R (B + 2 * D)
      hH (by positivity) h.R_nonneg (lt_of_le_of_ne (public_width_nonneg h hB) (Ne.symm hz))
      h.feedback ω hb u (u+n) (Nat.le_add_right u n) hu k
    simpa only [actualPublicLoss, Nat.add_sub_cancel_left, shadow, CNDHorizon.SG.actualModel, CNDHorizon.SG.model, CNDHorizon.SG.publicShadow] using ht

theorem sum_Ico_eq_intervalSum (X : ℕ → Ω → ℝ) (u n : ℕ) (ω : Ω) :
    (∑ t ∈ Ico u (u+n), X t ω) = CNDPayment.intervalSum X u n ω := by
  rw [sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left, CNDPayment.intervalSum]

/-- Actual bounded original-run Ico regret, with the original deterministic
32W proxy term and the three actual bounded probability-ledger sums. -/
theorem actual_physical_interval_le (hL : 0 ≤ L) (hK : 2 ≤ K) (hT : T ≤ 2 ^ d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    (u n : ℕ) (hu : u + n ≤ T) (k : Fin K) (ω : Ω)
    (hcover : ∀ t < T, ∀ i j,
      |(θ i - center (d := d) h ν L (public_width_nonneg h hB) t ω i) -
        (θ j - center (d := d) h ν L (public_width_nonneg h hB) t ω j)| ≤
      radius (d := d) h ν L (public_width_nonneg h hB) t ω i j) :
    let m := shadow ν h B L hB hm
    (∑ t ∈ Ico u (u+n), (h.physical t (h.action t ω) ω - h.physical t k ω)) ≤
      32 * (B + 2 * D) * Real.sqrt ((n : ℝ) * CNDProd.logExperts d K) +
      CNDPayment.intervalSum (CNDPayment.actualPublicResidual m (actualPublicLoss (d := d) ν h B L hB)) u n ω +
      CNDPayment.intervalSum (CNDPayment.observablePayment m (CNDPayment.actualRadius m (R + M + (ν : ℝ)) (4*L))) u n ω +
      CNDPayment.intervalSum (noiseDifference (CNDHorizon.SG.actualModel h ν L (B+2*D) (public_width_nonneg h hB) hm) k) u n ω := by
  let m := shadow ν h B L hB hm
  have hs := sum_le_sum (s := Ico u (u+n)) (fun t ht =>
    actual_physical_step_le ν h B L hB hm t (lt_of_lt_of_le (mem_Ico.mp ht).2 hu) ω k
      (hcover t (lt_of_lt_of_le (mem_Ico.mp ht).2 hu)))
  simp only [sum_add_distrib] at hs
  have hp := actual_proxy_interval_le ν h B L hB hm hL hK hT hc u n hu k ω
  rw [sum_Ico_eq_intervalSum, sum_Ico_eq_intervalSum, sum_Ico_eq_intervalSum] at hs
  linarith

end Part2.CNDHorizon.SGMain
