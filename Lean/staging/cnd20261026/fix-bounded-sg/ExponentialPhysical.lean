import staging.cnd20261024.payment.IntervalNoiseTails
import CNDPhysicalRegret
import Part2.Intervals

/-! Conditional E11--E13 bridge, independent of the expert update rule.
The input expert bound is deterministic E10, not a concentration assumption.
M1 supplies the feedback timing, predictable probabilities and encoder laws.
No claim is made here that the frozen exponential recursion instantiates M1,
or that its searched private radii satisfy E11. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 1200000

namespace Part2.ExponentialPhysical
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}
variable (h : CNDProbability.M1Model ℱ μ θ R M D)
  (a : ℕ → ι → Ω → ℝ) (r : ℕ → ι → ι → Ω → ℝ)

def loss (t : ℕ) (i : ι) (ω : Ω) : ℝ :=
  CNDPhysicalRegret.surrogate (fun j => a t j ω) (fun j => h.p t j ω)
    (fun j => h.publicCost t j ω) (fun j => h.error t j ω) (fun i j => r t i j ω) i

def physical (t : ℕ) (i : ι) (ω : Ω) : ℝ :=
  h.publicCost t i ω + θ i + h.drift t ω

def proxyRegret (k : ι) (t : ℕ) (ω : Ω) : ℝ :=
  (∑ j, h.p t j ω * loss h a r t j ω) - loss h a r t k ω

def payment (t : ℕ) (ω : Ω) : ℝ :=
  CNDPhysicalRegret.payment (fun i j => r t i j ω)
    (fun j => h.p t j ω) (h.action t ω)

def Covers (T : ℕ) (ω : Ω) : Prop := ∀ t < T, ∀ i j,
  |(θ i - θ j) - (a t i ω - a t j ω)| ≤ r t i j ω

/-- The transport interface needed upstream of E10: conservation and
nonincreasing transported comparator losses suffice, independently of Prod. -/
theorem proxyRegret_le_transported (t : ℕ) (ω : Ω) (k : ι)
    (q : ι → ℝ) (transport : ι → ι → ℝ)
    (hcons : ∀ j, (∑ i, q i * transport i j) = h.p t j ω)
    (hdom : CNDPhysicalRegret.transported transport (fun i => loss h a r t i ω) k ≤
      loss h a r t k ω) :
    proxyRegret h a r k t ω ≤
      CNDPhysicalRegret.avg q
        (CNDPhysicalRegret.transported transport (fun i => loss h a r t i ω)) -
      CNDPhysicalRegret.transported transport (fun i => loss h a r t i ω) k := by
  have hm := CNDPhysicalRegret.transported_mixture (fun i => h.p t i ω) q
    (fun i => loss h a r t i ω) transport hcons
  dsimp only [proxyRegret, CNDPhysicalRegret.avg] at *
  linarith

theorem loss_measurable
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j)) (t : ℕ) (i : ι) :
    Measurable[h.encoded t] (loss h a r t i) := by
  have hp (j : ι) := (h.p_measurable t j).mono
    ((h.past_le_pre t).trans (h.pre_le_encoded t)) le_rfl
  have hac (j : ι) := (ha t j).mono
    ((h.past_le_pre t).trans (h.pre_le_encoded t)) le_rfl
  have hrc (i j : ι) := (hr t i j).mono
    ((h.past_le_pre t).trans (h.pre_le_encoded t)) le_rfl
  exact ((hac i).sub (Finset.measurable_fun_sum _ (fun j _ => (hp j).mul (hac j))) |>.sub
    (Finset.measurable_fun_sum _ (fun j _ => (hp j).mul (hrc i j)))).add
    (h.public_potential_measurable t i)

/-- Physical one-step algebra with the actual radius, using only E11. -/
theorem physical_step_le (t : ℕ) (ω : Ω) (k : ι)
    (hc : ∀ i j, |(θ i - θ j) - (a t i ω - a t j ω)| ≤ r t i j ω) :
    physical h t (h.action t ω) ω - physical h t k ω ≤
      proxyRegret h a r k t ω + CNDPayment.actualPublicResidual h (loss h a r) t ω +
      payment h r t ω + CNDPayment.encodingDifference h k t ω := by
  have hi := (CNDPhysicalRegret.confidence_controls_actual_deficit θ
    (fun j => a t j ω) (fun j => h.p t j ω) (fun i j => r t i j ω)
    (h.p_nonneg t ω) (h.p_sum t ω) hc (h.action t ω)).2
  have hk := (CNDPhysicalRegret.confidence_controls_actual_deficit θ
    (fun j => a t j ω) (fun j => h.p t j ω) (fun i j => r t i j ω)
    (h.p_nonneg t ω) (h.p_sum t ω) hc k).1
  have hid := CNDPhysicalRegret.physical_identity θ (fun j => a t j ω)
    (fun j => h.p t j ω) (fun j => h.publicCost t j ω)
    (fun j => h.error t j ω) (fun _ => 0) (fun i j => r t i j ω)
    (h.drift t ω) (h.action t ω) k
  simp only [CNDPhysicalRegret.physical, CNDPhysicalRegret.avg, sub_zero, zero_sub,
    add_zero] at hid
  change _ ≤ _ + _ + CNDPhysicalRegret.payment _ _ _ + _
  dsimp only [physical, proxyRegret, CNDPayment.actualPublicResidual,
    CNDPayment.encodingDifference, loss]
  linarith

def actionBound (W : ℝ) (T n : ℕ) (δa : ℝ) : ℝ :=
  W * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa))
def encodingBound (T n : ℕ) (δe : ℝ) : ℝ :=
  (2 * D) * Real.sqrt (2 * (n : ℝ) *
    Real.log ((Fintype.card ι : ℝ) * (T : ℝ)^2 / δe))

def Event (W : ℝ) (T : ℕ) (δa δe : ℝ) (ω : Ω) : Prop :=
  Covers (θ := θ) a r T ω ∧
  (∀ u n, u+n ≤ T → 0 < n →
    CNDPayment.intervalSum (CNDPayment.actualPublicResidual h (loss h a r)) u n ω ≤
      actionBound W T n δa) ∧
  (∀ k u n, u+n ≤ T → 0 < n →
    CNDPayment.intervalSum (CNDPayment.encodingDifference h k) u n ω ≤
      encodingBound (ι := ι) (D := D) T n δe)

/-- The only probability input beyond M1 is the explicitly conditional E11
event. Both noise events are constructed by proved interval Hoeffding bounds. -/
theorem common_event {W : ℝ} (hW : 0 ≤ W) (T : ℕ)
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j))
    (hspan : ∀ t ω i j, 0 < h.p t i ω → 0 < h.p t j ω →
      |loss h a r t i ω - loss h a r t j ω| ≤ 2 * W)
    {δc δa δe : ℝ} (hδa : 0 < δa) (hδa1 : δa < 1)
    (hδe : 0 < δe) (hδe1 : δe < 1)
    (C : Set Ω) (hC : μ.real Cᶜ ≤ δc) (hcover : ∀ ω ∈ C, Covers (θ := θ) a r T ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc + δa + δe ∧
      ∀ ω ∈ G, Event h a r W T δa δe ω := by
  classical
  let A : Set Ω := {ω | ∃ u n, u+n ≤ T ∧ 0 < n ∧
    actionBound W T n δa <
      CNDPayment.intervalSum (CNDPayment.actualPublicResidual h (loss h a r)) u n ω}
  let E : Set Ω := {ω | ∃ k u n, u+n ≤ T ∧ 0 < n ∧
    encodingBound (ι := ι) (D := D) T n δe <
      CNDPayment.intervalSum (CNDPayment.encodingDifference h k) u n ω}
  have hA : μ.real A ≤ δa := CNDPayment.public_all_intervals_delta h (loss h a r)
    hW (loss_measurable h a r ha hr) hspan T hδa hδa1
  have hE : μ.real E ≤ δe := CNDPayment.encoding_all_intervals_delta h T hδe hδe1
  let B := toMeasurable μ (Cᶜ ∪ (A ∪ E))
  refine ⟨Bᶜ, (measurableSet_toMeasurable μ _).compl, ?_, ?_⟩
  · have hb := (measureReal_union_le Cᶜ (A ∪ E)).trans
      (add_le_add hC ((measureReal_union_le A E).trans (add_le_add hA hE)))
    simpa only [B, compl_compl, measureReal_def, measure_toMeasurable, add_assoc] using hb
  · intro ω hω
    have hb : ω ∉ Cᶜ ∪ (A ∪ E) := fun hw => hω (subset_toMeasurable μ _ hw)
    refine ⟨hcover ω (by by_contra hw; exact hb (Or.inl hw)), ?_, ?_⟩
    · intro u n hu hn
      exact le_of_not_gt (fun hx => hb (Or.inr (Or.inl ⟨u,n,hu,hn,hx⟩)))
    · intro k u n hu hn
      exact le_of_not_gt (fun hx => hb (Or.inr (Or.inr ⟨k,u,n,hu,hn,hx⟩)))

/-- E12 with a deterministic expert interval bound. The cost can be E9,
its quadratic enlargement, or any proved upper bound of E10. -/
theorem e12_on_event (W : ℝ) (T : ℕ) (δa δe : ℝ)
    (cost : ℕ → ℕ → ι → Ω → ℝ)
    (hexpert : ∀ u n, u+n ≤ T → ∀ k ω,
      CNDPayment.intervalSum (proxyRegret h a r k) u n ω ≤ cost u n k ω)
    (ω : Ω) (hω : Event h a r W T δa δe ω)
    (u n : ℕ) (hu : u+n ≤ T) (hn : 0 < n) (k : ι) :
    CNDPayment.intervalSum (fun t ω => physical h t (h.action t ω) ω - physical h t k ω) u n ω ≤
      cost u n k ω + actionBound W T n δa + encodingBound (ι := ι) (D := D) T n δe +
      CNDPayment.intervalSum (payment h r) u n ω := by
  have hs := sum_le_sum (s := range n) (fun t ht =>
    physical_step_le h a r (u+t) ω k (hω.1 (u+t) (by have := mem_range.mp ht; omega)))
  simp only [sum_add_distrib] at hs
  have hp := hexpert u n hu k ω
  have ha := hω.2.1 u n hu hn
  have he := hω.2.2 k u n hu hn
  dsimp only [CNDPayment.intervalSum] at *
  linarith

def noiseCoefficient (W : ℝ) (T : ℕ) (δa δe : ℝ) : ℝ :=
  W * Real.sqrt (2 * Real.log ((T : ℝ)^2 / δa)) +
  (2 * D) * Real.sqrt (2 * Real.log ((Fintype.card ι : ℝ) * (T : ℝ)^2 / δe))

theorem bounds_factor (W : ℝ) (T n : ℕ) (δa δe : ℝ) :
    actionBound W T n δa + encodingBound (ι := ι) (D := D) T n δe =
      noiseCoefficient (ι := ι) (D := D) W T δa δe * Real.sqrt (n : ℝ) := by
  unfold actionBound encodingBound noiseCoefficient
  rw [show 2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa) =
    (n : ℝ) * (2 * Real.log ((T : ℝ)^2 / δa)) by ring,
    show 2 * (n : ℝ) * Real.log ((Fintype.card ι : ℝ) * (T : ℝ)^2 / δe) =
    (n : ℝ) * (2 * Real.log ((Fintype.card ι : ℝ) * (T : ℝ)^2 / δe)) by ring,
    Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_mul (Nat.cast_nonneg n)]
  ring

/-- E13 on precisely the E12 event, for any post-hoc constant-block path.
The supplied partition records the maximal runs if the caller wants s+1.
The private ledger is added exactly once, without any budget assumption. -/
theorem e13_on_event {W : ℝ} (hW : 0 ≤ W) (T : ℕ) (δa δe : ℝ)
    (cost : ℕ → ℕ → ι → Ω → ℝ)
    (hexpert : ∀ u n, u+n ≤ T → ∀ k ω,
      CNDPayment.intervalSum (proxyRegret h a r k) u n ω ≤ cost u n k ω)
    (ω : Ω) (hω : Event h a r W T δa δe ω)
    (P : Intervals.Partition (range T)) (start len : ℕ → ℕ)
    (hblocks : ∀ j ∈ P.labels, P.block j = Ico (start j) (start j + len j))
    (hends : ∀ j ∈ P.labels, start j + len j ≤ T)
    (hlens : ∀ j ∈ P.labels, 0 < len j)
    (path : ℕ → ι) (arm : ℕ → ι)
    (hconst : ∀ j ∈ P.labels, ∀ t ∈ P.block j, path t = arm j) :
    (∑ t ∈ range T, (physical h t (h.action t ω) ω - physical h t (path t) ω)) ≤
      (∑ j ∈ P.labels, cost (start j) (len j) (arm j) ω) +
      noiseCoefficient (ι := ι) (D := D) W T δa δe *
        Real.sqrt ((T : ℝ) * (P.labels.card : ℝ)) +
      CNDPayment.intervalSum (payment h r) 0 T ω := by
  have hlocal (j : ℕ) (hj : j ∈ P.labels) :
      (∑ t ∈ P.block j, (physical h t (h.action t ω) ω - physical h t (path t) ω)) ≤
        cost (start j) (len j) (arm j) ω +
        noiseCoefficient (ι := ι) (D := D) W T δa δe * Real.sqrt ((P.block j).card : ℝ) +
        ∑ t ∈ P.block j, payment h r t ω := by
    have he := e12_on_event h a r W T δa δe cost hexpert ω hω
      (start j) (len j) (hends j hj) (hlens j hj) (arm j)
    rw [add_assoc (cost _ _ _ _) (actionBound _ _ _ _) (encodingBound (ι := ι) (D := D) _ _ _),
      bounds_factor] at he
    have hc : (P.block j).card = len j := by rw [hblocks j hj, Nat.card_Ico]; omega
    rw [hc]
    have hreg : (∑ t ∈ P.block j,
        (physical h t (h.action t ω) ω - physical h t (path t) ω)) =
        CNDPayment.intervalSum (fun t ω => physical h t (h.action t ω) ω - physical h t (arm j) ω)
          (start j) (len j) ω := by
      simp_rw [show (∑ t ∈ P.block j, (physical h t (h.action t ω) ω - physical h t (path t) ω)) =
        ∑ t ∈ P.block j, (physical h t (h.action t ω) ω - physical h t (arm j) ω) from
        sum_congr rfl (fun t ht => by rw [hconst j hj t ht])]
      rw [hblocks j hj, sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, CNDPayment.intervalSum]
    rw [hreg, hblocks j hj, sum_Ico_eq_sum_range]
    simpa only [Nat.add_sub_cancel_left, CNDPayment.intervalSum] using he
  have hs := sum_le_sum hlocal
  rw [P.sum_blocks] at hs
  simp only [sum_add_distrib, ← mul_sum] at hs
  rw [P.sum_blocks] at hs
  have hcoef : 0 ≤ noiseCoefficient (ι := ι) (D := D) W T δa δe := by
    unfold noiseCoefficient
    exact add_nonneg (mul_nonneg hW (Real.sqrt_nonneg _))
      (mul_nonneg (by linarith [h.D_nonneg]) (Real.sqrt_nonneg _))
  have hsqrt := mul_le_mul_of_nonneg_left P.sum_sqrt_lengths_le hcoef
  simp only [card_range] at hsqrt
  have hpay : (∑ t ∈ range T, payment h r t ω) =
      CNDPayment.intervalSum (payment h r) 0 T ω := by simp [CNDPayment.intervalSum]
  rw [hpay] at hs
  linarith

/-- One measurable event supports all E12 intervals and all E13 partitions.
The comparator path, segmentation and expert costs may be read after ω. -/
theorem conditional_e12_e13 {W : ℝ} (hW : 0 ≤ W) (T : ℕ)
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j))
    (hspan : ∀ t ω i j, 0 < h.p t i ω → 0 < h.p t j ω →
      |loss h a r t i ω - loss h a r t j ω| ≤ 2 * W)
    {δc δa δe : ℝ} (hδa : 0 < δa) (hδa1 : δa < 1)
    (hδe : 0 < δe) (hδe1 : δe < 1)
    (C : Set Ω) (hC : μ.real Cᶜ ≤ δc)
    (hcover : ∀ ω ∈ C, Covers (θ := θ) a r T ω)
    (cost : ℕ → ℕ → ι → Ω → ℝ)
    (hexpert : ∀ u n, u+n ≤ T → ∀ k ω,
      CNDPayment.intervalSum (proxyRegret h a r k) u n ω ≤ cost u n k ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc + δa + δe ∧ ∀ ω ∈ G,
      (∀ u n, u+n ≤ T → 0 < n → ∀ k,
        CNDPayment.intervalSum (fun t ω => physical h t (h.action t ω) ω - physical h t k ω) u n ω ≤
          cost u n k ω + actionBound W T n δa + encodingBound (ι := ι) (D := D) T n δe +
          CNDPayment.intervalSum (payment h r) u n ω) ∧
      (∀ (P : Intervals.Partition (range T)) (start len : ℕ → ℕ),
        (∀ j ∈ P.labels, P.block j = Ico (start j) (start j + len j)) →
        (∀ j ∈ P.labels, start j + len j ≤ T) →
        (∀ j ∈ P.labels, 0 < len j) →
        ∀ (path : ℕ → ι) (arm : ℕ → ι),
        (∀ j ∈ P.labels, ∀ t ∈ P.block j, path t = arm j) →
        (∑ t ∈ range T, (physical h t (h.action t ω) ω - physical h t (path t) ω)) ≤
          (∑ j ∈ P.labels, cost (start j) (len j) (arm j) ω) +
          noiseCoefficient (ι := ι) (D := D) W T δa δe *
            Real.sqrt ((T : ℝ) * (P.labels.card : ℝ)) +
          CNDPayment.intervalSum (payment h r) 0 T ω) := by
  obtain ⟨G, hG, hprob, hgood⟩ := common_event h a r hW T ha hr hspan
    hδa hδa1 hδe hδe1 C hC hcover
  refine ⟨G, hG, hprob, ?_⟩
  intro ω hω
  constructor
  · intro u n hu hn k
    exact e12_on_event h a r W T δa δe cost hexpert ω (hgood ω hω) u n hu hn k
  · intro P start len hblocks hends hlens path arm hconst
    exact e13_on_event h a r hW T δa δe cost hexpert ω (hgood ω hω)
      P start len hblocks hends hlens path arm hconst

end Part2.ExponentialPhysical
