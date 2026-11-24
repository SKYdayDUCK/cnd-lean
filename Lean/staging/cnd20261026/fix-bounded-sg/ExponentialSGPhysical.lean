import staging.cnd20261026.«fix-bounded-sg».ExponentialGap
import staging.cnd20261025.sg.NoiseEvents

/-! SG physical conversion for an actual exponential trajectory. The expert
envelope is computed from that same trajectory. The SG combined-noise event
keeps the coefficient 2ν, without coordinate independence. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory NNReal
set_option maxHeartbeats 1600000

namespace Part2.ExponentialSGPhysical
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}
variable (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
  (a : ℕ → ι → Ω → ℝ) (r : ℕ → ι → ι → Ω → ℝ)

def physical (t : ℕ) (i : ι) (ω : Ω) : ℝ :=
  ExponentialPhysical.physical h.toM1Model t i ω + h.noise t i ω

theorem physical_step_le (t : ℕ) (ω : Ω) (k : ι)
    (hc : ∀ i j, |(θ i - θ j) - (a t i ω - a t j ω)| ≤ r t i j ω) :
    physical h t (h.action t ω) ω - physical h t k ω ≤
      ExponentialPhysical.proxyRegret h.toM1Model a r k t ω +
      CNDPayment.actualPublicResidual h.toM1Model (ExponentialPhysical.loss h.toM1Model a r) t ω +
      ExponentialPhysical.payment h.toM1Model r t ω + CNDSGMain.noiseDifference h k t ω := by
  have hb := ExponentialPhysical.physical_step_le h.toM1Model a r t ω k hc
  unfold physical CNDSGMain.noiseDifference CNDProbability.SGModel.combinedNoise
    CNDPayment.encodingDifference at *
  linarith

def noiseBound (ν : ℝ≥0) (T n : ℕ) (δn : ℝ) : ℝ :=
  (2 * (ν : ℝ)) * Real.sqrt (2 * (n : ℝ) *
    Real.log ((Fintype.card ι : ℝ) * (T : ℝ)^2 / δn))

def noiseCoefficient (ν : ℝ≥0) (W : ℝ) (T : ℕ) (δa δn : ℝ) : ℝ :=
  W * Real.sqrt (2 * Real.log ((T : ℝ)^2 / δa)) +
  (2 * (ν : ℝ)) * Real.sqrt (2 * Real.log ((Fintype.card ι : ℝ) * (T : ℝ)^2 / δn))

def Event (ν : ℝ≥0) (W : ℝ) (T : ℕ) (δa δn : ℝ) (ω : Ω) : Prop :=
  ExponentialPhysical.Covers (θ := θ) a r T ω ∧
  (∀ u n, u+n ≤ T → 0 < n →
    CNDPayment.intervalSum (CNDPayment.actualPublicResidual h.toM1Model
      (ExponentialPhysical.loss h.toM1Model a r)) u n ω ≤
      ExponentialPhysical.actionBound W T n δa) ∧
  (∀ k u n, u+n ≤ T → 0 < n →
    CNDPayment.intervalSum (CNDSGMain.noiseDifference h k) u n ω ≤ noiseBound (ι := ι) ν T n δn)

theorem common_event (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    {W : ℝ} (hW : 0 ≤ W) (T : ℕ)
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j))
    (hspan : ∀ t ω i j, 0 < h.p t i ω → 0 < h.p t j ω →
      |ExponentialPhysical.loss h.toM1Model a r t i ω -
        ExponentialPhysical.loss h.toM1Model a r t j ω| ≤ 2 * W)
    {δc δa δn : ℝ} (hδa : 0 < δa) (hδa1 : δa < 1)
    (hδn : 0 < δn) (hδn1 : δn < 1)
    (C : Set Ω) (hC : μ.real Cᶜ ≤ δc)
    (hcover : ∀ ω ∈ C, ExponentialPhysical.Covers (θ := θ) a r T ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc+δa+δn ∧
      ∀ ω ∈ G, Event h a r ν W T δa δn ω := by
  classical
  let A : Set Ω := {ω | ∃ u n, u+n ≤ T ∧ 0 < n ∧
    ExponentialPhysical.actionBound W T n δa < CNDPayment.intervalSum
      (CNDPayment.actualPublicResidual h.toM1Model (ExponentialPhysical.loss h.toM1Model a r)) u n ω}
  let N : Set Ω := {ω | ∃ k u n, u+n ≤ T ∧ 0 < n ∧
    noiseBound (ι := ι) ν T n δn < CNDPayment.intervalSum (CNDSGMain.noiseDifference h k) u n ω}
  have hA : μ.real A ≤ δa := CNDPayment.public_all_intervals_delta h.toM1Model
    (ExponentialPhysical.loss h.toM1Model a r) hW
    (ExponentialPhysical.loss_measurable h.toM1Model a r ha hr) hspan T hδa hδa1
  have hN : μ.real N ≤ δn := CNDSGMain.noise_all_intervals_delta h ν hν T hδn hδn1
  let B := toMeasurable μ (Cᶜ ∪ (A ∪ N))
  refine ⟨Bᶜ, (measurableSet_toMeasurable μ _).compl, ?_, ?_⟩
  · have hb := (measureReal_union_le Cᶜ (A ∪ N)).trans
      (add_le_add hC ((measureReal_union_le A N).trans (add_le_add hA hN)))
    simpa only [B, compl_compl, measureReal_def, measure_toMeasurable, add_assoc] using hb
  · intro ω hω
    have hb : ω ∉ Cᶜ ∪ (A ∪ N) := fun hw => hω (subset_toMeasurable μ _ hw)
    refine ⟨hcover ω (by by_contra hw; exact hb (Or.inl hw)), ?_, ?_⟩
    · intro u n hu hn
      exact le_of_not_gt (fun hx => hb (Or.inr (Or.inl ⟨u,n,hu,hn,hx⟩)))
    · intro k u n hu hn
      exact le_of_not_gt (fun hx => hb (Or.inr (Or.inr ⟨k,u,n,hu,hn,hx⟩)))

theorem e12_on_event (ν : ℝ≥0) (W : ℝ) (T : ℕ) (δa δn : ℝ)
    (cost : ℕ → ℕ → ι → Ω → ℝ)
    (hexpert : ∀ u n, u+n ≤ T → ∀ k ω,
      CNDPayment.intervalSum (ExponentialPhysical.proxyRegret h.toM1Model a r k) u n ω ≤ cost u n k ω)
    (ω : Ω) (hω : Event h a r ν W T δa δn ω)
    (u n : ℕ) (hu : u+n ≤ T) (hn : 0 < n) (k : ι) :
    CNDPayment.intervalSum (fun t ω => physical h t (h.action t ω) ω - physical h t k ω) u n ω ≤
      cost u n k ω + ExponentialPhysical.actionBound W T n δa + noiseBound (ι := ι) ν T n δn +
      CNDPayment.intervalSum (ExponentialPhysical.payment h.toM1Model r) u n ω := by
  have hs := sum_le_sum (s := range n) (fun t ht =>
    physical_step_le h a r (u+t) ω k (hω.1 (u+t) (by have := mem_range.mp ht; omega)))
  simp only [sum_add_distrib] at hs
  have hp := hexpert u n hu k ω
  have ha := hω.2.1 u n hu hn
  have hn' := hω.2.2 k u n hu hn
  dsimp only [CNDPayment.intervalSum] at *
  linarith

theorem bounds_factor (ν : ℝ≥0) (W : ℝ) (T n : ℕ) (δa δn : ℝ) :
    ExponentialPhysical.actionBound W T n δa + noiseBound (ι := ι) ν T n δn =
      noiseCoefficient (ι := ι) ν W T δa δn * Real.sqrt (n : ℝ) := by
  unfold ExponentialPhysical.actionBound noiseBound noiseCoefficient
  rw [show 2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa) =
    (n : ℝ) * (2 * Real.log ((T : ℝ)^2 / δa)) by ring,
    show 2 * (n : ℝ) * Real.log ((Fintype.card ι : ℝ) * (T : ℝ)^2 / δn) =
    (n : ℝ) * (2 * Real.log ((Fintype.card ι : ℝ) * (T : ℝ)^2 / δn)) by ring,
    Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_mul (Nat.cast_nonneg n)]
  ring

theorem e13_on_event (ν : ℝ≥0) {W : ℝ} (hW : 0 ≤ W) (T : ℕ) (δa δn : ℝ)
    (cost : ℕ → ℕ → ι → Ω → ℝ)
    (hexpert : ∀ u n, u+n ≤ T → ∀ k ω,
      CNDPayment.intervalSum (ExponentialPhysical.proxyRegret h.toM1Model a r k) u n ω ≤ cost u n k ω)
    (ω : Ω) (hω : Event h a r ν W T δa δn ω)
    (P : Intervals.Partition (range T)) (start len : ℕ → ℕ)
    (hblocks : ∀ j ∈ P.labels, P.block j = Ico (start j) (start j + len j))
    (hends : ∀ j ∈ P.labels, start j + len j ≤ T)
    (hlens : ∀ j ∈ P.labels, 0 < len j)
    (path : ℕ → ι) (arm : ℕ → ι)
    (hconst : ∀ j ∈ P.labels, ∀ t ∈ P.block j, path t = arm j) :
    (∑ t ∈ range T, (physical h t (h.action t ω) ω - physical h t (path t) ω)) ≤
      (∑ j ∈ P.labels, cost (start j) (len j) (arm j) ω) +
      noiseCoefficient (ι := ι) ν W T δa δn * Real.sqrt ((T : ℝ) * (P.labels.card : ℝ)) +
      CNDPayment.intervalSum (ExponentialPhysical.payment h.toM1Model r) 0 T ω := by
  have hlocal (j : ℕ) (hj : j ∈ P.labels) :
      (∑ t ∈ P.block j, (physical h t (h.action t ω) ω - physical h t (path t) ω)) ≤
        cost (start j) (len j) (arm j) ω +
        noiseCoefficient (ι := ι) ν W T δa δn * Real.sqrt ((P.block j).card : ℝ) +
        ∑ t ∈ P.block j, ExponentialPhysical.payment h.toM1Model r t ω := by
    have he := e12_on_event h a r ν W T δa δn cost hexpert ω hω
      (start j) (len j) (hends j hj) (hlens j hj) (arm j)
    rw [add_assoc (cost _ _ _ _) (ExponentialPhysical.actionBound _ _ _ _) (noiseBound (ι := ι) _ _ _ _),
      bounds_factor] at he
    have hc : (P.block j).card = len j := by rw [hblocks j hj, Nat.card_Ico]; omega
    rw [hc]
    have hreg : (∑ t ∈ P.block j, (physical h t (h.action t ω) ω - physical h t (path t) ω)) =
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
  have hcoef : 0 ≤ noiseCoefficient (ι := ι) ν W T δa δn := by
    unfold noiseCoefficient
    exact add_nonneg (mul_nonneg hW (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hsqrt := mul_le_mul_of_nonneg_left P.sum_sqrt_lengths_le hcoef
  simp only [card_range] at hsqrt
  have hpay : (∑ t ∈ range T, ExponentialPhysical.payment h.toM1Model r t ω) =
      CNDPayment.intervalSum (ExponentialPhysical.payment h.toM1Model r) 0 T ω := by
    simp [CNDPayment.intervalSum]
  rw [hpay] at hs
  linarith

theorem conditional_e12_e13 (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    {W : ℝ} (hW : 0 ≤ W) (T : ℕ)
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j))
    (hspan : ∀ t ω i j, 0 < h.p t i ω → 0 < h.p t j ω →
      |ExponentialPhysical.loss h.toM1Model a r t i ω -
        ExponentialPhysical.loss h.toM1Model a r t j ω| ≤ 2 * W)
    {δc δa δn : ℝ} (hδa : 0 < δa) (hδa1 : δa < 1)
    (hδn : 0 < δn) (hδn1 : δn < 1)
    (C : Set Ω) (hC : μ.real Cᶜ ≤ δc)
    (hcover : ∀ ω ∈ C, ExponentialPhysical.Covers (θ := θ) a r T ω)
    (cost : ℕ → ℕ → ι → Ω → ℝ)
    (hexpert : ∀ u n, u+n ≤ T → ∀ k ω,
      CNDPayment.intervalSum (ExponentialPhysical.proxyRegret h.toM1Model a r k) u n ω ≤ cost u n k ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc+δa+δn ∧ ∀ ω ∈ G,
      (∀ u n, u+n ≤ T → 0 < n → ∀ k,
        CNDPayment.intervalSum (fun t ω => physical h t (h.action t ω) ω - physical h t k ω) u n ω ≤
          cost u n k ω + ExponentialPhysical.actionBound W T n δa + noiseBound (ι := ι) ν T n δn +
          CNDPayment.intervalSum (ExponentialPhysical.payment h.toM1Model r) u n ω) ∧
      (∀ (P : Intervals.Partition (range T)) (start len : ℕ → ℕ),
        (∀ j ∈ P.labels, P.block j = Ico (start j) (start j + len j)) →
        (∀ j ∈ P.labels, start j + len j ≤ T) → (∀ j ∈ P.labels, 0 < len j) →
        ∀ (path : ℕ → ι) (arm : ℕ → ι),
        (∀ j ∈ P.labels, ∀ t ∈ P.block j, path t = arm j) →
        (∑ t ∈ range T, (physical h t (h.action t ω) ω - physical h t (path t) ω)) ≤
          (∑ j ∈ P.labels, cost (start j) (len j) (arm j) ω) +
          noiseCoefficient (ι := ι) ν W T δa δn * Real.sqrt ((T : ℝ) * (P.labels.card : ℝ)) +
          CNDPayment.intervalSum (ExponentialPhysical.payment h.toM1Model r) 0 T ω) := by
  obtain ⟨G,hG,hprob,hgood⟩ := common_event h a r ν hν hW T ha hr hspan hδa hδa1 hδn hδn1 C hC hcover
  exact ⟨G,hG,hprob,fun ω hω => ⟨e12_on_event h a r ν W T δa δn cost hexpert ω (hgood ω hω),
    e13_on_event h a r ν hW T δa δn cost hexpert ω (hgood ω hω)⟩⟩

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
variable (v : ExponentialComposition.Trajectory E ι Ω)

def intervalConclusion (ν : ℝ≥0) (T : ℕ) (W δa δn : ℝ) (ω : Ω) : Prop :=
  ∀ u n, u+n ≤ T → 0 < n → ∀ k,
    CNDPayment.intervalSum (fun t ω => physical h t (h.action t ω) ω - physical h t k ω) u n ω ≤
      ExponentialComposition.envelope h.toM1Model a r v T W u n k ω +
      ExponentialPhysical.actionBound W T n δa + noiseBound (ι := ι) ν T n δn +
      CNDPayment.intervalSum (ExponentialPhysical.payment h.toM1Model r) u n ω +
      ExponentialGap.gapLedger (θ := θ) a r u n ω

def pathConclusion (ν : ℝ≥0) (T : ℕ) (W δa δn : ℝ) (ω : Ω) : Prop :=
  ∀ path : ℕ → ι,
    (∑ t ∈ range T, (physical h t (h.action t ω) ω - physical h t (path t) ω)) ≤
      (∑ j ∈ (SwitchingRuns.partition path T).labels,
        ExponentialComposition.envelope h.toM1Model a r v T W
          (ExponentialComposition.runStart path T j) (ExponentialComposition.runLength path T j)
          (SwitchingRuns.label path T j) ω) +
      noiseCoefficient (ι := ι) ν W T δa δn *
        Real.sqrt ((T : ℝ) * ((ExponentialComposition.switchCount T path+1 : ℕ) : ℝ)) +
      CNDPayment.intervalSum (ExponentialPhysical.payment h.toM1Model r) 0 T ω +
      ExponentialGap.gapLedger (θ := θ) a r 0 T ω

/-- No confidence or expert-regret conclusion is an input. The gap is
charged exactly once, on top of the actual private ledger, with the original
trajectory, probabilities, radii and cover envelope all fixed. -/
theorem actual_e12_e13_with_gap_pos (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    {T : ℕ} {W : ℝ} (hv : ExponentialComposition.Laws h.toM1Model a r v T W)
    (hW : 0 ≤ W) (hT : 0 < T)
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j))
    {δa δn : ℝ} (hδa : 0 < δa) (hδa1 : δa < 1)
    (hδn : 0 < δn) (hδn1 : δn < 1) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δa+δn ∧ ∀ ω ∈ G,
      intervalConclusion h a r v ν T W δa δn ω ∧ pathConclusion h a r v ν T W δa δn ω := by
  have hmr : ∀ t i j, Measurable[ℱ t] (ExponentialGap.analysisRadius (θ := θ) a r t i j) := by
    intro t i j
    exact (hr t i j).add (ExponentialGap.gap_measurable a r ha hr t)
  have hexpert : ∀ u n, u+n ≤ T → ∀ k ω,
      CNDPayment.intervalSum (ExponentialPhysical.proxyRegret h.toM1Model a
        (ExponentialGap.analysisRadius (θ := θ) a r) k) u n ω ≤
      ExponentialComposition.envelope h.toM1Model a r v T W u n k ω := by
    intro u n hu k ω
    simpa only [CNDPayment.intervalSum, ExponentialGap.proxyRegret_analysisRadius] using
      ExponentialComposition.actual_interval_envelope h.toM1Model a r v hv u n hu k ω
  obtain ⟨G,hG,hprob,hgood⟩ := conditional_e12_e13 h a
    (ExponentialGap.analysisRadius (θ := θ) a r) ν hν hW T ha hmr
    (ExponentialGap.support_span_analysisRadius h.toM1Model a r W hv.support_span)
    (δc := 0) hδa hδa1 hδn hδn1 Set.univ (by simp)
    (fun ω _ => ExponentialGap.analysisRadius_covers a r T ω)
    (ExponentialComposition.envelope h.toM1Model a r v T W) hexpert
  refine ⟨G,hG,by simpa using hprob,?_⟩
  intro ω hω
  constructor
  · intro u n hu hn k
    have hi := (hgood ω hω).1 u n hu hn k
    simpa only [ExponentialGap.payment_interval_analysisRadius, add_assoc] using hi
  · intro path
    have hp := (hgood ω hω).2 (SwitchingRuns.partition path T)
      (ExponentialComposition.runStart path T) (ExponentialComposition.runLength path T)
      (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).1)
      (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).2.1)
      (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).2.2)
      path (SwitchingRuns.label path T)
      (fun j hj t ht => SwitchingRuns.block_constant path T j hj ht)
    rw [ExponentialComposition.maximal_run_card path T hT] at hp
    simpa only [ExponentialGap.payment_interval_analysisRadius, add_assoc] using hp

theorem zero_horizon (ν : ℝ≥0) (W δa δn : ℝ) (ω : Ω) :
    intervalConclusion h a r v ν 0 W δa δn ω ∧ pathConclusion h a r v ν 0 W δa δn ω := by
  constructor
  · intro u n hu hn
    omega
  · intro path
    simp [SwitchingRuns.partition, CNDPayment.intervalSum, ExponentialGap.gapLedger]

theorem actual_e12_e13_with_gap (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    {T : ℕ} {W : ℝ} (hv : ExponentialComposition.Laws h.toM1Model a r v T W)
    (hW : 0 ≤ W)
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j))
    {δa δn : ℝ} (hδa : 0 < δa) (hδa1 : δa < 1)
    (hδn : 0 < δn) (hδn1 : δn < 1) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δa+δn ∧ ∀ ω ∈ G,
      intervalConclusion h a r v ν T W δa δn ω ∧ pathConclusion h a r v ν T W δa δn ω := by
  by_cases hT : T = 0
  · subst T
    refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · simpa using (show (0 : ℝ) ≤ δa + δn by linarith)
    · intro ω _
      exact zero_horizon h a r v ν W δa δn ω
  · exact actual_e12_e13_with_gap_pos h a r v ν hν hv hW (Nat.pos_of_ne_zero hT)
      ha hr hδa hδa1 hδn hδn1

end Part2.ExponentialSGPhysical
