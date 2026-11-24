import staging.cnd20261026.«fix-bounded-sg».ExponentialComposition
import Mathlib.MeasureTheory.Order.Lattice

/-! Confidence-gap accounting for the actual exponential trajectory.
The inflated radius is only an analysis device: the algorithm, its surrogate,
expert exponents and envelope retain the original actual radius.
No coverage event or small-gap assertion is assumed. -/

noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 1600000

namespace Part2.ExponentialGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Exact maximum of the positive part of the actual pairwise shortfall. -/
def epsilon (θ a : ι → ℝ) (r : ι → ι → ℝ) : ℝ :=
  (univ : Finset (ι × ι)).sup' univ_nonempty
    (fun ij => max (|(θ ij.1 - θ ij.2) - (a ij.1 - a ij.2)| - r ij.1 ij.2) 0)

theorem shortfall_le_epsilon (θ a : ι → ℝ) (r : ι → ι → ℝ) (i j : ι) :
    max (|(θ i - θ j) - (a i - a j)| - r i j) 0 ≤ epsilon θ a r := by
  exact Finset.le_sup' (fun ij : ι × ι =>
    max (|(θ ij.1 - θ ij.2) - (a ij.1 - a ij.2)| - r ij.1 ij.2) 0) (mem_univ (i, j))

theorem epsilon_nonneg (θ a : ι → ℝ) (r : ι → ι → ℝ) : 0 ≤ epsilon θ a r := by
  let i : ι := Classical.arbitrary ι
  exact (le_max_right _ _).trans (shortfall_le_epsilon θ a r i i)

theorem coverage_with_gap (θ a : ι → ℝ) (r : ι → ι → ℝ) (i j : ι) :
    |(θ i - θ j) - (a i - a j)| ≤ r i j + epsilon θ a r := by
  have hg := (le_max_left (|(θ i - θ j) - (a i - a j)| - r i j) 0).trans
    (shortfall_le_epsilon θ a r i j)
  linarith

theorem epsilon_eq_zero_iff (θ a : ι → ℝ) (r : ι → ι → ℝ) :
    epsilon θ a r = 0 ↔ ∀ i j, |(θ i - θ j) - (a i - a j)| ≤ r i j := by
  constructor
  · intro he i j
    simpa [he] using coverage_with_gap θ a r i j
  · intro hc
    apply le_antisymm _ (epsilon_nonneg θ a r)
    apply Finset.sup'_le
    intro ij _
    exact max_le (sub_nonpos.mpr (hc ij.1 ij.2)) le_rfl

theorem epsilon_le_of_pair_bound (θ a : ι → ℝ) (r : ι → ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hr : ∀ i j, 0 ≤ r i j)
    (hpair : ∀ i j, |(θ i - θ j) - (a i - a j)| ≤ B) :
    epsilon θ a r ≤ B := by
  apply Finset.sup'_le
  intro ij _
  exact max_le (by linarith [hpair ij.1 ij.2, hr ij.1 ij.2]) hB

theorem epsilon_le_max_pair_error (θ a : ι → ℝ) (r : ι → ι → ℝ)
    (hr : ∀ i j, 0 ≤ r i j) :
    epsilon θ a r ≤ (univ : Finset (ι × ι)).sup' univ_nonempty
      (fun ij => |(θ ij.1 - θ ij.2) - (a ij.1 - a ij.2)|) := by
  apply Finset.sup'_le
  intro ij _
  have hh := Finset.le_sup'
    (fun ij : ι × ι => |(θ ij.1 - θ ij.2) - (a ij.1 - a ij.2)|) (mem_univ ij)
  exact max_le (by linarith [hr ij.1 ij.2]) ((abs_nonneg _).trans hh)

theorem epsilon_le_two_range (θ a : ι → ℝ) (r : ι → ι → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ R)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ R) (hr : ∀ i j, 0 ≤ r i j) :
    epsilon θ a r ≤ 2 * R := by
  apply epsilon_le_of_pair_bound θ a r (2 * R) (by linarith) hr
  intro i j
  rw [abs_le]
  constructor <;> linarith [(hθ i).1, (hθ i).2, (hθ j).1, (hθ j).2,
    (ha i).1, (ha i).2, (ha j).1, (ha j).2]

theorem epsilon_zero_range (θ a : ι → ℝ) (r : ι → ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 0) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 0)
    (hr : ∀ i j, 0 ≤ r i j) : epsilon θ a r = 0 := by
  have hu := epsilon_le_two_range θ a r 0 le_rfl hθ ha hr
  have hl := epsilon_nonneg θ a r
  linarith

/-- Runtime-computable upper envelope when only the true range [0,R] is
known. It depends on the actual center and radius, but not on theta. -/
def observableGap (R : ℝ) (a : ι → ℝ) (r : ι → ι → ℝ) : ℝ :=
  (univ : Finset (ι × ι)).sup' univ_nonempty
    (fun ij => max (R + |a ij.1 - a ij.2| - r ij.1 ij.2) 0)

theorem epsilon_le_observableGap (θ a : ι → ℝ) (r : ι → ι → ℝ) (R : ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ R) : epsilon θ a r ≤ observableGap R a r := by
  apply Finset.sup'_le
  intro ij _
  have hθabs : |θ ij.1 - θ ij.2| ≤ R := by
    rw [abs_le]
    constructor <;> linarith [(hθ ij.1).1, (hθ ij.1).2, (hθ ij.2).1, (hθ ij.2).2]
  have hγ : |(θ ij.1 - θ ij.2) - (a ij.1 - a ij.2)| ≤ R + |a ij.1 - a ij.2| := by
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hθabs).1, (abs_le.mp hθabs).2,
      le_abs_self (a ij.1 - a ij.2), neg_abs_le (a ij.1 - a ij.2)]
  have hterm : max (|(θ ij.1 - θ ij.2) - (a ij.1 - a ij.2)| - r ij.1 ij.2) 0 ≤
      max (R + |a ij.1 - a ij.2| - r ij.1 ij.2) 0 :=
    max_le_max (by linarith) le_rfl
  exact hterm.trans (Finset.le_sup' (fun kl : ι × ι =>
    max (R + |a kl.1 - a kl.2| - r kl.1 kl.2) 0) (mem_univ ij))

theorem privateDeficit_bounds (θ a p : ι → ℝ) (r : ι → ι → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (i : ι) :
    -epsilon θ a r ≤ CNDPhysicalRegret.privateDeficit θ a p r i ∧
      CNDPhysicalRegret.privateDeficit θ a p r i ≤
        CNDPhysicalRegret.payment r p i + epsilon θ a r := by
  rw [CNDPhysicalRegret.privateDeficit_expansion θ a p r hp1 i]
  have hlo : (∑ j, p j * (-epsilon θ a r)) ≤
      ∑ j, p j * ((θ i - θ j) - (a i - a j) + r i j) := by
    apply sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left
      (by linarith [(abs_le.mp (coverage_with_gap θ a r i j)).1]) (hp0 j)
  have hhi : (∑ j, p j * ((θ i - θ j) - (a i - a j) + r i j)) ≤
      ∑ j, p j * (2 * r i j + epsilon θ a r) := by
    apply sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left
      (by linarith [(abs_le.mp (coverage_with_gap θ a r i j)).2]) (hp0 j)
  simp only [← sum_mul, hp1, one_mul] at hlo
  have hsum : (∑ j, p j * (2 * r i j + epsilon θ a r)) =
      CNDPhysicalRegret.payment r p i + epsilon θ a r := by
    simp only [mul_add, sum_add_distrib, ← sum_mul, hp1, one_mul]
    unfold CNDPhysicalRegret.payment CNDPhysicalRegret.rowRadius
    rw [mul_sum]
    congr 1
    apply sum_congr rfl
    intro j _
    ring
  rw [hsum] at hhi
  exact ⟨hlo, hhi⟩

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}
variable (h : CNDProbability.M1Model ℱ μ θ R M D)
  (a : ℕ → ι → Ω → ℝ) (r : ℕ → ι → ι → Ω → ℝ)

def gap (t : ℕ) (ω : Ω) : ℝ := epsilon θ (fun i => a t i ω) (fun i j => r t i j ω)

/-- Analysis only; this does not change the actual algorithm radius. -/
def analysisRadius (t : ℕ) (i j : ι) (ω : Ω) : ℝ :=
  r t i j ω + gap (θ := θ) a r t ω

def gapLedger (u n : ℕ) (ω : Ω) : ℝ :=
  2 * CNDPayment.intervalSum (gap (θ := θ) a r) u n ω

def observableGapLedger (R : ℝ) (u n : ℕ) (ω : Ω) : ℝ :=
  2 * CNDPayment.intervalSum
    (fun t ω => observableGap R (fun i => a t i ω) (fun i j => r t i j ω)) u n ω

theorem gapLedger_le_observable (B : ℝ) (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ B)
    (u n : ℕ) (ω : Ω) :
    gapLedger (θ := θ) a r u n ω ≤ observableGapLedger a r B u n ω := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply sum_le_sum
  intro t _
  exact epsilon_le_observableGap θ _ _ B hθ

theorem gap_measurable
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j)) (t : ℕ) :
    Measurable[ℱ t] (gap (θ := θ) a r t) := by
  letI : MeasurableSpace Ω := ℱ t
  have hm : Measurable[ℱ t]
      ((univ : Finset (ι × ι)).sup' univ_nonempty (fun ij ω =>
        max (|(θ ij.1 - θ ij.2) - (a t ij.1 ω - a t ij.2 ω)| - r t ij.1 ij.2 ω) 0)) := by
    apply Finset.measurable_sup' univ_nonempty
    intro ij _
    exact (((measurable_const.sub ((ha t ij.1).sub (ha t ij.2))).abs).sub
      (hr t ij.1 ij.2)).sup measurable_const
  convert hm using 1
  funext ω
  simpa only [gap, epsilon] using (Finset.sup'_apply univ_nonempty
    (fun ij : ι × ι => fun ω =>
      max (|(θ ij.1 - θ ij.2) - (a t ij.1 ω - a t ij.2 ω)| - r t ij.1 ij.2 ω) 0) ω).symm

theorem analysisRadius_covers (T : ℕ) (ω : Ω) :
    ExponentialPhysical.Covers (θ := θ) a (analysisRadius (θ := θ) a r) T ω := by
  intro t _ i j
  exact coverage_with_gap θ (fun i => a t i ω) (fun i j => r t i j ω) i j

theorem loss_analysisRadius (t : ℕ) (i : ι) (ω : Ω) :
    ExponentialPhysical.loss h a (analysisRadius (θ := θ) a r) t i ω =
      ExponentialPhysical.loss h a r t i ω - gap (θ := θ) a r t ω := by
  unfold ExponentialPhysical.loss CNDPhysicalRegret.surrogate CNDPhysicalRegret.proxy
    CNDPhysicalRegret.rowRadius analysisRadius
  simp only [mul_add, sum_add_distrib, ← sum_mul, h.p_sum, one_mul]
  ring

theorem proxyRegret_analysisRadius (k : ι) (t : ℕ) (ω : Ω) :
    ExponentialPhysical.proxyRegret h a (analysisRadius (θ := θ) a r) k t ω =
      ExponentialPhysical.proxyRegret h a r k t ω := by
  unfold ExponentialPhysical.proxyRegret
  simp_rw [loss_analysisRadius]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, h.p_sum, one_mul]
  ring

theorem actualPublicResidual_analysisRadius (t : ℕ) (ω : Ω) :
    CNDPayment.actualPublicResidual h
      (ExponentialPhysical.loss h a (analysisRadius (θ := θ) a r)) t ω =
      CNDPayment.actualPublicResidual h (ExponentialPhysical.loss h a r) t ω := by
  unfold CNDPayment.actualPublicResidual
  simp_rw [loss_analysisRadius]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, h.p_sum, one_mul]
  ring

theorem support_span_analysisRadius (W : ℝ)
    (hspan : ∀ t ω i j, 0 < h.p t i ω → 0 < h.p t j ω →
      |ExponentialPhysical.loss h a r t i ω - ExponentialPhysical.loss h a r t j ω| ≤ 2 * W) :
    ∀ t ω i j, 0 < h.p t i ω → 0 < h.p t j ω →
      |ExponentialPhysical.loss h a (analysisRadius (θ := θ) a r) t i ω -
        ExponentialPhysical.loss h a (analysisRadius (θ := θ) a r) t j ω| ≤ 2 * W := by
  intro t ω i j hi hj
  rw [loss_analysisRadius, loss_analysisRadius]
  convert hspan t ω i j hi hj using 1 <;> congr 1 <;> ring

theorem payment_analysisRadius (t : ℕ) (ω : Ω) :
    ExponentialPhysical.payment h (analysisRadius (θ := θ) a r) t ω =
      ExponentialPhysical.payment h r t ω + 2 * gap (θ := θ) a r t ω := by
  unfold ExponentialPhysical.payment CNDPhysicalRegret.payment CNDPhysicalRegret.rowRadius
    analysisRadius
  simp only [mul_add, sum_add_distrib, ← sum_mul, h.p_sum, one_mul]

/-- The physical one-step inequality with the exact gap correction and
the original actual surrogate, payment and sampling residual. -/
theorem physical_step_le_with_gap (t : ℕ) (ω : Ω) (k : ι) :
    ExponentialPhysical.physical h t (h.action t ω) ω -
      ExponentialPhysical.physical h t k ω ≤
    ExponentialPhysical.proxyRegret h a r k t ω +
      CNDPayment.actualPublicResidual h (ExponentialPhysical.loss h a r) t ω +
      ExponentialPhysical.payment h r t ω + CNDPayment.encodingDifference h k t ω +
      2 * gap (θ := θ) a r t ω := by
  have hc := analysisRadius_covers (θ := θ) a r (t + 1) ω
  have hi := ExponentialPhysical.physical_step_le h a (analysisRadius (θ := θ) a r)
    t ω k (hc t (by omega))
  rw [proxyRegret_analysisRadius, actualPublicResidual_analysisRadius,
    payment_analysisRadius] at hi
  linarith

theorem payment_interval_analysisRadius (u n : ℕ) (ω : Ω) :
    CNDPayment.intervalSum
      (ExponentialPhysical.payment h (analysisRadius (θ := θ) a r)) u n ω =
    CNDPayment.intervalSum (ExponentialPhysical.payment h r) u n ω +
      gapLedger (θ := θ) a r u n ω := by
  unfold gapLedger CNDPayment.intervalSum
  simp_rw [payment_analysisRadius]
  rw [sum_add_distrib, mul_sum]

theorem gapLedger_nonneg (u n : ℕ) (ω : Ω) : 0 ≤ gapLedger (θ := θ) a r u n ω := by
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro t _
  exact epsilon_nonneg θ _ _

@[simp] theorem gapLedger_empty (u : ℕ) (ω : Ω) :
    gapLedger (θ := θ) a r u 0 ω = 0 := by simp [gapLedger, CNDPayment.intervalSum]

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
variable (v : ExponentialComposition.Trajectory E ι Ω)

def intervalConclusion (T : ℕ) (W δa δe : ℝ) (ω : Ω) : Prop :=
  ∀ u n, u+n ≤ T → 0 < n → ∀ k,
    CNDPayment.intervalSum (fun t ω => ExponentialPhysical.physical h t (h.action t ω) ω -
      ExponentialPhysical.physical h t k ω) u n ω ≤
    ExponentialComposition.envelope h a r v T W u n k ω +
      ExponentialPhysical.actionBound W T n δa +
      ExponentialPhysical.encodingBound (ι := ι) (D := D) T n δe +
      CNDPayment.intervalSum (ExponentialPhysical.payment h r) u n ω +
      gapLedger (θ := θ) a r u n ω

def pathConclusion (T : ℕ) (W δa δe : ℝ) (ω : Ω) : Prop :=
  ∀ path : ℕ → ι,
    (∑ t ∈ range T, (ExponentialPhysical.physical h t (h.action t ω) ω -
      ExponentialPhysical.physical h t (path t) ω)) ≤
    (∑ j ∈ (SwitchingRuns.partition path T).labels,
      ExponentialComposition.envelope h a r v T W
        (ExponentialComposition.runStart path T j) (ExponentialComposition.runLength path T j)
        (SwitchingRuns.label path T j) ω) +
    ExponentialPhysical.noiseCoefficient (ι := ι) (D := D) W T δa δe *
      Real.sqrt ((T : ℝ) * ((ExponentialComposition.switchCount T path+1 : ℕ) : ℝ)) +
    CNDPayment.intervalSum (ExponentialPhysical.payment h r) 0 T ω +
      gapLedger (θ := θ) a r 0 T ω

/-- Gap-corrected E12/E13 for the original actual exponential trajectory.
M1, predictability and deterministic Laws remain explicit; pairwise
coverage, a confidence event and an expert-regret conclusion are not inputs.
The common event costs only the two sampling/encoding failure probabilities. -/
theorem actual_e12_e13_with_gap_pos {T : ℕ} {W : ℝ}
    (hv : ExponentialComposition.Laws h a r v T W) (hW : 0 ≤ W) (hT : 0 < T)
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j))
    {δa δe : ℝ} (hδa : 0 < δa) (hδa1 : δa < 1)
    (hδe : 0 < δe) (hδe1 : δe < 1) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δa+δe ∧ ∀ ω ∈ G,
      intervalConclusion h a r v T W δa δe ω ∧
        pathConclusion h a r v T W δa δe ω := by
  have hmr : ∀ t i j, Measurable[ℱ t] (analysisRadius (θ := θ) a r t i j) := by
    intro t i j
    exact (hr t i j).add (gap_measurable a r ha hr t)
  have hspan : ∀ t ω i j, 0 < h.p t i ω → 0 < h.p t j ω →
      |ExponentialPhysical.loss h a (analysisRadius (θ := θ) a r) t i ω -
        ExponentialPhysical.loss h a (analysisRadius (θ := θ) a r) t j ω| ≤ 2 * W := by
    exact support_span_analysisRadius h a r W hv.support_span
  have hexpert : ∀ u n, u+n ≤ T → ∀ k ω,
      CNDPayment.intervalSum
        (ExponentialPhysical.proxyRegret h a (analysisRadius (θ := θ) a r) k) u n ω ≤
      ExponentialComposition.envelope h a r v T W u n k ω := by
    intro u n hu k ω
    simpa only [CNDPayment.intervalSum, proxyRegret_analysisRadius] using
      ExponentialComposition.actual_interval_envelope h a r v hv u n hu k ω
  obtain ⟨G,hG,hprob,hgood⟩ := ExponentialPhysical.conditional_e12_e13 h a
    (analysisRadius (θ := θ) a r) hW T ha hmr hspan (δc := 0)
    hδa hδa1 hδe hδe1 Set.univ (by simp)
    (fun ω _ => analysisRadius_covers a r T ω)
    (ExponentialComposition.envelope h a r v T W) hexpert
  refine ⟨G,hG,by simpa using hprob,?_⟩
  intro ω hω
  constructor
  · intro u n hu hn k
    have hi := (hgood ω hω).1 u n hu hn k
    simpa only [payment_interval_analysisRadius, add_assoc] using hi
  · intro path
    have hp := (hgood ω hω).2 (SwitchingRuns.partition path T)
      (ExponentialComposition.runStart path T) (ExponentialComposition.runLength path T)
      (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).1)
      (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).2.1)
      (fun j hj => (ExponentialComposition.maximal_run_geometry path T j hj).2.2)
      path (SwitchingRuns.label path T)
      (fun j hj t ht => SwitchingRuns.block_constant path T j hj ht)
    rw [ExponentialComposition.maximal_run_card path T hT] at hp
    simpa only [payment_interval_analysisRadius, add_assoc] using hp

theorem zero_horizon (W δa δe : ℝ) (ω : Ω) :
    intervalConclusion h a r v 0 W δa δe ω ∧ pathConclusion h a r v 0 W δa δe ω := by
  constructor
  · intro u n hu hn
    omega
  · intro path
    simp [SwitchingRuns.partition, CNDPayment.intervalSum, gapLedger]

/-- Includes the empty horizon without needing a positive-length assumption. -/
theorem actual_e12_e13_with_gap {T : ℕ} {W : ℝ}
    (hv : ExponentialComposition.Laws h a r v T W) (hW : 0 ≤ W)
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j))
    {δa δe : ℝ} (hδa : 0 < δa) (hδa1 : δa < 1)
    (hδe : 0 < δe) (hδe1 : δe < 1) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δa+δe ∧ ∀ ω ∈ G,
      intervalConclusion h a r v T W δa δe ω ∧
        pathConclusion h a r v T W δa δe ω := by
  by_cases hT : T = 0
  · subst T
    refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · simpa using (show (0 : ℝ) ≤ δa + δe by linarith)
    · intro ω _
      exact zero_horizon h a r v W δa δe ω
  · exact actual_e12_e13_with_gap_pos h a r v hv hW (Nat.pos_of_ne_zero hT)
      ha hr hδa hδa1 hδe hδe1

end Part2.ExponentialGap
