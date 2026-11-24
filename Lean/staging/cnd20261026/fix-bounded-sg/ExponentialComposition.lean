import Part2.ExponentialCovers
import staging.cnd20261026.«fix-bounded-sg».ExponentialPhysical
import SwitchingRuns

/-! Finite deterministic wiring of the actual exponential cover envelope to
the conditional M1 physical theorem. No recursive M1 instance or E11 proof
is asserted. The probability theorem has no expert-regret inequality field. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 1600000

namespace Part2.ExponentialComposition

structure Trajectory (E ι Ω : Type*) [Fintype E] [DecidableEq E] where
  eta : E → ℝ
  active : ℕ → Finset E
  arm : E → ι
  weight : ℕ → E → Ω → ℝ
  transport : ℕ → ι → ι → Ω → ℝ

variable {E Ω ι : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}
variable (h : CNDProbability.M1Model ℱ μ θ R M D)
  (a : ℕ → ι → Ω → ℝ) (r : ℕ → ι → ι → Ω → ℝ)
  (v : Trajectory E ι Ω)

def recommendation (t : ℕ) (k : ι) (ω : Ω) : ℝ :=
  Prod.mixture (v.active t) v.eta (fun e => v.weight t e ω)
    (fun e k => if v.arm e = k then 1 else 0) k

def excess (t : ℕ) (e : E) (ω : Ω) : ℝ :=
  CNDPhysicalRegret.avg (fun k => recommendation v t k ω)
    (CNDPhysicalRegret.transported (fun i j => v.transport t i j ω)
      (fun i => ExponentialPhysical.loss h a r t i ω)) -
  CNDPhysicalRegret.transported (fun i j => v.transport t i j ω)
    (fun i => ExponentialPhysical.loss h a r t i ω) (v.arm e)

def exponent (t : ℕ) (e : E) (ω : Ω) : ℝ :=
  if e ∈ v.active t then v.eta e * excess h a r v t e ω else 0

/-- Primitive deterministic equations and geometry, rather than a target
regret or concentration conclusion. Row support can also be derived from
positive recommendation masses and conservation in a concrete transport. -/
structure Laws (T : ℕ) (W : ℝ) where
  eta_pos : ∀ e, 0 < v.eta e
  initial_pos : ∀ e ω, 0 < v.weight 0 e ω
  update : ∀ t < T, ∀ e ω, v.weight (t+1) e ω =
    ExponentialExperts.step (fun i => v.weight t i ω) (fun i => exponent h a r v t i ω) e
  root : ι → E
  root_arm : ∀ k, v.arm (root k) = k
  root_awake : ∀ t < T, ∀ k, root k ∈ v.active t
  conservation : ∀ t ω j,
    (∑ i, recommendation v t i ω * v.transport t i j ω) = h.p t j ω
  domination : ∀ t ω k,
    CNDPhysicalRegret.transported (fun i j => v.transport t i j ω)
      (fun i => ExponentialPhysical.loss h a r t i ω) k ≤ ExponentialPhysical.loss h a r t k ω
  row_nonneg : ∀ t ω i j, 0 ≤ v.transport t i j ω
  row_sum : ∀ t ω i, (∑ j, v.transport t i j ω) = 1
  row_support : ∀ t ω i j, 0 < v.transport t i j ω → 0 < h.p t j ω
  support_span : ∀ t ω i j, 0 < h.p t i ω → 0 < h.p t j ω →
    |ExponentialPhysical.loss h a r t i ω - ExponentialPhysical.loss h a r t j ω| ≤ 2 * W

variable {T : ℕ} {W : ℝ}

theorem actual_gap (hv : Laws h a r v T W) (t : ℕ) (ω : Ω) (e : E) :
    ExponentialPhysical.proxyRegret h a r (v.arm e) t ω ≤ excess h a r v t e ω := by
  exact ExponentialPhysical.proxyRegret_le_transported h a r t ω (v.arm e)
    (fun k => recommendation v t k ω) (fun i j => v.transport t i j ω)
    (hv.conservation t ω) (hv.domination t ω (v.arm e))

/-- The 2W cap is derived from row stochasticity, support geometry and
domination, including comparators outside the execution support. -/
theorem actual_cap (hv : Laws h a r v T W) (t : ℕ) (ω : Ω) (k : ι) :
    ExponentialPhysical.proxyRegret h a r k t ω ≤ 2 * W := by
  let l := fun i => ExponentialPhysical.loss h a r t i ω
  let m := fun j => v.transport t k j ω
  have hpoint (i : ι) (hi : 0 < h.p t i ω) :
      l i - (∑ j, m j * l j) ≤ 2 * W := by
    have hs : (∑ j, m j * (l i - l j)) ≤ ∑ j, m j * (2 * W) := by
      apply sum_le_sum
      intro j _
      by_cases hj : m j = 0
      · simp [hj]
      · have hjp : 0 < m j := lt_of_le_of_ne (hv.row_nonneg t ω k j) (Ne.symm hj)
        exact mul_le_mul_of_nonneg_left
          (le_trans (le_abs_self _) (hv.support_span t ω i j hi (hv.row_support t ω k j hjp)))
          hjp.le
    simp only [mul_sub, sum_sub_distrib, ← sum_mul] at hs
    rw [show (∑ j, m j) = 1 from hv.row_sum t ω k] at hs
    simpa only [one_mul] using hs
  have hs : (∑ i, h.p t i ω * (l i - ∑ j, m j * l j)) ≤
      ∑ i, h.p t i ω * (2 * W) := by
    apply sum_le_sum
    intro i _
    by_cases hi : h.p t i ω = 0
    · simp [hi]
    · exact mul_le_mul_of_nonneg_left (hpoint i
        (lt_of_le_of_ne (h.p_nonneg t ω i) (Ne.symm hi))) (h.p_nonneg t ω i)
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, h.p_sum, one_mul] at hs
  have hd := hv.domination t ω k
  change (∑ i, m i * l i) ≤ l k at hd
  dsimp only [ExponentialPhysical.proxyRegret]
  change (∑ i, h.p t i ω * l i) - l k ≤ _
  linarith

def envelope (T : ℕ) (W : ℝ) (u n : ℕ) (k : ι) (ω : Ω) : ℝ :=
  if n = 0 then 0 else
    min (2 * W * ((Ico u (u+n)).card : ℝ))
      (sInf (Set.range (fun C : ExponentialCovers.Cover T v.active v.arm k (Ico u (u+n)) =>
        C.totalCost (fun t e => v.weight t e ω) (fun t e => exponent h a r v t e ω) v.eta)))

/-- Actual E10, constructed from the one original virtual trajectory. -/
theorem actual_interval_envelope (hv : Laws h a r v T W)
    (u n : ℕ) (hu : u+n ≤ T) (k : ι) (ω : Ω) :
    CNDPayment.intervalSum (ExponentialPhysical.proxyRegret h a r k) u n ω ≤
      envelope h a r v T W u n k ω := by
  by_cases hn : n = 0
  · simp [hn, CNDPayment.intervalSum, envelope]
  · have he := ExponentialCovers.interval_envelope T u n (Nat.pos_of_ne_zero hn) hu
      v.active v.arm k (fun t e => v.weight t e ω) (fun t e => exponent h a r v t e ω)
      (fun t e => excess h a r v t e ω) v.eta
      (fun t => ExponentialPhysical.proxyRegret h a r k t ω) W
      hv.eta_pos (fun e => hv.initial_pos e ω)
      (fun t ht e => hv.update t ht e ω)
      (fun t _ e he => by simp only [exponent, if_pos he])
      (fun t _ e _ hk => by simpa only [hk] using actual_gap h a r v hv t ω e)
      (fun t _ => actual_cap h a r v hv t ω k)
      (hv.root k) (fun t ht => hv.root_awake t ht k) (hv.root_arm k)
    rw [sum_Ico_eq_sum_range] at he
    simpa only [Nat.add_sub_cancel_left, CNDPayment.intervalSum, envelope, if_neg hn] using he

def runStart (path : ℕ → ι) (T j : ℕ) : ℕ :=
  if hn : ((SwitchingRuns.partition path T).block j).Nonempty then
    ((SwitchingRuns.partition path T).block j).min' hn else 0

def runLength (path : ℕ → ι) (T j : ℕ) : ℕ :=
  if hn : ((SwitchingRuns.partition path T).block j).Nonempty then
    ((SwitchingRuns.partition path T).block j).max' hn + 1 -
      ((SwitchingRuns.partition path T).block j).min' hn else 0

def switchCount (T : ℕ) (path : ℕ → ι) : ℕ :=
  ((range (T-1)).filter (fun t => path (t+1) ≠ path t)).card

theorem maximal_run_geometry (path : ℕ → ι) (T j : ℕ)
    (hj : j ∈ (SwitchingRuns.partition path T).labels) :
    (SwitchingRuns.partition path T).block j = Ico (runStart path T j)
      (runStart path T j + runLength path T j) ∧
    runStart path T j + runLength path T j ≤ T ∧ 0 < runLength path T j := by
  have hn := SwitchingRuns.block_nonempty path T j hj
  have hmin := min'_mem _ hn
  have hmax := max'_mem _ hn
  have hle := min'_le _ _ hmax
  have hmaxT : ((SwitchingRuns.partition path T).block j).max' hn < T :=
    mem_range.mp (mem_filter.mp hmax).1
  simp only [runStart, runLength, dif_pos hn]
  constructor
  · calc
      _ = Icc (((SwitchingRuns.partition path T).block j).min' hn)
        (((SwitchingRuns.partition path T).block j).max' hn) :=
          SwitchingRuns.block_eq_Icc path T j hj
      _ = _ := ?_
    ext t
    simp only [mem_Icc, mem_Ico]
    omega
  · omega

theorem maximal_run_card (path : ℕ → ι) (T : ℕ) (hT : 0 < T) :
    (SwitchingRuns.partition path T).labels.card = switchCount T path + 1 := by
  cases T with
  | zero => omega
  | succ N =>
    rw [SwitchingRuns.partition_card, SwitchingRuns.runIndex_eq_actual_changes]
    simp only [switchCount, Nat.add_sub_cancel]

def intervalConclusion (T : ℕ) (W δa δe : ℝ) (ω : Ω) : Prop :=
  ∀ u n, u+n ≤ T → 0 < n → ∀ k,
    CNDPayment.intervalSum (fun t ω => ExponentialPhysical.physical h t (h.action t ω) ω -
      ExponentialPhysical.physical h t k ω) u n ω ≤
    envelope h a r v T W u n k ω + ExponentialPhysical.actionBound W T n δa +
      ExponentialPhysical.encodingBound (ι := ι) (D := D) T n δe +
      CNDPayment.intervalSum (ExponentialPhysical.payment h r) u n ω

def pathConclusion (T : ℕ) (W δa δe : ℝ) (ω : Ω) : Prop :=
  ∀ path : ℕ → ι,
    (∑ t ∈ range T, (ExponentialPhysical.physical h t (h.action t ω) ω -
      ExponentialPhysical.physical h t (path t) ω)) ≤
    (∑ j ∈ (SwitchingRuns.partition path T).labels,
      envelope h a r v T W (runStart path T j) (runLength path T j)
        (SwitchingRuns.label path T j) ω) +
    ExponentialPhysical.noiseCoefficient (ι := ι) (D := D) W T δa δe *
      Real.sqrt ((T : ℝ) * ((switchCount T path+1 : ℕ) : ℝ)) +
    CNDPayment.intervalSum (ExponentialPhysical.payment h r) 0 T ω

/-- Actual E9/E10 composed with conditional E12 and actual maximal runs E13.
Neither target inequality is an input. Paths can be selected after ω. -/
theorem actual_conditional_e12_e13 (hv : Laws h a r v T W) (hW : 0 ≤ W) (hT : 0 < T)
    (ha : ∀ t i, Measurable[ℱ t] (a t i))
    (hr : ∀ t i j, Measurable[ℱ t] (r t i j))
    {δc δa δe : ℝ} (hδa : 0 < δa) (hδa1 : δa < 1)
    (hδe : 0 < δe) (hδe1 : δe < 1)
    (C : Set Ω) (hC : μ.real Cᶜ ≤ δc)
    (hcover : ∀ ω ∈ C, ExponentialPhysical.Covers (θ := θ) a r T ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc+δa+δe ∧ ∀ ω ∈ G,
      intervalConclusion h a r v T W δa δe ω ∧ pathConclusion h a r v T W δa δe ω := by
  obtain ⟨G,hG,hprob,hgood⟩ := ExponentialPhysical.conditional_e12_e13 h a r hW T
    ha hr hv.support_span hδa hδa1 hδe hδe1 C hC hcover
    (envelope h a r v T W) (actual_interval_envelope h a r v hv)
  refine ⟨G,hG,hprob,?_⟩
  intro ω hω
  refine ⟨(hgood ω hω).1, ?_⟩
  intro path
  have hp := (hgood ω hω).2 (SwitchingRuns.partition path T)
    (runStart path T) (runLength path T)
    (fun j hj => (maximal_run_geometry path T j hj).1)
    (fun j hj => (maximal_run_geometry path T j hj).2.1)
    (fun j hj => (maximal_run_geometry path T j hj).2.2)
    path (SwitchingRuns.label path T)
    (fun j hj t ht => SwitchingRuns.block_constant path T j hj ht)
  rw [maximal_run_card path T hT] at hp
  exact hp

end Part2.ExponentialComposition
