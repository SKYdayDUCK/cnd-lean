import staging.cnd20261026.«fix-bounded-sg».ExponentialGeometry
import staging.cnd20261026.«fix-bounded-sg».ExponentialComposition

/-! Shared actual exponential trajectory and composition laws from generic
original feedback and an identified stopped M1 shadow. Bounded and SG runs
share every update, transport and support argument in this module. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 2400000

namespace Part2.ExponentialActual
open CNDProcess CNDHorizon
variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}
  {θ : Fin K → ℝ} {R M D W : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A finite preset library with an independent positive prior per expert.
No dyadic windows or learning-rate upper bound are required. -/
abbrev Config (T : ℕ) (R W : ℝ) := ExponentialGeometry.Config (K := K) (E := E) T R W

variable (H L : ℝ) (hR : 0 ≤ R) (hW : 0 ≤ W)
  (c : Config (K := K) (E := E) T R W) (f : Feedback (ι := Fin K) ℱ)

def maps : DecisionMaps (Fin K) := ExponentialGeometry.maps H L R W hR hW c
def state (t : ℕ) (ω : Ω) : State (Fin K) E :=
  ExponentialStochastic.run (maps H L hR hW c) c.data c.prior f t ω

def center (t : ℕ) (i : Fin K) (ω : Ω) : ℝ :=
  if t<T then confidence (maps H L hR hW c) c.data (state H L hR hW c f t ω) i else 0
def radius (t : ℕ) (i j : Fin K) (ω : Ω) : ℝ :=
  if t<T then CNDProcess.radius (maps H L hR hW c) c.data (state H L hR hW c f t ω) i j else 0

def trajectory : ExponentialComposition.Trajectory E (Fin K) Ω where
  eta := c.data.eta
  active t := if t<T then activeSet c.data t else univ
  arm := c.data.arm
  weight t e ω := (state H L hR hW c f t ω).2 e
  transport t i j ω := if t<T then transport (maps H L hR hW c) c.data t (state H L hR hW c f t ω) i j
    else if (CNDHorizon.root : Fin K) = j then 1 else 0

variable (m : CNDProbability.M1Model ℱ μ θ R M D)

/-- Same original feedback and stopping identities, rather than a geometry,
regret or concentration oracle. Both bounded and SG models instantiate it. -/
structure Bridge : Prop where
  p_before : ∀ t<T, m.p t = ExponentialStochastic.runProbability (maps H L hR hW c) c.data c.prior f t
  broadcast_before : ∀ t<T, ∀ ω i, f.broadcast t ω i = m.publicCost t i ω + m.error t i ω
  p_after : ∀ t, ¬t<T → m.p t = fun i _ => if (CNDHorizon.root : Fin K)=i then 1 else 0
  public_after : ∀ t, ¬t<T → m.publicCost t = fun _ _ => 0
  error_after : ∀ t, ¬t<T → m.error t = fun _ _ => 0

theorem center_measurable (t : ℕ) (i : Fin K) : Measurable[ℱ t] (center H L hR hW c f t i) := by
  change Measurable[ℱ t] (fun ω => if t<T then
    confidence (maps H L hR hW c) c.data (state H L hR hW c f t ω) i else 0)
  by_cases ht : t<T
  · simp only [if_pos ht]
    exact ExponentialStochastic.run_center_measurable (maps H L hR hW c) c.data c.prior f t i
  · simp only [if_neg ht]; exact measurable_const

theorem radius_measurable (t : ℕ) (i j : Fin K) : Measurable[ℱ t] (radius H L hR hW c f t i j) := by
  change Measurable[ℱ t] (fun ω => if t<T then
    CNDProcess.radius (maps H L hR hW c) c.data (state H L hR hW c f t ω) i j else 0)
  by_cases ht : t<T
  · simp only [if_pos ht]
    exact ExponentialStochastic.run_radius_measurable (maps H L hR hW c) c.data c.prior f t i j
  · simp only [if_neg ht]; exact measurable_const

theorem concrete_radius_isCND (hH : 0 ≤ H) (hL : 0 ≤ L) (t : ℕ) (ω : Ω) :
    CND.IsCND (CNDProcess.radius (maps H L hR hW c) c.data (state H L hR hW c f t ω)) := by
  exact ExponentialGeometry.concrete_radius_isCND H L R W hR hW c f
    hH hL t ω

theorem recommendation_before (hWpos : 0 < W) (t : ℕ) (ht : t<T) (ω : Ω) :
    (fun k => ExponentialComposition.recommendation (trajectory H L hR hW c f) t k ω) =
      suggestion c.data t (state H L hR hW c f t ω) := by
  have hw : c.data.W ≠ 0 := by rw [c.width_eq]; exact ne_of_gt hWpos
  funext k
  simpa only [trajectory, ExponentialComposition.recommendation, if_pos ht, pureAdvice] using
    (congrFun (suggestion_eq_pure_mixture c.data hw t (state H L hR hW c f t ω)) k).symm

theorem loss_before (hm : Bridge H L hR hW c f m) (t : ℕ) (ht : t<T) (ω : Ω) (i : Fin K) :
    ExponentialPhysical.loss m (center H L hR hW c f) (radius H L hR hW c f) t i ω =
      processLoss (maps H L hR hW c) c.data t (state H L hR hW c f t ω) (f.broadcast t ω) i := by
  have hp := hm.p_before t ht
  simp only [ExponentialPhysical.loss, center, radius, if_pos ht, hp,
    CNDPhysicalRegret.surrogate, CNDPhysicalRegret.proxy, CNDPhysicalRegret.broadcast,
    CNDPhysicalRegret.avg, CNDPhysicalRegret.rowRadius]
  let o := maps H L hR hW c
  let s := state H L hR hW c f t ω
  change (confidence o c.data s i - (∑ j, probability o c.data t s j * confidence o c.data s j) -
    (∑ j, probability o c.data t s j * CNDProcess.radius o c.data s i j)) +
    (m.publicCost t i ω + m.error t i ω) =
    (confidence o c.data s i - (∑ j, CNDProcess.radius o c.data s i j * probability o c.data t s j) -
    (∑ j, probability o c.data t s j * confidence o c.data s j)) + f.broadcast t ω i
  rw [hm.broadcast_before t ht ω i]
  have hmul : (∑ j, CNDProcess.radius o c.data s i j * probability o c.data t s j) =
    ∑ j, probability o c.data t s j * CNDProcess.radius o c.data s i j :=
      sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [hmul]
  ring

theorem loss_after (hm : Bridge H L hR hW c f m) (t : ℕ) (ht : ¬t<T) (ω : Ω) (i : Fin K) :
    ExponentialPhysical.loss m (center H L hR hW c f) (radius H L hR hW c f) t i ω = 0 := by
  simp [ExponentialPhysical.loss, center, radius, ht, hm.public_after t ht, hm.error_after t ht,
    CNDPhysicalRegret.surrogate, CNDPhysicalRegret.proxy, CNDPhysicalRegret.broadcast,
    CNDPhysicalRegret.avg, CNDPhysicalRegret.rowRadius]

/-- Actual canonical geometry at an executed slot. In particular row support
is proved from strictly positive actual q, conservation and nonnegative rows. -/
theorem raw_geometry (hH : 0 ≤ H) (hL : 0 ≤ L) (hWpos : 0 < W)
    (hb : ∀ t<T, ∀ ω i j, f.broadcast t ω j - f.broadcast t ω i ≤ W)
    (t : ℕ) (ht : t<T) (ω : Ω) :
    let o := maps H L hR hW c
    let s := state H L hR hW c f t ω
    let q := suggestion c.data t s
    let p := probability o c.data t s
    let m := transport o c.data t s
    let l := processLoss o c.data t s (f.broadcast t ω)
    (∀ j, (∑ i, q i * m i j) = p j) ∧ (∀ i j, 0 ≤ m i j) ∧
    (∀ i, (∑ j, m i j) = 1) ∧ (∀ i j, 0 < m i j → 0 < p j) ∧
    (∀ k, (∑ j, m k j * l j) ≤ l k) ∧
    (∀ i j, 0 < p i → 0 < p j → |l i - l j| ≤ 2*W) := by
  apply ExponentialGeometry.raw_geometry H L R W hR hW c f
    hH hL hWpos _ t ht ω
  intro n hn ω i j
  exact hb n hn ω i j

theorem recommendation_simplex (hWpos : 0 < W) (t : ℕ) (ω : Ω) :
    (fun k => ExponentialComposition.recommendation (trajectory H L hR hW c f) t k ω) ∈ CND.simplex := by
  let v := trajectory H L hR hW c f
  let d : ExpertData (Fin K) E := { c.data with active := fun _ e => decide (e ∈ v.active t) }
  have hset : activeSet d t = v.active t := by ext e; simp [activeSet,d]
  have hne : (v.active t).Nonempty := by
    by_cases ht : t<T
    · exact ⟨c.root CNDHorizon.root, by simpa only [v,trajectory,if_pos ht] using c.root_awake t ht CNDHorizon.root⟩
    · simpa only [v,trajectory,if_neg ht] using (univ_nonempty : (univ : Finset E).Nonempty)
  have hw : d.W ≠ 0 := by change c.data.W ≠ 0; rw [c.width_eq]; exact ne_of_gt hWpos
  have hq := suggestion_simplex_of_positive d hw t (state H L hR hW c f t ω)
    (by rw [hset]; exact hne) c.eta_pos
    (ExponentialStochastic.run_weights_positive (maps H L hR hW c) c.data c.prior f c.prior_pos t ω)
  rw [suggestion_eq_pure_mixture d hw, hset] at hq
  exact hq

theorem meanExpertLoss_eq_suggestion_average (o : DecisionMaps (Fin K)) (d : ExpertData (Fin K) E)
    (hwidth : d.W ≠ 0) (t : ℕ) (s : State (Fin K) E) (b : Vec (Fin K)) :
    meanExpertLoss o d t s b = CNDPhysicalRegret.avg (suggestion d t s)
      (CNDPhysicalRegret.transported (transport o d t s) (processLoss o d t s b)) := by
  have hcons (j : Fin K) : (∑ k, suggestion d t s k * transport o d t s k j) =
      Prod.mixture (activeSet d t) d.eta s.2 (processAdvice o d t s) j := by
    rw [suggestion_eq_pure_mixture d hwidth]
    exact (CNDProd.mixture_remap (activeSet d t) d.eta s.2 d.arm (transport o d t s) j).symm
  have hid := CNDPhysicalRegret.transported_mixture
    (Prod.mixture (activeSet d t) d.eta s.2 (processAdvice o d t s))
    (suggestion d t s) (processLoss o d t s b) (transport o d t s) hcons
  exact (meanExpertLoss_eq_mixtureLoss o d t s b).trans hid.symm

theorem actual_excess_before (hm : Bridge H L hR hW c f m) (hWpos : 0 < W) (t : ℕ) (ht : t<T)
    (e : E) (ω : Ω) :
    ExponentialComposition.excess m (center H L hR hW c f) (radius H L hR hW c f)
      (trajectory H L hR hW c f) t e ω =
    meanExpertLoss (maps H L hR hW c) c.data t (state H L hR hW c f t ω) (f.broadcast t ω) -
      expertLoss (maps H L hR hW c) c.data t (state H L hR hW c f t ω) (f.broadcast t ω) e := by
  unfold ExponentialComposition.excess
  rw [recommendation_before H L hR hW c f hWpos t ht ω]
  simp_rw [loss_before H L hR hW c f m hm t ht ω]
  simp only [trajectory, if_pos ht]
  rw [meanExpertLoss_eq_suggestion_average _ _ (by rw [c.width_eq]; exact ne_of_gt hWpos)]
  rfl

theorem actual_exponent_before (hm : Bridge H L hR hW c f m) (hWpos : 0 < W) (t : ℕ) (ht : t<T)
    (e : E) (ω : Ω) :
    ExponentialComposition.exponent m (center H L hR hW c f) (radius H L hR hW c f)
      (trajectory H L hR hW c f) t e ω =
    if c.data.active t e then c.data.eta e *
      (meanExpertLoss (maps H L hR hW c) c.data t (state H L hR hW c f t ω) (f.broadcast t ω) -
        expertLoss (maps H L hR hW c) c.data t (state H L hR hW c f t ω) (f.broadcast t ω) e) else 0 := by
  unfold ExponentialComposition.exponent
  rw [actual_excess_before H L hR hW c f m hm hWpos t ht e ω]
  simp only [trajectory,if_pos ht,activeSet,mem_filter,mem_univ,true_and]

theorem actual_update (hm : Bridge H L hR hW c f m) (hWpos : 0 < W) (t : ℕ) (ht : t<T) (e : E) (ω : Ω) :
    (trajectory H L hR hW c f).weight (t+1) e ω =
      ExponentialExperts.step (fun i => (trajectory H L hR hW c f).weight t i ω)
        (fun i => ExponentialComposition.exponent m (center H L hR hW c f)
          (radius H L hR hW c f) (trajectory H L hR hW c f) t i ω) e := by
  have hw : c.data.W ≠ 0 := by rw [c.width_eq]; exact ne_of_gt hWpos
  change (if c.data.W = 0 then (state H L hR hW c f t ω).2 e else if c.data.active t e then
    (state H L hR hW c f t ω).2 e * Real.exp (c.data.eta e *
      (meanExpertLoss (maps H L hR hW c) c.data t (state H L hR hW c f t ω) (f.broadcast t ω) -
        expertLoss (maps H L hR hW c) c.data t (state H L hR hW c f t ω) (f.broadcast t ω) e))
    else (state H L hR hW c f t ω).2 e) = _
  rw [if_neg hw]
  simp only [ExponentialExperts.step]
  rw [actual_exponent_before H L hR hW c f m hm hWpos t ht e ω]
  by_cases he : c.data.active t e = true <;> simp [he,trajectory]

theorem model_p_after (hm : Bridge H L hR hW c f m) (t : ℕ) (ht : ¬t<T) :
    m.p t = fun i _ => if (CNDHorizon.root : Fin K)=i then 1 else 0 := hm.p_after t ht

/-- All Composition laws are now theorems of the actual recursion and
canonical decisions. No row-support, regret, confidence or tail field is
assumed. After T the matrix maps every row to the stopping root. -/
def compositionLaws (hm : Bridge H L hR hW c f m) (hH : 0 ≤ H) (hL : 0 ≤ L) (hWpos : 0 < W)
    (hb : ∀ t<T, ∀ ω i j, f.broadcast t ω j - f.broadcast t ω i ≤ W) :
    ExponentialComposition.Laws m (center H L hR hW c f) (radius H L hR hW c f)
      (trajectory H L hR hW c f) T W where
  eta_pos := c.eta_pos
  initial_pos := fun e _ => c.prior_pos e
  update := actual_update H L hR hW c f m hm hWpos
  root := c.root
  root_arm := c.root_arm
  root_awake t ht k := by simpa only [trajectory,if_pos ht] using c.root_awake t ht k
  conservation t ω j := by
    by_cases ht : t<T
    · have hg := (raw_geometry H L hR hW c f hH hL hWpos hb t ht ω).1 j
      rw [← recommendation_before H L hR hW c f hWpos t ht ω] at hg
      change (∑ i, ExponentialComposition.recommendation (trajectory H L hR hW c f) t i ω *
        (trajectory H L hR hW c f).transport t i j ω) = m.p t j ω
      rw [show m.p t = ExponentialStochastic.runProbability
        (maps H L hR hW c) c.data c.prior f t from hm.p_before t ht]
      simpa only [trajectory,if_pos ht] using hg
    · rw [model_p_after H L hR hW c f m hm t ht]
      simp only [trajectory,if_neg ht]
      change (∑ i, ExponentialComposition.recommendation (trajectory H L hR hW c f) t i ω *
        (if (CNDHorizon.root : Fin K)=j then 1 else 0)) = _
      rw [← sum_mul,(recommendation_simplex H L hR hW c f hWpos t ω).2,one_mul]
  domination t ω k := by
    by_cases ht : t<T
    · simp_rw [loss_before H L hR hW c f m hm t ht ω]
      change (∑ j, (trajectory H L hR hW c f).transport t k j ω * _) ≤ _
      simpa only [trajectory,if_pos ht] using (raw_geometry H L hR hW c f hH hL hWpos hb t ht ω).2.2.2.2.1 k
    · simp_rw [loss_after H L hR hW c f m hm t ht ω]
      simp [CNDPhysicalRegret.transported]
  row_nonneg t ω i j := by
    by_cases ht : t<T
    · simpa only [trajectory,if_pos ht] using (raw_geometry H L hR hW c f hH hL hWpos hb t ht ω).2.1 i j
    · change 0 ≤ if t<T then _ else if (CNDHorizon.root : Fin K)=j then 1 else 0
      simp only [if_neg ht]
      split_ifs <;> norm_num
  row_sum t ω i := by
    by_cases ht : t<T
    · simpa only [trajectory,if_pos ht] using (raw_geometry H L hR hW c f hH hL hWpos hb t ht ω).2.2.1 i
    · simp [trajectory,ht]
  row_support t ω i j := by
    by_cases ht : t<T
    · intro hij
      simp only [trajectory,if_pos ht] at hij
      rw [show m.p t = ExponentialStochastic.runProbability
        (maps H L hR hW c) c.data c.prior f t from hm.p_before t ht]
      exact (raw_geometry H L hR hW c f hH hL hWpos hb t ht ω).2.2.2.1 i j hij
    · intro hij
      rw [model_p_after H L hR hW c f m hm t ht]
      simpa only [trajectory,if_neg ht] using hij
  support_span t ω i j := by
    by_cases ht : t<T
    · intro hi hj
      simp_rw [loss_before H L hR hW c f m hm t ht ω]
      rw [show m.p t = ExponentialStochastic.runProbability
        (maps H L hR hW c) c.data c.prior f t from hm.p_before t ht] at hi hj
      exact (raw_geometry H L hR hW c f hH hL hWpos hb t ht ω).2.2.2.2.2 i j hi hj
    · intro _ _
      simp_rw [loss_after H L hR hW c f m hm t ht ω]
      simp only [sub_self,abs_zero]
      linarith


end Part2.ExponentialActual
