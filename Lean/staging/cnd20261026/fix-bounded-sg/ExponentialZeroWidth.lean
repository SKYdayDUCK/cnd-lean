import staging.cnd20261026.«fix-bounded-sg».ExponentialGeometry
import staging.cnd20261026.«fix-bounded-sg».ExponentialSGPhysical
import staging.cnd20261026.«fix-bounded-sg».ExponentialSGStochastic
import staging.cnd20261026.«fix-bounded-sg».ExponentialSGFinite

/-! The actual zero-width exponential branch. Its recommendation is uniform
and its expert coordinates are untouched, even for zero/negative unused eta
and arbitrary priors. Physical bounds use canonical optimality, with zero
expert cost; no E9 expression or positive-rate/root configuration is needed.
The actual confidence/radius scales remain in the computed maps. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory NNReal
set_option maxHeartbeats 2400000
namespace Part2.ExponentialZeroWidth
open CNDProcess CNDHorizon

section Recursion
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [Nonempty E]

theorem suggestion_uniform (d : ExpertData ι E) (hd : d.W=0)
    (n : ℕ) (s : State ι E) (i : ι) :
    suggestion d n s i=(Fintype.card ι:ℝ)⁻¹ := by
  simp [suggestion,hd]

theorem step_experts_unchanged (o : DecisionMaps ι) (d : ExpertData ι E) (hd : d.W=0)
    (n : ℕ) (s : State ι E) (A : ι) (Y : ℝ) (b : Vec ι) :
    (ExponentialStochastic.step o d n s A Y b).2=s.2 := by
  funext e
  simp [ExponentialStochastic.step,hd]

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] {ℱ : Filtration ℕ m₀}

theorem rawRun_experts_eq_prior (o : DecisionMaps ι) (d : ExpertData ι E) (hd : d.W=0)
    (prior : E → ℝ) (A : ℕ → Ω → ι) (Y : ℕ → Ω → ℝ) (b : ℕ → Ω → Vec ι)
    (n : ℕ) (ω : Ω) :
    (ExponentialStochastic.rawRun o d prior A Y b n ω).2=prior := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (ExponentialStochastic.step o d n _ _ _ _).2=prior
    rw [step_experts_unchanged o d hd,ih]

theorem run_experts_eq_prior (o : DecisionMaps ι) (d : ExpertData ι E) (hd : d.W=0)
    (prior : E → ℝ) (f : Feedback (ι:=ι) ℱ) (n : ℕ) (ω : Ω) :
    (ExponentialStochastic.run o d prior f n ω).2=prior :=
  rawRun_experts_eq_prior o d hd prior f.action f.residual f.broadcast n ω

theorem run_suggestion_uniform (o : DecisionMaps ι) (d : ExpertData ι E) (hd : d.W=0)
    (prior : E → ℝ) (f : Feedback (ι:=ι) ℱ) (n : ℕ) (ω : Ω) (i : ι) :
    suggestion d n (ExponentialStochastic.run o d prior f n ω) i=(Fintype.card ι:ℝ)⁻¹ :=
  suggestion_uniform d hd n _ i
end Recursion

variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}

def maps (H L R cs rs : ℝ) (hR : 0≤R) : DecisionMaps (Fin K) :=
  ExponentialScaledMaps.decisionMaps H L R 0 cs rs hR le_rfl

variable (H L R cs rs : ℝ) (hR : 0≤R)
  (d : ExpertData (Fin K) E) (prior : E → ℝ) (f : Feedback (ι:=Fin K) ℱ)

def state (t : ℕ) (ω : Ω) : State (Fin K) E :=
  ExponentialStochastic.run (maps H L R cs rs hR) d prior f t ω

def center (T t : ℕ) (i : Fin K) (ω : Ω) : ℝ :=
  if t<T then confidence (maps H L R cs rs hR) d (state H L R cs rs hR d prior f t ω) i else 0

def radius (T t : ℕ) (i j : Fin K) (ω : Ω) : ℝ :=
  if t<T then CNDProcess.radius (maps H L R cs rs hR) d (state H L R cs rs hR d prior f t ω) i j else 0

theorem radius_isCND (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs) (t : ℕ) (ω : Ω) :
    CND.IsCND (CNDProcess.radius (maps H L R cs rs hR) d
      (state H L R cs rs hR d prior f t ω)) :=
  ExponentialGeometry.run_scaled_radius_isCND H L R 0 cs rs hR le_rfl hrs d prior f hH hL t ω

theorem proxy_nonpos (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (t : ℕ) (ω : Ω) (k : Fin K)
    (hb : ∀ i j,f.broadcast t ω j-f.broadcast t ω i≤0) :
    let o := maps (K:=K) H L R cs rs hR
    let s := state H L R cs rs hR d prior f t ω
    let l := processLoss o d t s (f.broadcast t ω)
    (∑ j,probability o d t s j*l j)-l k≤0 := by
  let o := maps (K:=K) H L R cs rs hR
  let s := state H L R cs rs hR d prior f t ω
  let a := confidence o d s
  let r := CNDProcess.radius o d s
  let q := suggestion d t s
  let p := probability o d t s
  have hr := radius_isCND H L R cs rs hR d prior f hH hL hrs t ω
  have hp : p ∈ CND.simplex := o.prox_simplex _
  have hmin := extendedProx_minimizes 0 le_rfl (a,(r,q)) hr
  have hs : (∑ j,p j*(CNDMatrixProx.prediction a r p j+f.broadcast t ω j))≤
      ∑ j,p j*(CNDMatrixProx.prediction a r p k+f.broadcast t ω k) := by
    apply sum_le_sum
    intro j _
    by_cases hj : p j=0
    · simp [hj]
    · have hjp : 0<p j := lt_of_le_of_ne (hp.1 j) (Ne.symm hj)
      have hg := CNDMatrixProx.minimizer_support_bound a r q p 0 hr.1 hr.2.1 le_rfl hp hmin j k hjp
      have hpub := hb k j
      have hdiff := CNDMatrixProx.prediction_difference a r p j k
      exact mul_le_mul_of_nonneg_left (by linarith) (hp.1 j)
  rw [←sum_mul,hp.2,one_mul] at hs
  exact sub_nonpos.mpr hs

theorem proxy_interval_nonpos (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0)
    (u n : ℕ) (hu : u+n≤T) (k : Fin K) (ω : Ω) :
    (∑ t ∈ range n,
      ((∑ j,ExponentialStochastic.runProbability (maps H L R cs rs hR) d prior f (u+t) j ω*
        processLoss (maps H L R cs rs hR) d (u+t)
          (state H L R cs rs hR d prior f (u+t) ω) (f.broadcast (u+t) ω) j)-
       processLoss (maps H L R cs rs hR) d (u+t)
          (state H L R cs rs hR d prior f (u+t) ω) (f.broadcast (u+t) ω) k))≤0 := by
  apply sum_nonpos
  intro t ht
  exact proxy_nonpos H L R cs rs hR d prior f hH hL hrs (u+t) ω k
    (hb (u+t) (by have := mem_range.mp ht; omega) ω)

theorem actual_zero_width_branch (hd : d.W=0) (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (t : ℕ) (ω : Ω) (hb : ∀ i j,f.broadcast t ω j-f.broadcast t ω i≤0) :
    (state H L R cs rs hR d prior f t ω).2=prior ∧
    (∀ i,suggestion d t (state H L R cs rs hR d prior f t ω) i=(K:ℝ)⁻¹) ∧
    (∀ k,let o := maps (K:=K) H L R cs rs hR
      let s := state H L R cs rs hR d prior f t ω
      let l := processLoss o d t s (f.broadcast t ω)
      (∑ j,probability o d t s j*l j)-l k≤0) := by
  refine ⟨run_experts_eq_prior _ d hd prior f t ω,?_,?_⟩
  · intro i
    simpa only [Fintype.card_fin] using run_suggestion_uniform _ d hd prior f t ω i
  · intro k
    exact proxy_nonpos H L R cs rs hR d prior f hH hL hrs t ω k hb

theorem center_measurable (T t : ℕ) (i : Fin K) :
    Measurable[ℱ t] (center H L R cs rs hR d prior f T t i) := by
  by_cases ht : t<T
  · have he : center H L R cs rs hR d prior f T t i=
        fun ω => confidence (maps H L R cs rs hR) d (state H L R cs rs hR d prior f t ω) i := by
      funext ω
      simp only [center,if_pos ht]
    rw [he]
    simpa only [state] using
      ExponentialStochastic.run_center_measurable (maps H L R cs rs hR) d prior f t i
  · have he : center H L R cs rs hR d prior f T t i=fun _ => 0 := by
      funext ω
      simp only [center,if_neg ht]
    rw [he]
    exact measurable_const

theorem radius_measurable (T t : ℕ) (i j : Fin K) :
    Measurable[ℱ t] (radius H L R cs rs hR d prior f T t i j) := by
  by_cases ht : t<T
  · have he : radius H L R cs rs hR d prior f T t i j=
        fun ω => CNDProcess.radius (maps H L R cs rs hR) d
          (state H L R cs rs hR d prior f t ω) i j := by
      funext ω
      simp only [radius,if_pos ht]
    rw [he]
    simpa only [state] using
      ExponentialStochastic.run_radius_measurable (maps H L R cs rs hR) d prior f t i j
  · have he : radius H L R cs rs hR d prior f T t i j=fun _ => 0 := by
      funext ω
      simp only [radius,if_neg ht]
    rw [he]
    exact measurable_const

section Physical
variable {θ : Fin K → ℝ} {M D : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (m : CNDProbability.M1Model ℱ μ θ R M D)

/-- Only original feedback/stopping identifications. No expert regret,
positivity, active-root, confidence-coverage or span conclusion is a field. -/
structure Bridge (T : ℕ) : Prop where
  p_before : ∀ t<T,m.p t=ExponentialStochastic.runProbability (maps H L R cs rs hR) d prior f t
  broadcast_before : ∀ t<T,∀ ω i,f.broadcast t ω i=m.publicCost t i ω+m.error t i ω
  public_after : ∀ t,¬t<T → m.publicCost t=fun _ _ => 0
  error_after : ∀ t,¬t<T → m.error t=fun _ _ => 0

variable (hm : Bridge H L R cs rs hR d prior f m T)
include hm

theorem loss_before (t : ℕ) (ht : t<T) (ω : Ω) (i : Fin K) :
    ExponentialPhysical.loss m (center H L R cs rs hR d prior f T)
      (radius H L R cs rs hR d prior f T) t i ω=
    processLoss (maps H L R cs rs hR) d t (state H L R cs rs hR d prior f t ω)
      (f.broadcast t ω) i := by
  have hp := hm.p_before t ht
  simp only [ExponentialPhysical.loss,center,radius,if_pos ht,hp,
    CNDPhysicalRegret.surrogate,CNDPhysicalRegret.proxy,CNDPhysicalRegret.broadcast,
    CNDPhysicalRegret.avg,CNDPhysicalRegret.rowRadius]
  let o := maps (K:=K) H L R cs rs hR
  let s := state H L R cs rs hR d prior f t ω
  change (confidence o d s i-(∑ j,probability o d t s j*confidence o d s j)-
    (∑ j,probability o d t s j*CNDProcess.radius o d s i j))+
    (m.publicCost t i ω+m.error t i ω)=
    (confidence o d s i-(∑ j,CNDProcess.radius o d s i j*probability o d t s j)-
      (∑ j,probability o d t s j*confidence o d s j))+f.broadcast t ω i
  rw [hm.broadcast_before t ht ω i]
  have hmul : (∑ j,CNDProcess.radius o d s i j*probability o d t s j)=
      ∑ j,probability o d t s j*CNDProcess.radius o d s i j :=
    sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [hmul]
  ring

theorem loss_after (t : ℕ) (ht : ¬t<T) (ω : Ω) (i : Fin K) :
    ExponentialPhysical.loss m (center H L R cs rs hR d prior f T)
      (radius H L R cs rs hR d prior f T) t i ω=0 := by
  simp [ExponentialPhysical.loss,center,radius,ht,hm.public_after t ht,hm.error_after t ht,
    CNDPhysicalRegret.surrogate,CNDPhysicalRegret.proxy,CNDPhysicalRegret.broadcast,
    CNDPhysicalRegret.avg,CNDPhysicalRegret.rowRadius]

theorem physical_proxy_interval_nonpos (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0)
    (u n : ℕ) (hu : u+n≤T) (k : Fin K) (ω : Ω) :
    CNDPayment.intervalSum (ExponentialPhysical.proxyRegret m
      (center H L R cs rs hR d prior f T) (radius H L R cs rs hR d prior f T) k) u n ω≤0 := by
  apply sum_nonpos
  intro t ht
  have htt : u+t<T := by have := mem_range.mp ht; omega
  simp only [ExponentialPhysical.proxyRegret]
  simp_rw [loss_before H L R cs rs hR d prior f m hm (u+t) htt]
  rw [hm.p_before (u+t) htt]
  exact proxy_nonpos H L R cs rs hR d prior f hH hL hrs (u+t) ω k (hb (u+t) htt ω)

theorem support_span_zero (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0) :
    ∀ t ω i j,0<m.p t i ω → 0<m.p t j ω →
      |ExponentialPhysical.loss m (center H L R cs rs hR d prior f T)
          (radius H L R cs rs hR d prior f T) t i ω-
       ExponentialPhysical.loss m (center H L R cs rs hR d prior f T)
          (radius H L R cs rs hR d prior f T) t j ω|≤2*0 := by
  intro t ω i j hi hj
  by_cases ht : t<T
  · rw [loss_before H L R cs rs hR d prior f m hm t ht ω i,
      loss_before H L R cs rs hR d prior f m hm t ht ω j]
    let o := maps (K:=K) H L R cs rs hR
    let s := state H L R cs rs hR d prior f t ω
    have hp : probability o d t s ∈ CND.simplex := o.prox_simplex _
    rw [hm.p_before t ht] at hi hj
    have hh := ExponentialSGFinite.support_span_of_proxy_nonpos (probability o d t s)
      (processLoss o d t s (f.broadcast t ω)) hp.1 hp.2
      (fun k => proxy_nonpos H L R cs rs hR d prior f hH hL hrs t ω k (hb t ht ω)) i j hi hj
    simpa only [mul_zero] using hh
  · rw [loss_after H L R cs rs hR d prior f m hm t ht ω i,
      loss_after H L R cs rs hR d prior f m hm t ht ω j]
    norm_num

theorem e12_on_event (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0)
    (δa δe : ℝ) (ω : Ω)
    (hω : ExponentialPhysical.Event m (center H L R cs rs hR d prior f T)
      (radius H L R cs rs hR d prior f T) 0 T δa δe ω)
    (u n : ℕ) (hu : u+n≤T) (hn : 0<n) (k : Fin K) :
    CNDPayment.intervalSum (fun t ω => ExponentialPhysical.physical m t (m.action t ω) ω-
      ExponentialPhysical.physical m t k ω) u n ω≤
    ExponentialPhysical.encodingBound (ι:=Fin K) (D:=D) T n δe+
      CNDPayment.intervalSum (ExponentialPhysical.payment m
        (radius H L R cs rs hR d prior f T)) u n ω := by
  have hh := ExponentialPhysical.e12_on_event m (center H L R cs rs hR d prior f T)
    (radius H L R cs rs hR d prior f T) 0 T δa δe (fun _ _ _ _ => 0)
    (physical_proxy_interval_nonpos H L R cs rs hR d prior f m hm hH hL hrs hb)
    ω hω u n hu hn k
  simpa [ExponentialPhysical.actionBound] using hh

theorem e13_on_event (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0)
    (δa δe : ℝ) (ω : Ω)
    (hω : ExponentialPhysical.Event m (center H L R cs rs hR d prior f T)
      (radius H L R cs rs hR d prior f T) 0 T δa δe ω)
    (P : Intervals.Partition (range T)) (start len : ℕ → ℕ)
    (hblocks : ∀ j∈P.labels,P.block j=Ico (start j) (start j+len j))
    (hends : ∀ j∈P.labels,start j+len j≤T) (hlens : ∀ j∈P.labels,0<len j)
    (path : ℕ → Fin K) (arm : ℕ → Fin K)
    (hconst : ∀ j∈P.labels,∀ t∈P.block j,path t=arm j) :
    (∑ t∈range T,(ExponentialPhysical.physical m t (m.action t ω) ω-
      ExponentialPhysical.physical m t (path t) ω))≤
    ExponentialPhysical.noiseCoefficient (ι:=Fin K) (D:=D) 0 T δa δe*
      Real.sqrt ((T:ℝ)*(P.labels.card:ℝ))+
      CNDPayment.intervalSum (ExponentialPhysical.payment m
        (radius H L R cs rs hR d prior f T)) 0 T ω := by
  have hh := ExponentialPhysical.e13_on_event m (center H L R cs rs hR d prior f T)
    (radius H L R cs rs hR d prior f T) (W:=0) le_rfl T δa δe (fun _ _ _ _ => 0)
    (physical_proxy_interval_nonpos H L R cs rs hR d prior f m hm hH hL hrs hb)
    ω hω P start len hblocks hends hlens path arm hconst
  simpa only [sum_const_zero,zero_add] using hh

/-- The arbitrary actual-radius branch. The confidence shortfall is recorded
explicitly; E11 is neither assumed nor obtained by changing the algorithm. -/
theorem common_event_with_gap (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0)
    {δa δe : ℝ} (hδa : 0<δa) (hδa1 : δa<1) (hδe : 0<δe) (hδe1 : δe<1) :
    ∃ G : Set Ω,MeasurableSet G ∧ μ.real Gᶜ≤δa+δe ∧ ∀ ω∈G,
      ExponentialPhysical.Event m (center H L R cs rs hR d prior f T)
        (ExponentialGap.analysisRadius (θ:=θ) (center H L R cs rs hR d prior f T)
          (radius H L R cs rs hR d prior f T)) 0 T δa δe ω ∧
      (∀ u n,u+n≤T → 0<n → ∀ k : Fin K,
      CNDPayment.intervalSum (fun t ω => ExponentialPhysical.physical m t (m.action t ω) ω-
        ExponentialPhysical.physical m t k ω) u n ω≤
      ExponentialPhysical.encodingBound (ι:=Fin K) (D:=D) T n δe+
        CNDPayment.intervalSum (ExponentialPhysical.payment m
          (radius H L R cs rs hR d prior f T)) u n ω+
        ExponentialGap.gapLedger (θ:=θ) (center H L R cs rs hR d prior f T)
          (radius H L R cs rs hR d prior f T) u n ω) := by
  let a := center H L R cs rs hR d prior f T
  let r := radius H L R cs rs hR d prior f T
  have ha := center_measurable H L R cs rs hR d prior f T
  have hr := radius_measurable H L R cs rs hR d prior f T
  have hmr (t : ℕ) (i j : Fin K) :
      Measurable[ℱ t] (ExponentialGap.analysisRadius (θ:=θ) a r t i j) :=
    (hr t i j).add (ExponentialGap.gap_measurable a r ha hr t)
  obtain ⟨G,hG,hprob,hgood⟩ := ExponentialPhysical.common_event m a
    (ExponentialGap.analysisRadius (θ:=θ) a r) (W:=0) le_rfl T ha hmr
    (ExponentialGap.support_span_analysisRadius m a r 0
      (support_span_zero H L R cs rs hR d prior f m hm hH hL hrs hb))
    (δc:=0) hδa hδa1 hδe hδe1 Set.univ (by simp)
    (fun ω _ => ExponentialGap.analysisRadius_covers a r T ω)
  refine ⟨G,hG,by simpa using hprob,?_⟩
  intro ω hω
  refine ⟨hgood ω hω,?_⟩
  intro u n hu hn k
  have hx : ∀ u n,u+n≤T → ∀ k ω,
      CNDPayment.intervalSum (ExponentialPhysical.proxyRegret m a
        (ExponentialGap.analysisRadius (θ:=θ) a r) k) u n ω≤(0:ℝ) := by
    intro u n hu k ω
    simpa only [CNDPayment.intervalSum,ExponentialGap.proxyRegret_analysisRadius] using
      physical_proxy_interval_nonpos H L R cs rs hR d prior f m hm hH hL hrs hb u n hu k ω
  have hh := ExponentialPhysical.e12_on_event m a (ExponentialGap.analysisRadius (θ:=θ) a r)
    0 T δa δe (fun _ _ _ _ => 0) hx ω (hgood ω hω) u n hu hn k
  simpa only [ExponentialPhysical.actionBound,zero_mul,zero_add,
    ExponentialGap.payment_interval_analysisRadius,add_assoc] using hh

theorem e13_with_gap_on_event (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0)
    (δa δe : ℝ) (ω : Ω)
    (hω : ExponentialPhysical.Event m (center H L R cs rs hR d prior f T)
      (ExponentialGap.analysisRadius (θ:=θ) (center H L R cs rs hR d prior f T)
        (radius H L R cs rs hR d prior f T)) 0 T δa δe ω)
    (P : Intervals.Partition (range T)) (start len : ℕ → ℕ)
    (hblocks : ∀ j∈P.labels,P.block j=Ico (start j) (start j+len j))
    (hends : ∀ j∈P.labels,start j+len j≤T) (hlens : ∀ j∈P.labels,0<len j)
    (path : ℕ → Fin K) (arm : ℕ → Fin K)
    (hconst : ∀ j∈P.labels,∀ t∈P.block j,path t=arm j) :
    (∑ t∈range T,(ExponentialPhysical.physical m t (m.action t ω) ω-
      ExponentialPhysical.physical m t (path t) ω))≤
    ExponentialPhysical.noiseCoefficient (ι:=Fin K) (D:=D) 0 T δa δe*
      Real.sqrt ((T:ℝ)*(P.labels.card:ℝ))+
      CNDPayment.intervalSum (ExponentialPhysical.payment m
        (radius H L R cs rs hR d prior f T)) 0 T ω+
      ExponentialGap.gapLedger (θ:=θ) (center H L R cs rs hR d prior f T)
        (radius H L R cs rs hR d prior f T) 0 T ω := by
  let a := center H L R cs rs hR d prior f T
  let r := radius H L R cs rs hR d prior f T
  have hx : ∀ u n,u+n≤T → ∀ k ω,
      CNDPayment.intervalSum (ExponentialPhysical.proxyRegret m a
        (ExponentialGap.analysisRadius (θ:=θ) a r) k) u n ω≤(0:ℝ) := by
    intro u n hu k ω
    simpa only [CNDPayment.intervalSum,ExponentialGap.proxyRegret_analysisRadius] using
      physical_proxy_interval_nonpos H L R cs rs hR d prior f m hm hH hL hrs hb u n hu k ω
  have hh := ExponentialPhysical.e13_on_event m a (ExponentialGap.analysisRadius (θ:=θ) a r)
    (W:=0) le_rfl T δa δe (fun _ _ _ _ => 0) hx ω hω
    P start len hblocks hends hlens path arm hconst
  simpa only [sum_const_zero,zero_add,ExponentialGap.payment_interval_analysisRadius,add_assoc] using hh

end Physical

section SGPhysical
variable {θ : Fin K → ℝ} {M D σ σe : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (s : CNDProbability.SGModel ℱ μ θ R M D σ σe)
  (hs : Bridge H L R cs rs hR d prior f s.toM1Model T)
include hs

theorem sg_e12_on_event (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0)
    (ν : ℝ≥0) (δa δn : ℝ) (ω : Ω)
    (hω : ExponentialSGPhysical.Event s (center H L R cs rs hR d prior f T)
      (radius H L R cs rs hR d prior f T) ν 0 T δa δn ω)
    (u n : ℕ) (hu : u+n≤T) (hn : 0<n) (k : Fin K) :
    CNDPayment.intervalSum (fun t ω => ExponentialSGPhysical.physical s t (s.action t ω) ω-
      ExponentialSGPhysical.physical s t k ω) u n ω≤
    ExponentialSGPhysical.noiseBound (ι:=Fin K) ν T n δn+
      CNDPayment.intervalSum (ExponentialPhysical.payment s.toM1Model
        (radius H L R cs rs hR d prior f T)) u n ω := by
  have hh := ExponentialSGPhysical.e12_on_event s (center H L R cs rs hR d prior f T)
    (radius H L R cs rs hR d prior f T) ν 0 T δa δn (fun _ _ _ _ => 0)
    (physical_proxy_interval_nonpos H L R cs rs hR d prior f s.toM1Model hs hH hL hrs hb)
    ω hω u n hu hn k
  simpa [ExponentialPhysical.actionBound] using hh

theorem sg_e13_on_event (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0)
    (ν : ℝ≥0) (δa δn : ℝ) (ω : Ω)
    (hω : ExponentialSGPhysical.Event s (center H L R cs rs hR d prior f T)
      (radius H L R cs rs hR d prior f T) ν 0 T δa δn ω)
    (P : Intervals.Partition (range T)) (start len : ℕ → ℕ)
    (hblocks : ∀ j∈P.labels,P.block j=Ico (start j) (start j+len j))
    (hends : ∀ j∈P.labels,start j+len j≤T) (hlens : ∀ j∈P.labels,0<len j)
    (path : ℕ → Fin K) (arm : ℕ → Fin K)
    (hconst : ∀ j∈P.labels,∀ t∈P.block j,path t=arm j) :
    (∑ t∈range T,(ExponentialSGPhysical.physical s t (s.action t ω) ω-
      ExponentialSGPhysical.physical s t (path t) ω))≤
    ExponentialSGPhysical.noiseCoefficient (ι:=Fin K) ν 0 T δa δn*
      Real.sqrt ((T:ℝ)*(P.labels.card:ℝ))+
      CNDPayment.intervalSum (ExponentialPhysical.payment s.toM1Model
        (radius H L R cs rs hR d prior f T)) 0 T ω := by
  have hh := ExponentialSGPhysical.e13_on_event s (center H L R cs rs hR d prior f T)
    (radius H L R cs rs hR d prior f T) ν (W:=0) le_rfl T δa δn (fun _ _ _ _ => 0)
    (physical_proxy_interval_nonpos H L R cs rs hR d prior f s.toM1Model hs hH hL hrs hb)
    ω hω P start len hblocks hends hlens path arm hconst
  simpa only [sum_const_zero,zero_add] using hh

theorem sg_common_event_with_gap (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0)
    (ν : ℝ≥0) (hν : (ν:ℝ)^2=σ^2+σe^2)
    {δa δn : ℝ} (hδa : 0<δa) (hδa1 : δa<1) (hδn : 0<δn) (hδn1 : δn<1) :
    ∃ G : Set Ω,MeasurableSet G ∧ μ.real Gᶜ≤δa+δn ∧ ∀ ω∈G,
      ExponentialSGPhysical.Event s (center H L R cs rs hR d prior f T)
        (ExponentialGap.analysisRadius (θ:=θ) (center H L R cs rs hR d prior f T)
          (radius H L R cs rs hR d prior f T)) ν 0 T δa δn ω ∧
      (∀ u n,u+n≤T → 0<n → ∀ k : Fin K,
      CNDPayment.intervalSum (fun t ω => ExponentialSGPhysical.physical s t (s.action t ω) ω-
        ExponentialSGPhysical.physical s t k ω) u n ω≤
      ExponentialSGPhysical.noiseBound (ι:=Fin K) ν T n δn+
        CNDPayment.intervalSum (ExponentialPhysical.payment s.toM1Model
          (radius H L R cs rs hR d prior f T)) u n ω+
        ExponentialGap.gapLedger (θ:=θ) (center H L R cs rs hR d prior f T)
          (radius H L R cs rs hR d prior f T) u n ω) := by
  let a := center H L R cs rs hR d prior f T
  let r := radius H L R cs rs hR d prior f T
  have ha := center_measurable H L R cs rs hR d prior f T
  have hr := radius_measurable H L R cs rs hR d prior f T
  have hmr (t : ℕ) (i j : Fin K) :
      Measurable[ℱ t] (ExponentialGap.analysisRadius (θ:=θ) a r t i j) :=
    (hr t i j).add (ExponentialGap.gap_measurable a r ha hr t)
  obtain ⟨G,hG,hprob,hgood⟩ := ExponentialSGPhysical.common_event s a
    (ExponentialGap.analysisRadius (θ:=θ) a r) ν hν (W:=0) le_rfl T ha hmr
    (ExponentialGap.support_span_analysisRadius s.toM1Model a r 0
      (support_span_zero H L R cs rs hR d prior f s.toM1Model hs hH hL hrs hb))
    (δc:=0) hδa hδa1 hδn hδn1 Set.univ (by simp)
    (fun ω _ => ExponentialGap.analysisRadius_covers a r T ω)
  refine ⟨G,hG,by simpa using hprob,?_⟩
  intro ω hω
  refine ⟨hgood ω hω,?_⟩
  intro u n hu hn k
  have hx : ∀ u n,u+n≤T → ∀ k ω,
      CNDPayment.intervalSum (ExponentialPhysical.proxyRegret s.toM1Model a
        (ExponentialGap.analysisRadius (θ:=θ) a r) k) u n ω≤(0:ℝ) := by
    intro u n hu k ω
    simpa only [CNDPayment.intervalSum,ExponentialGap.proxyRegret_analysisRadius] using
      physical_proxy_interval_nonpos H L R cs rs hR d prior f s.toM1Model hs hH hL hrs hb u n hu k ω
  have hh := ExponentialSGPhysical.e12_on_event s a (ExponentialGap.analysisRadius (θ:=θ) a r)
    ν 0 T δa δn (fun _ _ _ _ => 0) hx ω (hgood ω hω) u n hu hn k
  simpa only [ExponentialPhysical.actionBound,zero_mul,zero_add,
    ExponentialGap.payment_interval_analysisRadius,add_assoc] using hh

theorem sg_e13_with_gap_on_event (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs)
    (hb : ∀ t<T,∀ ω i j,f.broadcast t ω j-f.broadcast t ω i≤0)
    (ν : ℝ≥0) (δa δn : ℝ) (ω : Ω)
    (hω : ExponentialSGPhysical.Event s (center H L R cs rs hR d prior f T)
      (ExponentialGap.analysisRadius (θ:=θ) (center H L R cs rs hR d prior f T)
        (radius H L R cs rs hR d prior f T)) ν 0 T δa δn ω)
    (P : Intervals.Partition (range T)) (start len : ℕ → ℕ)
    (hblocks : ∀ j∈P.labels,P.block j=Ico (start j) (start j+len j))
    (hends : ∀ j∈P.labels,start j+len j≤T) (hlens : ∀ j∈P.labels,0<len j)
    (path : ℕ → Fin K) (arm : ℕ → Fin K)
    (hconst : ∀ j∈P.labels,∀ t∈P.block j,path t=arm j) :
    (∑ t∈range T,(ExponentialSGPhysical.physical s t (s.action t ω) ω-
      ExponentialSGPhysical.physical s t (path t) ω))≤
    ExponentialSGPhysical.noiseCoefficient (ι:=Fin K) ν 0 T δa δn*
      Real.sqrt ((T:ℝ)*(P.labels.card:ℝ))+
      CNDPayment.intervalSum (ExponentialPhysical.payment s.toM1Model
        (radius H L R cs rs hR d prior f T)) 0 T ω+
      ExponentialGap.gapLedger (θ:=θ) (center H L R cs rs hR d prior f T)
        (radius H L R cs rs hR d prior f T) 0 T ω := by
  let a := center H L R cs rs hR d prior f T
  let r := radius H L R cs rs hR d prior f T
  have hx : ∀ u n,u+n≤T → ∀ k ω,
      CNDPayment.intervalSum (ExponentialPhysical.proxyRegret s.toM1Model a
        (ExponentialGap.analysisRadius (θ:=θ) a r) k) u n ω≤(0:ℝ) := by
    intro u n hu k ω
    simpa only [CNDPayment.intervalSum,ExponentialGap.proxyRegret_analysisRadius] using
      physical_proxy_interval_nonpos H L R cs rs hR d prior f s.toM1Model hs hH hL hrs hb u n hu k ω
  have hh := ExponentialSGPhysical.e13_on_event s a (ExponentialGap.analysisRadius (θ:=θ) a r)
    ν (W:=0) le_rfl T δa δn (fun _ _ _ _ => 0) hx ω hω
    P start len hblocks hends hlens path arm hconst
  simpa only [sum_const_zero,zero_add,ExponentialGap.payment_interval_analysisRadius,add_assoc] using hh
end SGPhysical

section FiniteBridge
variable {θ : Fin K → ℝ} {M D : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (h : BoundedInputs ℱ θ R M D T)
  (hp : ExponentialStochastic.FiniteLaws (maps H L R cs rs hR) d prior h (μ:=μ))

theorem bounded_broadcast_zero (B : ℝ) (hwidth : B+2*D=0)
    (hc : ∀ t<T,∀ ω i j,h.publicCost t j ω-h.publicCost t i ω≤B) :
    ∀ t<T,∀ ω i j,h.broadcast t ω j-h.broadcast t ω i≤0 := by
  intro t ht ω i j
  have hi := abs_le.mp (h.error_bound t ht i ω)
  have hj := abs_le.mp (h.error_bound t ht j ω)
  have hh := hc t ht ω i j
  dsimp only [BoundedInputs.broadcast]
  linarith

def bounded_bridge : Bridge H L R cs rs hR d prior h.extend.feedback
    (ExponentialStochastic.model (maps H L R cs rs hR) d prior h hp) T where
  p_before t ht := ExponentialStochastic.model_p _ _ _ _ hp ht
  broadcast_before t ht ω i := by
    rw [ExponentialStochastic.model_public _ _ _ _ hp ht,
      ExponentialStochastic.model_error _ _ _ _ hp ht]
    change h.extend.broadcast t ω i=h.publicCost t i ω+h.error t i ω
    rw [h.extend_broadcast ht]
    rfl
  public_after t ht := by
    funext i ω
    simp only [ExponentialStochastic.model,Primitive.stopped,ExponentialStochastic.primitive,
      BoundedInputs.extend,if_neg ht]
  error_after t ht := by
    funext i ω
    simp only [ExponentialStochastic.model,Primitive.stopped,ExponentialStochastic.primitive,
      BoundedInputs.extend,if_neg ht]
end FiniteBridge

section SGFiniteBridge
variable {θ : Fin K → ℝ} {M D σ σe : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (h : SGInputs ℱ θ R M D T)
  (hp : ExponentialSGStochastic.FiniteLaws (maps H L R cs rs hR) d prior h
    (μ:=μ) (σ:=σ) (σe:=σe))

theorem sg_broadcast_zero (B : ℝ) (hwidth : B+2*D=0)
    (hc : ∀ t<T,∀ ω i j,h.publicCost t j ω-h.publicCost t i ω≤B) :
    ∀ t<T,∀ ω i j,h.broadcast t ω j-h.broadcast t ω i≤0 := by
  intro t ht ω i j
  have hi := abs_le.mp (h.error_bound t ht i ω)
  have hj := abs_le.mp (h.error_bound t ht j ω)
  have hh := hc t ht ω i j
  dsimp only [SGInputs.broadcast]
  linarith

def sg_bridge : Bridge H L R cs rs hR d prior h.extend.feedback
    (ExponentialSGStochastic.model (maps H L R cs rs hR) d prior h hp).toM1Model T where
  p_before t ht := ExponentialSGStochastic.model_p _ _ _ _ hp ht
  broadcast_before t ht ω i := by
    rw [ExponentialSGStochastic.model_public _ _ _ _ hp ht,
      ExponentialSGStochastic.model_error _ _ _ _ hp ht]
    change h.extend.broadcast t ω i=h.publicCost t i ω+h.error t i ω
    rw [h.extend_broadcast ht]
    rfl
  public_after t ht := by
    funext i ω
    simp only [ExponentialSGStochastic.model,ExponentialSGStochastic.publicShadow,
      Primitive.stopped,ExponentialSGStochastic.primitive,SGInputs.extend,if_neg ht]
  error_after t ht := by
    funext i ω
    simp only [ExponentialSGStochastic.model,ExponentialSGStochastic.publicShadow,
      Primitive.stopped,ExponentialSGStochastic.primitive,SGInputs.extend,if_neg ht]
end SGFiniteBridge

theorem zero_horizon_state (ω : Ω) :
    state H L R cs rs hR d prior f 0 ω=ExponentialStochastic.initial prior := rfl

theorem zero_horizon_accumulators {θ : Fin K → ℝ} {M D : ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (m : CNDProbability.M1Model ℱ μ θ R M D) (ω : Ω) :
    (∀ path : ℕ → Fin K,(∑ t∈range 0,(ExponentialPhysical.physical m t (m.action t ω) ω-
      ExponentialPhysical.physical m t (path t) ω))=0) ∧
    (∀ k : Fin K,CNDPayment.intervalSum (fun t ω =>
      ExponentialPhysical.physical m t (m.action t ω) ω-ExponentialPhysical.physical m t k ω) 0 0 ω=0) ∧
    CNDPayment.intervalSum (ExponentialPhysical.payment m
      (radius H L R cs rs hR d prior f 0)) 0 0 ω=0 ∧
    ExponentialGap.gapLedger (θ:=θ) (center H L R cs rs hR d prior f 0)
      (radius H L R cs rs hR d prior f 0) 0 0 ω=0 := by
  simp [CNDPayment.intervalSum,ExponentialGap.gapLedger]

theorem zero_horizon_sg_accumulators {θ : Fin K → ℝ} {M D σ σe : ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (s : CNDProbability.SGModel ℱ μ θ R M D σ σe) (ω : Ω) :
    (∀ path : ℕ → Fin K,(∑ t∈range 0,(ExponentialSGPhysical.physical s t (s.action t ω) ω-
      ExponentialSGPhysical.physical s t (path t) ω))=0) ∧
    (∀ k : Fin K,CNDPayment.intervalSum (fun t ω =>
      ExponentialSGPhysical.physical s t (s.action t ω) ω-ExponentialSGPhysical.physical s t k ω) 0 0 ω=0) ∧
    CNDPayment.intervalSum (ExponentialPhysical.payment s.toM1Model
      (radius H L R cs rs hR d prior f 0)) 0 0 ω=0 ∧
    ExponentialGap.gapLedger (θ:=θ) (center H L R cs rs hR d prior f 0)
      (radius H L R cs rs hR d prior f 0) 0 0 ω=0 := by
  simp [CNDPayment.intervalSum,ExponentialGap.gapLedger]

section Singleton
variable {θ : Fin 1 → ℝ} {M D : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (m : CNDProbability.M1Model ℱ μ θ R M D)

theorem singleton_probability (o : DecisionMaps (Fin 1)) (d : ExpertData (Fin 1) E)
    (prior : E → ℝ) (f : Feedback (ι:=Fin 1) ℱ) (t : ℕ) (ω : Ω) (i : Fin 1) :
    ExponentialStochastic.runProbability o d prior f t i ω=1 := by
  have hs := (ExponentialStochastic.runProbability_simplex o d prior f t ω).2
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  simpa using hs

theorem singleton_actual_radius (W : ℝ) (hW : 0≤W)
    (d : ExpertData (Fin 1) E) (prior : E → ℝ) (f : Feedback (ι:=Fin 1) ℱ)
    (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs) (t : ℕ) (ω : Ω) :
    let o := ExponentialScaledMaps.decisionMaps H L R W cs rs hR hW
    CNDProcess.radius o d (ExponentialStochastic.run o d prior f t ω)=0 := by
  let o := ExponentialScaledMaps.decisionMaps (K:=1) H L R W cs rs hR hW
  have hr := ExponentialGeometry.run_scaled_radius_isCND H L R W cs rs hR hW hrs
    d prior f hH hL t ω
  funext i j
  rw [Subsingleton.elim j i]
  exact hr.2.1 i

theorem singleton_actual_payment (W : ℝ) (hW : 0≤W)
    (d : ExpertData (Fin 1) E) (prior : E → ℝ) (f : Feedback (ι:=Fin 1) ℱ)
    (hH : 0≤H) (hL : 0≤L) (hrs : 0≤rs) (t : ℕ) (ω : Ω) (A : Fin 1) :
    let o := ExponentialScaledMaps.decisionMaps H L R W cs rs hR hW
    CNDPhysicalRegret.payment (CNDProcess.radius o d (ExponentialStochastic.run o d prior f t ω))
      (fun i => ExponentialStochastic.runProbability o d prior f t i ω) A=0 := by
  simp only [singleton_actual_radius H L R cs rs hR W hW d prior f hH hL hrs t ω,
    CNDPhysicalRegret.payment,CNDPhysicalRegret.rowRadius,Pi.zero_apply,mul_zero,sum_const_zero]

theorem singleton_interval (u n : ℕ) (k : Fin 1) (ω : Ω) :
    CNDPayment.intervalSum (fun t ω => ExponentialPhysical.physical m t (m.action t ω) ω-
      ExponentialPhysical.physical m t k ω) u n ω=0 := by
  apply sum_eq_zero
  intro t ht
  dsimp only
  rw [Subsingleton.elim (m.action (u+t) ω) k,sub_self]

theorem singleton_path (T : ℕ) (path : ℕ → Fin 1) (ω : Ω) :
    (∑ t ∈ range T,(ExponentialPhysical.physical m t (m.action t ω) ω-
      ExponentialPhysical.physical m t (path t) ω))=0 := by
  apply sum_eq_zero
  intro t ht
  rw [Subsingleton.elim (m.action t ω) (path t),sub_self]

theorem singleton_sg_interval {σ σe : ℝ} (s : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (u n : ℕ) (k : Fin 1) (ω : Ω) :
    CNDPayment.intervalSum (fun t ω => ExponentialSGPhysical.physical s t (s.action t ω) ω-
      ExponentialSGPhysical.physical s t k ω) u n ω=0 := by
  apply sum_eq_zero
  intro t ht
  dsimp only
  rw [Subsingleton.elim (s.action (u+t) ω) k,sub_self]

theorem singleton_sg_path {σ σe : ℝ} (s : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (T : ℕ) (path : ℕ → Fin 1) (ω : Ω) :
    (∑ t ∈ range T,(ExponentialSGPhysical.physical s t (s.action t ω) ω-
      ExponentialSGPhysical.physical s t (path t) ω))=0 := by
  apply sum_eq_zero
  intro t ht
  rw [Subsingleton.elim (s.action t ω) (path t),sub_self]

theorem singleton_actual_bounded_model (o : DecisionMaps (Fin 1))
    (d : ExpertData (Fin 1) E) (prior : E → ℝ) (h : BoundedInputs ℱ θ R M D T)
    (hp : ExponentialStochastic.FiniteLaws o d prior h (μ:=μ)) (ω : Ω) :
    let a := ExponentialStochastic.model o d prior h hp
    (∀ u n k,CNDPayment.intervalSum (fun t ω => ExponentialPhysical.physical a t (a.action t ω) ω-
      ExponentialPhysical.physical a t k ω) u n ω=0) ∧
    (∀ path : ℕ → Fin 1,(∑ t∈range T,(ExponentialPhysical.physical a t (a.action t ω) ω-
      ExponentialPhysical.physical a t (path t) ω))=0) := by
  exact ⟨fun u n k => singleton_interval R _ u n k ω,fun path => singleton_path R _ T path ω⟩

theorem singleton_actual_sg_model {σ σe : ℝ} (o : DecisionMaps (Fin 1))
    (d : ExpertData (Fin 1) E) (prior : E → ℝ) (h : SGInputs ℱ θ R M D T)
    (hp : ExponentialSGStochastic.FiniteLaws o d prior h (μ:=μ) (σ:=σ) (σe:=σe)) (ω : Ω) :
    let a := ExponentialSGStochastic.model o d prior h hp
    (∀ u n k,CNDPayment.intervalSum (fun t ω => ExponentialSGPhysical.physical a t (a.action t ω) ω-
      ExponentialSGPhysical.physical a t k ω) u n ω=0) ∧
    (∀ path : ℕ → Fin 1,(∑ t∈range T,(ExponentialSGPhysical.physical a t (a.action t ω) ω-
      ExponentialSGPhysical.physical a t (path t) ω))=0) := by
  exact ⟨fun u n k => singleton_sg_interval R _ u n k ω,fun path => singleton_sg_path R _ T path ω⟩
end Singleton

end Part2.ExponentialZeroWidth

#print axioms Part2.ExponentialZeroWidth.suggestion_uniform
#print axioms Part2.ExponentialZeroWidth.step_experts_unchanged
#print axioms Part2.ExponentialZeroWidth.rawRun_experts_eq_prior
#print axioms Part2.ExponentialZeroWidth.run_experts_eq_prior
#print axioms Part2.ExponentialZeroWidth.run_suggestion_uniform
#print axioms Part2.ExponentialZeroWidth.radius_isCND
#print axioms Part2.ExponentialZeroWidth.proxy_nonpos
#print axioms Part2.ExponentialZeroWidth.proxy_interval_nonpos
#print axioms Part2.ExponentialZeroWidth.actual_zero_width_branch
#print axioms Part2.ExponentialZeroWidth.center_measurable
#print axioms Part2.ExponentialZeroWidth.radius_measurable
#print axioms Part2.ExponentialZeroWidth.loss_before
#print axioms Part2.ExponentialZeroWidth.loss_after
#print axioms Part2.ExponentialZeroWidth.physical_proxy_interval_nonpos
#print axioms Part2.ExponentialZeroWidth.support_span_zero
#print axioms Part2.ExponentialZeroWidth.e12_on_event
#print axioms Part2.ExponentialZeroWidth.e13_on_event
#print axioms Part2.ExponentialZeroWidth.common_event_with_gap
#print axioms Part2.ExponentialZeroWidth.e13_with_gap_on_event
#print axioms Part2.ExponentialZeroWidth.sg_e12_on_event
#print axioms Part2.ExponentialZeroWidth.sg_e13_on_event
#print axioms Part2.ExponentialZeroWidth.sg_common_event_with_gap
#print axioms Part2.ExponentialZeroWidth.sg_e13_with_gap_on_event
#print axioms Part2.ExponentialZeroWidth.bounded_broadcast_zero
#print axioms Part2.ExponentialZeroWidth.sg_broadcast_zero
#print axioms Part2.ExponentialZeroWidth.singleton_probability
#print axioms Part2.ExponentialZeroWidth.singleton_actual_radius
#print axioms Part2.ExponentialZeroWidth.singleton_actual_payment
#print axioms Part2.ExponentialZeroWidth.singleton_interval
#print axioms Part2.ExponentialZeroWidth.singleton_path
#print axioms Part2.ExponentialZeroWidth.singleton_sg_interval
#print axioms Part2.ExponentialZeroWidth.singleton_sg_path
#print axioms Part2.ExponentialZeroWidth.singleton_actual_bounded_model
#print axioms Part2.ExponentialZeroWidth.singleton_actual_sg_model
#print axioms Part2.ExponentialZeroWidth.zero_horizon_state
#print axioms Part2.ExponentialZeroWidth.zero_horizon_accumulators
#print axioms Part2.ExponentialZeroWidth.zero_horizon_sg_accumulators
