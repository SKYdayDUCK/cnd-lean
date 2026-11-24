import staging.cnd20261026.«fix-bounded-sg».ExponentialStatistics
import staging.cnd20261026.«fix-bounded-sg».ExponentialScaledMaps

/-! Shared bounded/SG geometry for the same measurable exponential run.
Only the raw feedback vector's span is an input; all probability, transport
and support properties follow from the actual canonical maps and positive q. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 2400000
namespace Part2.ExponentialGeometry
open CNDProcess
variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

structure Config (T : ℕ) (R W : ℝ) where
  data : ExpertData (Fin K) E
  prior : E → ℝ
  width_eq : data.W = W
  range_eq : data.R = R
  eta_pos : ∀ e, 0 < data.eta e
  prior_pos : ∀ e, 0 < prior e
  root : Fin K → E
  root_arm : ∀ k, data.arm (root k) = k
  root_awake : ∀ t<T, ∀ k, root k ∈ activeSet data t
  confidence_scale : ℝ := 1
  radius_scale : ℝ := 1
  confidence_nonneg : 0 ≤ confidence_scale
  radius_nonneg : 0 ≤ radius_scale

def maps (H L R W : ℝ) (hR : 0 ≤ R) (hW : 0 ≤ W) (c : Config (K := K) (E := E) T R W) :
    DecisionMaps (Fin K) :=
  ExponentialScaledMaps.decisionMaps H L R W c.confidence_scale c.radius_scale hR hW

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}

theorem scaled_actual_radius_isCND (p : ℕ → Fin K → ℝ) (hp : ∀ t, p t ∈ CND.simplex)
    (n : ℕ) (H L R scale : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) (hs : 0 ≤ scale) :
    CND.IsCND (fun i j => CNDPhysical.saturatedRadius R
      (scale * CNDPhysical.pairRadius p n H L R i j)) := by
  have hd := CNDPhysical.actual_resistance_isCND p hp n
  have hr : CND.IsCND (CNDPhysical.pairRadius p n H L R) := by
    have hc := CNDSaturation.sqrt_linear_isCND _ hd
      (2*H*Real.sqrt L) (4*H*L+R*Fintype.card (Fin K)) (by positivity) (by positivity)
    convert hc using 1
    funext i j
    unfold CNDPhysical.pairRadius
    rw [Real.sqrt_mul hL]
    ring
  have hscaled := CNDSaturation.cnd_scale _ hr scale hs
  have ht := CNDSaturation.exponential_saturation_isCND _ hscaled
    (2*R/CNDPhysical.c0) (1/R)
    (div_nonneg (by positivity) CNDPhysical.c0_pos.le) (div_nonneg (by norm_num) hR)
  convert ht using 1
  funext i j
  unfold CNDPhysical.saturatedRadius
  congr 2
  ring

/-- Geometry of any actual exponential run, including W=0 and arbitrary
unused learning rates or priors. No expert-library positivity is needed. -/
theorem run_scaled_radius_isCND (H L R W cs rs : ℝ) (hR : 0≤R) (hW : 0≤W) (hrs : 0≤rs)
    (d : ExpertData (Fin K) E) (prior : E → ℝ) (f : Feedback (ι := Fin K) ℱ)
    (hH : 0≤H) (hL : 0≤L) (t : ℕ) (ω : Ω) :
    let o := ExponentialScaledMaps.decisionMaps (K := K) H L R W cs rs hR hW
    CND.IsCND (CNDProcess.radius o d (ExponentialStochastic.run o d prior f t ω)) := by
  let o := ExponentialScaledMaps.decisionMaps (K := K) H L R W cs rs hR hW
  change CND.IsCND (CNDProcess.radius o d (ExponentialStochastic.run o d prior f t ω))
  by_cases hz : d.R=0
  · simp [CNDProcess.radius,hz,CND.IsCND,CND.ConditionallyNegative,CND.quadratic]
  · rw [CNDProcess.radius,if_neg hz]
    change CND.IsCND (fun i j => CNDPhysical.saturatedRadius R
      (rs * StatisticalMaps.rawPairRadius H L R (ExponentialStochastic.run o d prior f t ω).1 i j))
    rw [ExponentialStochastic.computed_rawPairRadius_eq_actual _ _ _ _ hz]
    exact scaled_actual_radius_isCND _
      (fun n => ExponentialStochastic.runProbability_simplex _ _ _ _ n ω) t H L R rs hH hL hR hrs

variable (H L R W : ℝ) (hR : 0 ≤ R) (hW : 0 ≤ W)
  (c : Config (K := K) (E := E) T R W) (f : Feedback (ι := Fin K) ℱ)

def state (t : ℕ) (ω : Ω) : State (Fin K) E :=
  ExponentialStochastic.run (maps H L R W hR hW c) c.data c.prior f t ω

theorem concrete_radius_isCND (hH : 0 ≤ H) (hL : 0 ≤ L) (t : ℕ) (ω : Ω) :
    CND.IsCND (CNDProcess.radius (maps H L R W hR hW c) c.data (state H L R W hR hW c f t ω)) := by
  exact run_scaled_radius_isCND H L R W c.confidence_scale c.radius_scale hR hW c.radius_nonneg
    c.data c.prior f hH hL t ω

theorem raw_geometry (hH : 0 ≤ H) (hL : 0 ≤ L) (hWpos : 0 < W)
    (hb : ∀ t<T, ∀ ω i j, f.broadcast t ω j - f.broadcast t ω i ≤ W)
    (t : ℕ) (ht : t<T) (ω : Ω) :
    let o := maps H L R W hR hW c
    let s := state H L R W hR hW c f t ω
    let q := suggestion c.data t s
    let p := probability o c.data t s
    let m := transport o c.data t s
    let l := processLoss o c.data t s (f.broadcast t ω)
    (∀ j, (∑ i, q i * m i j) = p j) ∧ (∀ i j, 0 ≤ m i j) ∧
    (∀ i, (∑ j, m i j) = 1) ∧ (∀ i j, 0 < m i j → 0 < p j) ∧
    (∀ k, (∑ j, m k j * l j) ≤ l k) ∧
    (∀ i j, 0 < p i → 0 < p j → |l i-l j| ≤ 2*W) := by
  let o := maps H L R W hR hW c
  let s := state H L R W hR hW c f t ω
  let a := confidence o c.data s
  let r := CNDProcess.radius o c.data s
  let q := suggestion c.data t s
  let p := probability o c.data t s
  let m := transport o c.data t s
  let b := f.broadcast t ω
  have hw : c.data.W ≠ 0 := by rw [c.width_eq]; exact ne_of_gt hWpos
  have hq : q ∈ CND.simplex := ExponentialStochastic.run_suggestion_simplex
    o c.data c.prior f c.prior_pos c.eta_pos hw t ω
    ⟨c.root CNDHorizon.root,c.root_awake t ht _⟩
  have hqp (k : Fin K) : 0 < q k := ExponentialStochastic.run_suggestion_positive
    o c.data c.prior f c.prior_pos c.eta_pos hw t ω k (c.root k) (c.root_awake t ht k) (c.root_arm k)
  have hp : p ∈ CND.simplex := o.prox_simplex _
  have hr : CND.IsCND r := concrete_radius_isCND H L R W hR hW c f hH hL t ω
  have hmin := extendedProx_minimizes W hW (a,(r,q)) hr
  have hM : ∀ i j, 0 ≤ m i j := ExactGreedyTransport.exactRemap_nonneg q p _ W univ_nonempty hq.1 hp.1
  have hrow : ∀ i, (∑ j, m i j) = 1 :=
    ExactGreedyTransport.exactRemap_row_sum q p _ W univ_nonempty (hq.2.trans hp.2.symm)
  have hcons : ∀ j, (∑ i, q i*m i j) = p j :=
    ExactGreedyTransport.exactRemap_consistent q p _ W univ_nonempty hq.1 hp.1 (hq.2.trans hp.2.symm)
  have hsupp (i j : Fin K) (hij : 0 < m i j) : 0 < p j := by
    have hs := single_le_sum (fun k _ => mul_nonneg (hq.1 k) (hM k j)) (mem_univ i)
    rw [hcons] at hs
    exact (mul_pos (hqp i) hij).trans_le hs
  refine ⟨hcons,hM,hrow,hsupp,?_,?_⟩
  · intro k
    apply CNDProd.allowed_row_dominates m (CNDMatrixProx.prediction a r p) b W hM hrow _ (hb t ht ω) k
    intro i j hij
    have hh := (ExactGreedyTransport.exactRemap_allowed a r q p W hr hW hq hp hmin univ_nonempty i j hij).2
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by rw [CNDMatrixProx.prediction_difference]; exact hh)
  · exact CNDMatrixProx.minimizer_public_support_span a r q p b W hr hW hp hmin (hb t ht ω)

theorem zero_width_proxy_nonpos (hH : 0 ≤ H) (hL : 0 ≤ L) (hw0 : W=0)
    (t : ℕ) (ω : Ω) (k : Fin K)
    (hb : ∀ i j, f.broadcast t ω j - f.broadcast t ω i ≤ W) :
    let o := maps H L R W hR hW c
    let s := state H L R W hR hW c f t ω
    let l := processLoss o c.data t s (f.broadcast t ω)
    (∑ j, probability o c.data t s j*l j) - l k ≤ 0 := by
  let o := maps H L R W hR hW c
  let s := state H L R W hR hW c f t ω
  let a := confidence o c.data s
  let r := CNDProcess.radius o c.data s
  let q := suggestion c.data t s
  let p := probability o c.data t s
  have hr := concrete_radius_isCND H L R W hR hW c f hH hL t ω
  have hp : p ∈ CND.simplex := o.prox_simplex _
  have hmin := extendedProx_minimizes W hW (a,(r,q)) hr
  have hs : (∑ j, p j*(CNDMatrixProx.prediction a r p j+f.broadcast t ω j)) ≤
      ∑ j, p j*(CNDMatrixProx.prediction a r p k+f.broadcast t ω k) := by
    apply sum_le_sum
    intro j _
    by_cases hj : p j=0
    · simp [hj]
    · have hjp : 0 < p j := lt_of_le_of_ne (hp.1 j) (Ne.symm hj)
      have hg := CNDMatrixProx.minimizer_support_bound a r q p W hr.1 hr.2.1 hW hp hmin j k hjp
      have hpub := hb k j
      have hdiff := CNDMatrixProx.prediction_difference a r p j k
      exact mul_le_mul_of_nonneg_left (by rw [hw0] at hg hpub; linarith) (hp.1 j)
  rw [← sum_mul,hp.2,one_mul] at hs
  exact sub_nonpos.mpr hs

#print axioms scaled_actual_radius_isCND
#print axioms run_scaled_radius_isCND
#print axioms raw_geometry
#print axioms zero_width_proxy_nonpos
end Part2.ExponentialGeometry
