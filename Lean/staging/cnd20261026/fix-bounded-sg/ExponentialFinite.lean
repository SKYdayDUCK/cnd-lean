import staging.cnd20261026.«fix-bounded-sg».ExponentialActual

/-! Concrete bounded finite-feedback exponential algorithm. All canonical
geometry and expert-update obligations use the shared actual-run layer. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 2400000
namespace Part2.ExponentialFinite
open CNDProcess CNDHorizon
variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
  {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}
  {θ : Fin K → ℝ} {R M D W : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]

abbrev Config (T : ℕ) (R W : ℝ) := ExponentialGeometry.Config (K := K) (E := E) T R W
variable (h : BoundedInputs ℱ θ R M D T) (L : ℝ) (hW : 0<W)
  (c : Config (K := K) (E := E) T R W)
def maps : DecisionMaps (Fin K) := ExponentialGeometry.maps (R+M+D) L R W h.R_nonneg hW.le c
def state (t : ℕ) (ω : Ω) : State (Fin K) E :=
  ExponentialStochastic.run (maps h L hW c) c.data c.prior h.extend.feedback t ω
abbrev Protocol := ExponentialStochastic.FiniteLaws (maps h L hW c) c.data c.prior h (μ := μ)
def model (hm : Protocol h L hW c (μ := μ)) : CNDProbability.M1Model ℱ μ θ R M D :=
  ExponentialStochastic.model (maps h L hW c) c.data c.prior h hm
def center (t : ℕ) (i : Fin K) (ω : Ω) : ℝ :=
  if t<T then confidence (maps h L hW c) c.data (state h L hW c t ω) i else 0
def radius (t : ℕ) (i j : Fin K) (ω : Ω) : ℝ :=
  if t<T then CNDProcess.radius (maps h L hW c) c.data (state h L hW c t ω) i j else 0
def trajectory : ExponentialComposition.Trajectory E (Fin K) Ω :=
  ExponentialActual.trajectory (R+M+D) L h.R_nonneg hW.le c h.extend.feedback

/-- Equalities of the original feedback and deterministic stopping fields. -/
def bridge (hm : Protocol h L hW c (μ := μ)) :
    ExponentialActual.Bridge (R+M+D) L h.R_nonneg hW.le c h.extend.feedback (model h L hW c hm) where
  p_before t ht := ExponentialStochastic.model_p (maps h L hW c) c.data c.prior h hm ht
  broadcast_before t ht ω i := by
    rw [show (model h L hW c hm).publicCost t=h.publicCost t from
      ExponentialStochastic.model_public _ _ _ _ hm ht,
      show (model h L hW c hm).error t=h.error t from ExponentialStochastic.model_error _ _ _ _ hm ht]
    change h.extend.broadcast t ω i=h.publicCost t i ω+h.error t i ω
    rw [h.extend_broadcast ht]
    rfl
  p_after t ht := by
    funext i ω
    simp only [model,ExponentialStochastic.model,Primitive.stopped,stopP,if_neg ht]
  public_after t ht := by
    funext i ω
    simp only [model,ExponentialStochastic.model,Primitive.stopped,if_neg ht]
  error_after t ht := by
    funext i ω
    simp only [model,ExponentialStochastic.model,Primitive.stopped,if_neg ht]

theorem center_measurable (t : ℕ) (i : Fin K) : Measurable[ℱ t] (center h L hW c t i) :=
  ExponentialActual.center_measurable (R+M+D) L h.R_nonneg hW.le c h.extend.feedback t i
theorem radius_measurable (t : ℕ) (i j : Fin K) : Measurable[ℱ t] (radius h L hW c t i j) :=
  ExponentialActual.radius_measurable (R+M+D) L h.R_nonneg hW.le c h.extend.feedback t i j

def compositionLaws (hm : Protocol h L hW c (μ := μ)) (hL : 0≤L)
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W) :
    ExponentialComposition.Laws (model h L hW c hm) (center h L hW c) (radius h L hW c)
      (trajectory h L hW c) T W := by
  apply ExponentialActual.compositionLaws (R+M+D) L h.R_nonneg hW.le c h.extend.feedback
    (model h L hW c hm) (bridge h L hW c hm)
    (by linarith [h.R_nonneg,h.M_nonneg,h.D_nonneg]) hL hW
  intro t ht ω i j
  change h.extend.broadcast t ω j-h.extend.broadcast t ω i≤W
  simpa only [h.extend_broadcast ht] using hb t ht ω i j

theorem broadcast_span {B : ℝ} (hwidth : W=B+2*D)
    (hc : ∀ t<T, ∀ ω i j, h.publicCost t j ω-h.publicCost t i ω≤B) :
    ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W := by
  intro t ht ω i j
  have hi := abs_le.mp (h.error_bound t ht i ω)
  have hj := abs_le.mp (h.error_bound t ht j ω)
  have hh := hc t ht ω i j
  dsimp only [BoundedInputs.broadcast]
  rw [hwidth]
  linarith

theorem physical_before (hm : Protocol h L hW c (μ := μ)) (t : ℕ) (ht : t<T)
    (i : Fin K) (ω : Ω) :
    ExponentialPhysical.physical (model h L hW c hm) t i ω=h.physical t i ω := by
  simp only [ExponentialPhysical.physical,model,
    ExponentialStochastic.model_public _ _ _ _ hm ht,ExponentialStochastic.model_drift _ _ _ _ hm ht]
  rfl

theorem interval_physical_eq (hm : Protocol h L hW c (μ := μ)) (u n : ℕ) (hu : u+n≤T)
    (k : Fin K) (ω : Ω) :
    CNDPayment.intervalSum (fun t ω => ExponentialPhysical.physical (model h L hW c hm) t
      ((model h L hW c hm).action t ω) ω-ExponentialPhysical.physical (model h L hW c hm) t k ω) u n ω =
    ∑ t ∈ Ico u (u+n), (h.physical t (h.action t ω) ω-h.physical t k ω) := by
  rw [sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left,CNDPayment.intervalSum]
  apply sum_congr rfl
  intro t ht
  have htT : u+t<T := by have := mem_range.mp ht; omega
  rw [physical_before h L hW c hm _ htT,physical_before h L hW c hm _ htT]
  rw [show (model h L hW c hm).action (u+t)=h.action (u+t) from
    ExponentialStochastic.model_action _ _ _ _ hm htT]

theorem path_physical_eq (hm : Protocol h L hW c (μ := μ)) (path : ℕ → Fin K) (ω : Ω) :
    (∑ t ∈ range T, (ExponentialPhysical.physical (model h L hW c hm) t
      ((model h L hW c hm).action t ω) ω-ExponentialPhysical.physical (model h L hW c hm) t (path t) ω)) =
    ∑ t ∈ range T, (h.physical t (h.action t ω) ω-h.physical t (path t) ω) := by
  apply sum_congr rfl
  intro t ht
  have htT := mem_range.mp ht
  rw [physical_before h L hW c hm _ htT,physical_before h L hW c hm _ htT]
  rw [show (model h L hW c hm).action t=h.action t from ExponentialStochastic.model_action _ _ _ _ hm htT]

theorem conditional_main (hm : Protocol h L hW c (μ := μ)) (hL : 0≤L) (hT : 0<T)
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W)
    {δc δa δe : ℝ} (hδa : 0<δa) (hδa1 : δa<1) (hδe : 0<δe) (hδe1 : δe<1)
    (C : Set Ω) (hC : μ.real Cᶜ≤δc)
    (hcover : ∀ ω∈C, ExponentialPhysical.Covers (θ := θ) (center h L hW c) (radius h L hW c) T ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ≤δc+δa+δe ∧ ∀ ω∈G,
      ExponentialComposition.intervalConclusion (model h L hW c hm) (center h L hW c)
        (radius h L hW c) (trajectory h L hW c) T W δa δe ω ∧
      ExponentialComposition.pathConclusion (model h L hW c hm) (center h L hW c)
        (radius h L hW c) (trajectory h L hW c) T W δa δe ω := by
  exact ExponentialComposition.actual_conditional_e12_e13 (model h L hW c hm)
    (center h L hW c) (radius h L hW c) (trajectory h L hW c)
    (compositionLaws h L hW c hm hL hb) hW.le hT
    (center_measurable h L hW c) (radius_measurable h L hW c)
    hδa hδa1 hδe hδe1 C hC hcover

def ActualConclusions (hm : Protocol h L hW c (μ := μ)) (δa δe : ℝ) (ω : Ω) : Prop :=
  (∀ u n, u+n≤T → 0<n → ∀ k,
    (∑ t ∈ Ico u (u+n), (h.physical t (h.action t ω) ω-h.physical t k ω)) ≤
      ExponentialComposition.envelope (model h L hW c hm) (center h L hW c) (radius h L hW c)
        (trajectory h L hW c) T W u n k ω + ExponentialPhysical.actionBound W T n δa +
      ExponentialPhysical.encodingBound (ι := Fin K) (D := D) T n δe +
      CNDPayment.intervalSum (ExponentialPhysical.payment (model h L hW c hm) (radius h L hW c)) u n ω) ∧
  (∀ path : ℕ → Fin K,
    (∑ t ∈ range T, (h.physical t (h.action t ω) ω-h.physical t (path t) ω)) ≤
      (∑ j ∈ (SwitchingRuns.partition path T).labels,
        ExponentialComposition.envelope (model h L hW c hm) (center h L hW c) (radius h L hW c)
          (trajectory h L hW c) T W (ExponentialComposition.runStart path T j)
          (ExponentialComposition.runLength path T j) (SwitchingRuns.label path T j) ω) +
      ExponentialPhysical.noiseCoefficient (ι := Fin K) (D := D) W T δa δe *
        Real.sqrt ((T : ℝ) * ((ExponentialComposition.switchCount T path+1 : ℕ) : ℝ)) +
      CNDPayment.intervalSum (ExponentialPhysical.payment (model h L hW c hm) (radius h L hW c)) 0 T ω)

theorem conclusions_transfer (hm : Protocol h L hW c (μ := μ)) (δa δe : ℝ) (ω : Ω)
    (hg : ExponentialComposition.intervalConclusion (model h L hW c hm) (center h L hW c)
        (radius h L hW c) (trajectory h L hW c) T W δa δe ω ∧
      ExponentialComposition.pathConclusion (model h L hW c hm) (center h L hW c)
        (radius h L hW c) (trajectory h L hW c) T W δa δe ω) :
    ActualConclusions h L hW c hm δa δe ω := by
  constructor
  · intro u n hu hn k
    have hi := hg.1 u n hu hn k
    rw [interval_physical_eq h L hW c hm u n hu k ω] at hi
    exact hi
  · intro path
    have hp := hg.2 path
    rw [path_physical_eq h L hW c hm path ω] at hp
    exact hp

theorem actual_conditional_main (hm : Protocol h L hW c (μ := μ)) (hL : 0≤L) (hT : 0<T)
    (hb : ∀ t<T, ∀ ω i j, h.broadcast t ω j-h.broadcast t ω i≤W)
    {δc δa δe : ℝ} (hδa : 0<δa) (hδa1 : δa<1) (hδe : 0<δe) (hδe1 : δe<1)
    (C : Set Ω) (hC : μ.real Cᶜ≤δc)
    (hcover : ∀ ω∈C, ExponentialPhysical.Covers (θ := θ) (center h L hW c) (radius h L hW c) T ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ≤δc+δa+δe ∧
      ∀ ω∈G, ActualConclusions h L hW c hm δa δe ω := by
  obtain ⟨G,hG,hprob,hgood⟩ := conditional_main h L hW c hm hL hT hb
    hδa hδa1 hδe hδe1 C hC hcover
  exact ⟨G,hG,hprob,fun ω hω => conclusions_transfer h L hW c hm δa δe ω (hgood ω hω)⟩

#print axioms bridge
#print axioms compositionLaws
#print axioms interval_physical_eq
#print axioms path_physical_eq
#print axioms conditional_main
#print axioms actual_conditional_main
end Part2.ExponentialFinite
