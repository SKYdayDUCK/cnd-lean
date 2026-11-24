import staging.cnd20261026.«fix-bounded-sg».SGRate
import staging.cnd20261026.«fix-bounded-sg».OutputPrefix

noncomputable section
open MeasureTheory Finset
open scoped BigOperators NNReal
namespace Part2.CNDHorizon.FiniteSG
open CNDProcess
variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {σ σe : ℝ}
variable (ν : ℝ≥0)

theorem width_nonneg (h : SGInputs ℱ θ R M D T) {B : ℝ} (hB : 0≤B) : 0≤B+2*D := by
  linarith [h.D_nonneg]

def maps (h : SGInputs ℱ θ R M D T) (B L : ℝ) (hB : 0≤B) : DecisionMaps (Fin K) :=
  concreteMaps (R+M+(ν:ℝ)) (4*L) R (B+2*D) h.R_nonneg (width_nonneg h hB)

def intervalRegret (h : SGInputs ℱ θ R M D T) (u n : ℕ) (k : Fin K) (ω : Ω) : ℝ :=
  ∑ t ∈ Ico u (u+n), (h.physical t (h.action t ω) ω-h.physical t k ω)
def pathRegret (h : SGInputs ℱ θ R M D T) (path : ℕ → Fin K) (ω : Ω) : ℝ :=
  ∑ t ∈ range T, (h.physical t (h.action t ω) ω-h.physical t (path t) ω)
def actualLedger (h : SGInputs ℱ θ R M D T) (B L : ℝ) (hB : 0≤B) : ℕ → Ω → ℝ :=
  ledger (h.actualP (maps ν h B L hB) (treeData d K (B+2*D) R)) h.action (R+M+(ν:ℝ)) (4*L) R
def actualBudgetQ (h : SGInputs ℱ θ R M D T) (B L : ℝ) (hB : 0≤B) (u n : ℕ) (ω : Ω) : ℝ :=
  CNDInformation.branchedQ (CNDInformation.canonicalChart (Fin K))
    (fun t i => h.actualP (maps ν h B L hB) (treeData d K (B+2*D) R) t i ω) u n (R+M+(ν:ℝ)) (4*L) R
def globalBudget (h : SGInputs ℱ θ R M D T) (B L : ℝ) (hB : 0≤B) (δg : ℝ) (ω : Ω) : ℝ :=
  min ((4*R/CNDPhysical.c0)*(T:ℝ)) (4*actualBudgetQ (d:=d) ν h B L hB 0 T ω+(4*R/CNDPhysical.c0)*Real.log (1/δg))
def exactPaymentEnvelope (h : SGInputs ℱ θ R M D T) (B L : ℝ) (hB : 0≤B)
    (u n : ℕ) (δg δl : ℝ) (ω : Ω) : ℝ :=
  min ((4*R/CNDPhysical.c0)*(n:ℝ)) (min
    (4*actualBudgetQ (d:=d) ν h B L hB u n ω+(4*R/CNDPhysical.c0)*Real.log ((T:ℝ)^2/δl))
    (globalBudget (d:=d) ν h B L hB δg ω))

section Transfer
variable (h : SGInputs ℱ θ R M D T) (B L : ℝ) (hB : 0≤B)
  (hm : SGLaws (maps ν h B L hB) (treeData d K (B+2*D) R) h μ σ σe)

theorem probability_prefix (t : ℕ) (ht : t<T) :
    ((CNDHorizon.SG.actualModel h.extend ν L (B+2*D) (width_nonneg h hB) hm.toInternal).toM1Model).p t=
      h.actualP (maps ν h B L hB) (treeData d K (B+2*D) R) t := by
  change (CNDHorizon.SG.model _ _ h.extend hm.toInternal).p t=_
  rw [CNDHorizon.SG.model_p _ _ _ _ ht]
  exact h.probability_prefix _ _ t (Nat.le_of_lt ht)

theorem ledger_eq (t : ℕ) (ht : t<T) (ω : Ω) :
    SGMain.actualLedger ν h.extend B L hB hm.toInternal t ω=actualLedger (d:=d) ν h B L hB t ω := by
  apply ledger_prefix _ _ _ (probability_prefix ν h B L hB hm) _ _ _ t ht ω
  intro s hs
  change (CNDHorizon.SG.model _ _ h.extend hm.toInternal).action s=_
  rw [CNDHorizon.SG.model_action _ _ _ _ hs,h.extend_action hs]

theorem ledgerSum_eq (u n : ℕ) (hu : u+n≤T) (ω : Ω) :
    CNDPayment.intervalSum (SGMain.actualLedger ν h.extend B L hB hm.toInternal) u n ω=
      CNDPayment.intervalSum (actualLedger (d:=d) ν h B L hB) u n ω :=
  intervalSum_prefix _ _ (fun t ht => funext (ledger_eq ν h B L hB hm t ht)) u n hu ω

theorem budgetQ_eq (u n : ℕ) (hu : u+n≤T) (ω : Ω) :
    SGMain.actualBudgetQ ν h.extend B L hB hm.toInternal u n ω=actualBudgetQ (d:=d) ν h B L hB u n ω := by
  apply budgetQ_prefix
  intro t ht
  exact congrArg (fun p => fun i => p i ω) (probability_prefix ν h B L hB hm t (lt_of_lt_of_le ht hu))

theorem global_eq (δg : ℝ) (ω : Ω) :
    SGMain.globalBudget ν h.extend B L hB hm.toInternal T δg ω=globalBudget (d:=d) ν h B L hB δg ω := by
  unfold SGMain.globalBudget globalBudget
  rw [budgetQ_eq ν h B L hB hm 0 T (by omega) ω]

theorem envelope_eq (u n : ℕ) (hu : u+n≤T) (δg δl : ℝ) (ω : Ω) :
    SGMain.exactPaymentEnvelope ν h.extend B L hB hm.toInternal T u n δg δl ω=
      exactPaymentEnvelope (d:=d) ν h B L hB u n δg δl ω := by
  unfold SGMain.exactPaymentEnvelope exactPaymentEnvelope
  rw [budgetQ_eq ν h B L hB hm u n hu ω,global_eq ν h B L hB hm δg ω]
end Transfer

theorem intervalRegret_eq (h : SGInputs ℱ θ R M D T) (u n : ℕ) (hu : u+n≤T) (k : Fin K) (ω : Ω) :
    SGMain.intervalRegret h.extend u n k ω=intervalRegret h u n k ω := by
  apply sum_congr rfl
  intro t ht
  have htT : t<T := lt_of_lt_of_le (mem_Ico.mp ht).2 hu
  rw [h.extend_physical htT,h.extend_action htT]

theorem pathRegret_eq (h : SGInputs ℱ θ R M D T) (path : ℕ → Fin K) (ω : Ω) :
    SGMain.pathRegret h.extend T path ω=pathRegret h path ω := by
  apply sum_congr rfl
  intro t ht
  rw [h.extend_physical (mem_range.mp ht),h.extend_action (mem_range.mp ht)]

def Conclusions (h : SGInputs ℱ θ R M D T) (B : ℝ) (hB : 0≤B) (δc δg δl δa δn : ℝ) (ω : Ω) : Prop :=
  (∀ u n : ℕ, u+n≤T → 0<n → ∀ k : Fin K, intervalRegret h u n k ω≤
    32*(B+2*D)*Real.sqrt ((n:ℝ)*CNDProd.logExperts d K)+
    (B+2*D)*Real.sqrt (2*(n:ℝ)*Real.log ((T:ℝ)^2/δa))+
    (2*(ν:ℝ))*Real.sqrt (2*(n:ℝ)*Real.log ((K:ℝ)*(T:ℝ)^2/δn))+
    CNDPayment.intervalSum (actualLedger (d:=d) ν h B (CNDNet.paperLc (Fin K) T δc) hB) u n ω) ∧
  (∀ u n : ℕ, u+n≤T → 0<n → CNDPayment.intervalSum (actualLedger (d:=d) ν h B (CNDNet.paperLc (Fin K) T δc) hB) u n ω≤
    exactPaymentEnvelope (d:=d) ν h B (CNDNet.paperLc (Fin K) T δc) hB u n δg δl ω) ∧
  (∀ path : ℕ → Fin K, pathRegret h path ω≤SGMain.publicCoefficient ν d K T B D δa δn*
    Real.sqrt ((T:ℝ)*((SGMain.switchCount T path+1:ℕ):ℝ))+
    globalBudget (d:=d) ν h B (CNDNet.paperLc (Fin K) T δc) hB δg ω) ∧
  (∀ P : Intervals.Partition (range T),
    (∑ j ∈ P.labels, ∑ t ∈ P.block j, actualLedger (d:=d) ν h B (CNDNet.paperLc (Fin K) T δc) hB t ω)=
    CNDPayment.intervalSum (actualLedger (d:=d) ν h B (CNDNet.paperLc (Fin K) T δc) hB) 0 T ω)

theorem conclusions_prefix (h : SGInputs ℱ θ R M D T) (B : ℝ) (hB : 0≤B) (δc δg δl δa δn : ℝ)
    (hm : SGLaws (maps ν h B (CNDNet.paperLc (Fin K) T δc) hB) (treeData d K (B+2*D) R) h μ σ σe)
    (ω : Ω) (hg : SGMain.SGConclusions ν h.extend B hB δc δg δl δa δn hm.toInternal ω) :
    Conclusions (d:=d) ν h B hB δc δg δl δa δn ω := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u n hu hn k
    have hi := hg.1 u n hu hn k
    rwa [intervalRegret_eq h u n hu k ω,ledgerSum_eq ν h B _ hB hm u n hu ω] at hi
  · intro u n hu hn
    have hi := hg.2.1 u n hu hn
    rwa [ledgerSum_eq ν h B _ hB hm u n hu ω,envelope_eq ν h B _ hB hm u n hu δg δl ω] at hi
  · intro path
    have hi := hg.2.2.1 path
    rwa [pathRegret_eq h path ω,global_eq ν h B _ hB hm δg ω] at hi
  · intro P
    simpa only [CNDPayment.intervalSum,Nat.zero_add] using
      P.sum_blocks (fun t => actualLedger (d:=d) ν h B (CNDNet.paperLc (Fin K) T δc) hB t ω)

theorem original_sg_main (h : SGInputs ℱ θ R M D T) (B : ℝ) (hB : 0≤B)
    (δc δg δl δa δn : ℝ)
    (hm : SGLaws (maps ν h B (CNDNet.paperLc (Fin K) T δc) hB) (treeData d K (B+2*D) R) h μ σ σe)
    (hν : (ν:ℝ)^2=σ^2+σe^2)
    (hK : 2≤K) (hT0 : 1≤T) (hT : T≤2^d)
    (hc : ∀ t<T,∀ ω i j,h.publicCost t j ω-h.publicCost t i ω≤B)
    {δ : ℝ} (hδc : 0<δc) (hδg : 0<δg) (hδl : 0<δl) (hδa : 0<δa) (hδn : 0<δn)
    (hδ : δ<1) (hδsum : δc+δg+δl+δa+δn≤δ) :
    ∃ G : Set Ω,MeasurableSet G ∧ μ.real Gᶜ≤δ ∧ ∀ ω∈G,Conclusions (d:=d) ν h B hB δc δg δl δa δn ω := by
  obtain ⟨G,hG,hprob,hgood⟩ := SGMain.original_sg_main ν h.extend B hB δc δg δl δa δn hm.toInternal
    hν hK hT0 hT (by intro t ht; simpa only [SGInputs.extend,if_pos ht] using hc t ht)
    hδc hδg hδl hδa hδn hδ hδsum
  exact ⟨G,hG,hprob,fun ω hω => conclusions_prefix ν h B hB δc δg δl δa δn hm ω (hgood ω hω)⟩

theorem paper_depth_sg_main (h : SGInputs ℱ θ R M D T) (B : ℝ) (hB : 0≤B)
    (δc δg δl δa δn : ℝ)
    (hm : SGLaws (maps ν h B (CNDNet.paperLc (Fin K) T δc) hB) (treeData (Nat.clog 2 T) K (B+2*D) R) h μ σ σe)
    (hν : (ν:ℝ)^2=σ^2+σe^2)
    (hK : 2≤K) (hT0 : 1≤T) (hc : ∀ t<T,∀ ω i j,h.publicCost t j ω-h.publicCost t i ω≤B)
    {δ : ℝ} (hδc : 0<δc) (hδg : 0<δg) (hδl : 0<δl) (hδa : 0<δa) (hδn : 0<δn)
    (hδ : δ<1) (hδsum : δc+δg+δl+δa+δn≤δ) :
    ∃ G : Set Ω,MeasurableSet G ∧ μ.real Gᶜ≤δ ∧ ∀ ω∈G,Conclusions (d:=Nat.clog 2 T) ν h B hB δc δg δl δa δn ω :=
  original_sg_main ν h B hB δc δg δl δa δn hm hν hK hT0 (CNDProd.padded_horizon T) hc
    hδc hδg hδl hδa hδn hδ hδsum
end Part2.CNDHorizon.FiniteSG
