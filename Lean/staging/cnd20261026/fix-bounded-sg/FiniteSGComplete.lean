import staging.cnd20261026.«fix-bounded-sg».FiniteSG

noncomputable section
open MeasureTheory Finset
open scoped BigOperators NNReal
namespace Part2.CNDHorizon.FiniteSG
open CNDProcess
variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {σ σe : ℝ}

def intervalPathRegret (h : SGInputs ℱ θ R M D T) (u n : ℕ) (path : ℕ → Fin K) (ω : Ω) : ℝ :=
  ∑ t ∈ range n,(h.physical (u+t) (h.action (u+t) ω) ω-h.physical (u+t) (path (u+t)) ω)

theorem intervalPathRegret_eq (h : SGInputs ℱ θ R M D T) (u n : ℕ) (hu : u+n≤T) (path : ℕ → Fin K) (ω : Ω) :
    SGMain.intervalPathRegret h.extend u n path ω=intervalPathRegret h u n path ω := by
  apply sum_congr rfl
  intro t ht
  have htT : u+t<T := by have := mem_range.mp ht; omega
  rw [h.extend_physical htT,h.extend_action htT]

def CompleteConclusions (ν : ℝ≥0) (h : SGInputs ℱ θ R M D T) (B : ℝ) (hB : 0≤B)
    (δc δg δl δa δn : ℝ) (ω : Ω) : Prop :=
  Conclusions (d:=d) ν h B hB δc δg δl δa δn ω ∧
  (∀ u n : ℕ,u+n≤T → 0<n → ∀ path : ℕ → Fin K,
    intervalPathRegret h u n path ω≤SGMain.publicCoefficient ν d K T B D δa δn*
      Real.sqrt ((n:ℝ)*((SGMain.intervalSwitchCount u n path+1:ℕ):ℝ))+
      CNDPayment.intervalSum (actualLedger (d:=d) ν h B (CNDNet.paperLc (Fin K) T δc) hB) u n ω) ∧
  (∀ u n : ℕ,∀ P : Intervals.Partition (Ico u (u+n)),
    (∑ j ∈ P.labels,∑ t ∈ P.block j,actualLedger (d:=d) ν h B (CNDNet.paperLc (Fin K) T δc) hB t ω)=
      CNDPayment.intervalSum (actualLedger (d:=d) ν h B (CNDNet.paperLc (Fin K) T δc) hB) u n ω)

theorem complete_prefix (ν : ℝ≥0) (h : SGInputs ℱ θ R M D T) (B : ℝ) (hB : 0≤B)
    (δc δg δl δa δn : ℝ)
    (hm : SGLaws (maps ν h B (CNDNet.paperLc (Fin K) T δc) hB) (treeData d K (B+2*D) R) h μ σ σe)
    (ω : Ω) (hg : SGMain.SGCompleteConclusions ν h.extend B hB δc δg δl δa δn hm.toInternal ω) :
    CompleteConclusions (d:=d) ν h B hB δc δg δl δa δn ω := by
  refine ⟨conclusions_prefix ν h B hB δc δg δl δa δn hm ω hg.1,?_,?_⟩
  · intro u n hu hn path
    have hi := hg.2.1 u n hu hn path
    rwa [intervalPathRegret_eq h u n hu path ω,ledgerSum_eq ν h B _ hB hm u n hu ω] at hi
  · intro u n P
    rw [← SGMain.sum_Ico_eq_intervalSum]
    exact P.sum_blocks _

theorem original_sg_complete_main (ν : ℝ≥0) (hν : (ν:ℝ)^2=σ^2+σe^2)
    (h : SGInputs ℱ θ R M D T) (B : ℝ) (hB : 0≤B) (δc δg δl δa δn : ℝ)
    (hm : SGLaws (maps ν h B (CNDNet.paperLc (Fin K) T δc) hB) (treeData d K (B+2*D) R) h μ σ σe)
    (hK : 2≤K) (hT0 : 1≤T) (hT : T≤2^d) (hc : ∀ t<T,∀ ω i j,h.publicCost t j ω-h.publicCost t i ω≤B)
    {δ : ℝ} (hδc : 0<δc) (hδg : 0<δg) (hδl : 0<δl) (hδa : 0<δa) (hδn : 0<δn)
    (hδ : δ<1) (hδsum : δc+δg+δl+δa+δn≤δ) :
    ∃ G : Set Ω,MeasurableSet G ∧ μ.real Gᶜ≤δ ∧ ∀ ω∈G,CompleteConclusions (d:=d) ν h B hB δc δg δl δa δn ω := by
  obtain ⟨G,hG,hprob,hgood⟩ := SGMain.original_sg_complete_main ν h.extend B hB δc δg δl δa δn hm.toInternal
    hν hK hT0 hT (by intro t ht; simpa only [SGInputs.extend,if_pos ht] using hc t ht)
    hδc hδg hδl hδa hδn hδ hδsum
  exact ⟨G,hG,hprob,fun ω hω => complete_prefix ν h B hB δc δg δl δa δn hm ω (hgood ω hω)⟩

theorem paper_depth_sg_complete_main (ν : ℝ≥0) (hν : (ν:ℝ)^2=σ^2+σe^2)
    (h : SGInputs ℱ θ R M D T) (B : ℝ) (hB : 0≤B) (δc δg δl δa δn : ℝ)
    (hm : SGLaws (maps ν h B (CNDNet.paperLc (Fin K) T δc) hB) (treeData (Nat.clog 2 T) K (B+2*D) R) h μ σ σe)
    (hK : 2≤K) (hT0 : 1≤T) (hc : ∀ t<T,∀ ω i j,h.publicCost t j ω-h.publicCost t i ω≤B)
    {δ : ℝ} (hδc : 0<δc) (hδg : 0<δg) (hδl : 0<δl) (hδa : 0<δa) (hδn : 0<δn)
    (hδ : δ<1) (hδsum : δc+δg+δl+δa+δn≤δ) :
    ∃ G : Set Ω,MeasurableSet G ∧ μ.real Gᶜ≤δ ∧ ∀ ω∈G,
      CompleteConclusions (d:=Nat.clog 2 T) ν h B hB δc δg δl δa δn ω :=
  original_sg_complete_main ν hν h B hB δc δg δl δa δn hm hK hT0 (CNDProd.padded_horizon T) hc
    hδc hδg hδl hδa hδn hδ hδsum
end Part2.CNDHorizon.FiniteSG
