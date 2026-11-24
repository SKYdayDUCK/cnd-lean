import staging.cnd20261026.«fix-bounded-sg».FiniteSGComplete

noncomputable section
open MeasureTheory Finset
open scoped BigOperators NNReal
namespace Part2.CNDHorizon.FiniteSG
open CNDProcess CNDBoundedRate
variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {σ σe : ℝ}
variable (ν : ℝ≥0)

theorem paper_original_sg_main_with_rates (hν : (ν:ℝ)^2=σ^2+σe^2)
    (h : SGInputs ℱ θ R M D T) (B : ℝ) (hB : 0 ≤ B) (δc δg δl δa δn : ℝ)
    (hm : SGLaws (maps ν h B (CNDNet.paperLc (Fin K) T δc) hB)
      (treeData (Nat.clog 2 T) K (B+2*D) R) h μ σ σe)
    (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω-h.publicCost t i ω ≤ B)
    {δ : ℝ} (hδc : 0 < δc) (hδg : 0 < δg) (hδl : 0 < δl)
    (hδa : 0 < δa) (hδn : 0 < δn) (hδ : δ < 1)
    (hδsum : δc+δg+δl+δa+δn ≤ δ) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δ ∧ ∀ ω ∈ G,
      CompleteConclusions (d:=Nat.clog 2 T) ν h B hB δc δg δl δa δn ω ∧
      (∀ u n : ℕ, u+n ≤ T → 0 < n →
        CNDPayment.intervalSum (actualLedger (d:=Nat.clog 2 T) ν h B (CNDNet.paperLc (Fin K) T δc) hB) u n ω ≤
          (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (n:ℝ)*(paperL0 K T δc δg δl)^2) ∧
      (globalBudget (d:=Nat.clog 2 T) ν h B (CNDNet.paperLc (Fin K) T δc) hB δg ω ≤
        (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (T:ℝ)*(paperL0 K T δc δg δl)^2) ∧
      (∀ u n : ℕ, u+n ≤ T → 0 < n → ∀ path : ℕ → Fin K,
        intervalPathRegret h u n path ω ≤ SGRate.paperPublicCoefficient ν K T B D δa δn *
          Real.sqrt ((n:ℝ)*((SGMain.intervalSwitchCount u n path+1:ℕ):ℝ)) +
          (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (n:ℝ)*(paperL0 K T δc δg δl)^2) ∧
      (∀ path : ℕ → Fin K, pathRegret h path ω ≤ SGRate.paperPublicCoefficient ν K T B D δa δn *
        Real.sqrt ((T:ℝ)*((SGMain.switchCount T path+1:ℕ):ℝ)) +
        (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (T:ℝ)*(paperL0 K T δc δg δl)^2)  := by
  obtain ⟨G,hG,hprob,hgood⟩ := SGRate.paper_original_sg_main_with_rates ν hν h.extend B hB δc δg δl δa δn hm.toInternal
    hK hT0 (by intro t ht; simpa only [SGInputs.extend,if_pos ht] using hc t ht)
    hδc hδg hδl hδa hδn hδ hδsum
  refine ⟨G,hG,hprob,?_⟩
  intro ω hω
  obtain ⟨hg,hl,hb,hlocal,hpath⟩ := hgood ω hω
  refine ⟨complete_prefix ν h B hB δc δg δl δa δn hm ω hg,?_,?_,?_,?_⟩
  · intro u n hu hn
    have hi := hl u n hu hn
    rwa [ledgerSum_eq ν h B _ hB hm u n hu ω] at hi
  · rwa [global_eq ν h B _ hB hm δg ω] at hb
  · intro u n hu hn path
    have hi := hlocal u n hu hn path
    rwa [intervalPathRegret_eq h u n hu path ω] at hi
  · intro path
    have hi := hpath path
    rwa [pathRegret_eq h path ω] at hi

theorem default_budget_sg_main_with_rates (hν : (ν:ℝ)^2=σ^2+σe^2)
    (h : SGInputs ℱ θ R M D T) (B : ℝ) (hB : 0 ≤ B) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm : SGLaws (maps ν h B (CNDNet.paperLc (Fin K) T (δ/5)) hB)
      (treeData (Nat.clog 2 T) K (B+2*D) R) h μ σ σe)
    (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω-h.publicCost t i ω ≤ B) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δ ∧ ∀ ω ∈ G,
      CompleteConclusions (d:=Nat.clog 2 T) ν h B hB (δ/5) (δ/5) (δ/5) (δ/5) (δ/5) ω ∧
      (∀ u n : ℕ, u+n ≤ T → 0 < n →
        CNDPayment.intervalSum (actualLedger (d:=Nat.clog 2 T) ν h B (CNDNet.paperLc (Fin K) T (δ/5)) hB) u n ω ≤
          (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (n:ℝ)*(SGRate.defaultLog K T δ)^2) ∧
      (globalBudget (d:=Nat.clog 2 T) ν h B (CNDNet.paperLc (Fin K) T (δ/5)) hB (δ/5) ω ≤
        (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (T:ℝ)*(SGRate.defaultLog K T δ)^2) ∧
      (∀ u n : ℕ, u+n ≤ T → 0 < n → ∀ path : ℕ → Fin K,
        intervalPathRegret h u n path ω ≤ SGRate.paperPublicCoefficient ν K T B D (δ/5) (δ/5) *
          Real.sqrt ((n:ℝ)*((SGMain.intervalSwitchCount u n path+1:ℕ):ℝ)) +
          (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (n:ℝ)*(SGRate.defaultLog K T δ)^2) ∧
      (∀ path : ℕ → Fin K, pathRegret h path ω ≤ SGRate.paperPublicCoefficient ν K T B D (δ/5) (δ/5) *
        Real.sqrt ((T:ℝ)*((SGMain.switchCount T path+1:ℕ):ℝ)) +
        (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (T:ℝ)*(SGRate.defaultLog K T δ)^2)  := by
  simpa only [SGRate.defaultLog] using paper_original_sg_main_with_rates ν hν h B hB
    (δ/5) (δ/5) (δ/5) (δ/5) (δ/5) hm hK hT0 hc
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hδ1 (by linarith)

end Part2.CNDHorizon.FiniteSG
