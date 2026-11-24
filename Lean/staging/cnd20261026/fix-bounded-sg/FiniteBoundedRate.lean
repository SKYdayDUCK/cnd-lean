import staging.cnd20261026.«fix-bounded-sg».FiniteBounded

noncomputable section
open MeasureTheory Finset
open scoped BigOperators
namespace Part2.CNDHorizon.FiniteBounded
open CNDProcess BoundedRate
variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem paper_original_main_with_rates (h : BoundedInputs ℱ θ R M D T) (B : ℝ) (hB : 0≤B)
    (δc δg δl δa δe : ℝ)
    (hm : BoundedLaws (maps h B (CNDNet.paperLc (Fin K) T δc) hB)
      (treeData (Nat.clog 2 T) K (B+2*D) R) h μ)
    (hK : 2≤K) (hT0 : 1≤T) (hc : ∀ t<T,∀ ω i j,h.publicCost t j ω-h.publicCost t i ω≤B)
    {δ : ℝ} (hδc : 0<δc) (hδg : 0<δg) (hδl : 0<δl) (hδa : 0<δa) (hδe : 0<δe)
    (hδ : δ<1) (hδsum : δc+δg+δl+δa+δe≤δ) :
    ∃ G : Set Ω,MeasurableSet G ∧ μ.real Gᶜ≤δ ∧ ∀ ω∈G,
      Conclusions (d:=Nat.clog 2 T) h B hB δc δg δl δa δe ω ∧
      (∀ u n : ℕ,u+n≤T → 0<n →
        CNDPayment.intervalSum (actualLedger (d:=Nat.clog 2 T) h B (CNDNet.paperLc (Fin K) T δc) hB) u n ω≤
          (156/CNDPhysical.c0)*(R+M+D)*(K:ℝ)*Real.sqrt (n:ℝ)*(paperL0 K T δc δg δl)^2) ∧
      (globalBudget (d:=Nat.clog 2 T) h B (CNDNet.paperLc (Fin K) T δc) hB δg ω≤
        (156/CNDPhysical.c0)*(R+M+D)*(K:ℝ)*Real.sqrt (T:ℝ)*(paperL0 K T δc δg δl)^2) ∧
      (∀ path : ℕ → Fin K,pathRegret h path ω≤paperPublicCoefficient K T B D δa δe*
        Real.sqrt ((T:ℝ)*((BoundedMain.switchCount T path+1:ℕ):ℝ))+
        (156/CNDPhysical.c0)*(R+M+D)*(K:ℝ)*Real.sqrt (T:ℝ)*(paperL0 K T δc δg δl)^2) := by
  obtain ⟨G,hG,hprob,hgood⟩ := BoundedRate.paper_original_main_with_rates h.extend B hB δc δg δl δa δe hm.toInternal
    hK hT0 (by intro t ht; simpa only [BoundedInputs.extend,if_pos ht] using hc t ht)
    hδc hδg hδl hδa hδe hδ hδsum
  refine ⟨G,hG,hprob,?_⟩
  intro ω hω
  obtain ⟨hg,hl,hb,hp⟩ := hgood ω hω
  refine ⟨conclusions_prefix h B hB δc δg δl δa δe hm ω hg,?_,?_,?_⟩
  · intro u n hu hn
    have hi := hl u n hu hn
    rwa [ledgerSum_eq h B _ hB hm u n hu ω] at hi
  · rwa [global_eq h B _ hB hm δg ω] at hb
  · intro path
    have hi := hp path
    rwa [pathRegret_eq h path ω] at hi
end Part2.CNDHorizon.FiniteBounded
