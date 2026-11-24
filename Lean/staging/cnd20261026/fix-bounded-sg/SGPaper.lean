import staging.cnd20261026.«fix-bounded-sg».SGPaths

noncomputable section
open MeasureTheory Finset
open scoped BigOperators NNReal
namespace Part2.CNDHorizon.SGMain
open CNDProcess CNDProcess.SG
variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {σ σe : ℝ}

/-- The complete original paper run uses the predetermined padded tree depth. -/
theorem paper_depth_sg_complete_main (ν : ℝ≥0) (hν : (ν:ℝ)^2=σ^2+σe^2)
    (h : Inputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B) (δc δg δl δa δn : ℝ)
    (hm : CNDHorizon.SG.Laws (maps (K := K) ν (CNDNet.paperLc (Fin K) T δc) R M (B+2*D)
      h.R_nonneg (public_width_nonneg h hB))
      (treeData (Nat.clog 2 T) K (B+2*D) R) h μ σ σe T)
    (hK : 2 ≤ K) (hT : 1 ≤ T)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω-h.publicCost t i ω ≤ B)
    {δ : ℝ} (hδc : 0 < δc) (hδg : 0 < δg) (hδl : 0 < δl)
    (hδa : 0 < δa) (hδn : 0 < δn) (hδ : δ < 1)
    (hδsum : δc+δg+δl+δa+δn ≤ δ) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δ ∧
      ∀ ω ∈ G, SGCompleteConclusions ν h B hB δc δg δl δa δn hm ω := by
  exact original_sg_complete_main ν h B hB δc δg δl δa δn hm hν hK hT
    (CNDProd.padded_horizon T) hc hδc hδg hδl hδa hδn hδ hδsum

/-- Width zero removes the public terms and retains the physical-noise term. -/
theorem zero_width_keeps_noise (ν : ℝ≥0) (d K T : ℕ) (B D δa δn : ℝ)
    (hW : B+2*D=0) :
    publicCoefficient ν d K T B D δa δn =
      (2*(ν:ℝ))*Real.sqrt (2*Real.log ((K:ℝ)*(T:ℝ)^2/δn)) := by
  simp only [publicCoefficient,hW,mul_zero,zero_mul,zero_add]

/-- R=0 fixes the private parameter while retaining the raw noisy observation. -/
theorem zero_range_residual_preserves_noise (h : Inputs ℱ θ R M D) (hR : R=0)
    (t : ℕ) (ω : Ω) :
    h.residual t ω = h.drift t ω+h.noise t ω (h.action t ω)-h.error t (h.action t ω) ω := by
  have ht : θ (h.action t ω)=0 :=
    le_antisymm (by simpa only [hR] using (h.theta_range (h.action t ω)).2) (h.theta_range _).1
  rw [h.residual_eq,ht,zero_add]

end Part2.CNDHorizon.SGMain
