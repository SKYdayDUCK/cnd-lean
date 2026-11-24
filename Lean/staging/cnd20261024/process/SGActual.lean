import staging.cnd20261024.process.SGOriginal

/-! The actual SG algorithm uses exactly the frozen canonical maps with
H=R+M+nu and L=4Lc. Statistics consume the genuine noisy residual. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators NNReal Matrix
namespace Part2.CNDProcess.SG

def maps {K : ℕ} [Nonempty (Fin K)] (ν : ℝ≥0) (Lc R M W : ℝ)
    (hR : 0 ≤ R) (hW : 0 ≤ W) : DecisionMaps (Fin K) :=
  concreteMaps (R + M + (ν : ℝ)) (4 * Lc) R W hR hW

variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ}

def actualScoreSum (o : DecisionMaps ι) (d : ExpertData ι E) (h : Inputs ℱ θ R M D)
    (n : ℕ) (ω : Ω) (i : ι) : ℝ :=
  ∑ t ∈ range n, ((if h.action t ω = i then 1 else 0) - runProbability o d h.feedback t i ω) *
    (θ (h.action t ω) + h.drift t ω + h.noise t ω (h.action t ω) - h.error t (h.action t ω) ω)

theorem runS_eq_actualScoreSum (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : Inputs ℱ θ R M D) (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) (i : ι) :
    runS o d h.feedback n i ω = actualScoreSum o d h n ω i := by
  rw [actual_statistic_identity o d h.feedback hR]
  apply sum_congr rfl
  intro t _
  change ((if h.action t ω = i then 1 else 0) - runProbability o d h.feedback t i ω) * h.residual t ω = _
  rw [h.residual_eq]

theorem estimator_uses_actual_score (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : Inputs ℱ θ R M D) (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) :
    StatisticalMaps.estimate (run o d h.feedback n ω).1 =
      CNDPhysical.inverseInformation (fun t i ↦ runProbability o d h.feedback t i ω) n *ᵥ
        actualScoreSum o d h n ω := by
  funext i
  rw [estimate_is_actual_inverse_statistic o d h.feedback hR]
  simp only [Matrix.mulVec, dotProduct, runS_eq_actualScoreSum o d h hR]

theorem original_pair_radius (Hs Lc R : ℝ) (s : Stats ι) (i j : ι) :
    StatisticalMaps.rawPairRadius Hs (4 * Lc) R s i j =
      4 * Hs * Real.sqrt (Lc * StatisticalMaps.resistance s.1 i j) +
        (16 * Hs * Lc + R * Fintype.card ι) * StatisticalMaps.resistance s.1 i j := by
  unfold StatisticalMaps.rawPairRadius
  rw [show 4 * Lc * StatisticalMaps.resistance s.1 i j =
    4 * (Lc * StatisticalMaps.resistance s.1 i j) by ring]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  ring

section Concrete
variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {θK : Fin K → ℝ} {σ σe : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def actualModel (h : Inputs ℱ θK R M D) (ν : ℝ≥0) (Lc W : ℝ) (hW : 0 ≤ W)
    (hm : Laws (maps ν Lc R M W h.R_nonneg hW) (treeData d K W R) h μ σ σe) :
    CNDProbability.SGModel ℱ μ θK R M D σ σe :=
  Laws.model _ _ h hm

theorem actualModel_probability (h : Inputs ℱ θK R M D) (ν : ℝ≥0) (Lc W : ℝ) (hW : 0 ≤ W)
    (hm : Laws (maps ν Lc R M W h.R_nonneg hW) (treeData d K W R) h μ σ σe)
    (n : ℕ) (i : Fin K) :
    (actualModel h ν Lc W hW hm).p n i =
      runProbability (maps ν Lc R M W h.R_nonneg hW) (treeData d K W R) h.feedback n i := rfl

theorem proxy_interval (hK : 2 ≤ K) (hT : T ≤ 2 ^ d) (h : Inputs ℱ θK R M D)
    (ν : ℝ≥0) (Lc W : ℝ) (hLc : 0 ≤ Lc) (hW : 0 < W) (ω : Ω)
    (hb : ∀ t < T, ∀ i j, h.broadcast t ω j - h.broadcast t ω i ≤ W)
    (u v : ℕ) (huv : u ≤ v) (hv : v ≤ T) (k : Fin K) :
    let o := maps ν Lc R M W h.R_nonneg hW.le
    let a := treeData d K W R
    (∑ t ∈ Ico u v, ((∑ j, runProbability o a h.feedback t j ω *
        processLoss o a t (run o a h.feedback t ω) (h.broadcast t ω) j) -
      processLoss o a t (run o a h.feedback t ω) (h.broadcast t ω) k)) ≤
        32 * W * Real.sqrt (((v - u : ℕ) : ℝ) * CNDProd.logExperts d K) := by
  exact actual_proxy_interval hK hT (R + M + (ν : ℝ)) (4 * Lc) R W
    (add_nonneg (add_nonneg h.R_nonneg h.M_nonneg) ν.coe_nonneg)
    (by positivity) h.R_nonneg hW h.feedback ω hb u v huv hv k

theorem zero_width_proxy_interval (h : Inputs ℱ θK R M D) (ν : ℝ≥0)
    (Lc : ℝ) (hLc : 0 ≤ Lc) (ω : Ω)
    (hb : ∀ t < T, ∀ i j, h.broadcast t ω j - h.broadcast t ω i ≤ 0)
    (u v : ℕ) (hv : v ≤ T) (k : Fin K) :
    let o := maps ν Lc R M 0 h.R_nonneg le_rfl
    let a := treeData d K 0 R
    (∑ t ∈ Ico u v, ((∑ j, runProbability o a h.feedback t j ω *
        processLoss o a t (run o a h.feedback t ω) (h.broadcast t ω) j) -
      processLoss o a t (run o a h.feedback t ω) (h.broadcast t ω) k)) ≤ 0 := by
  exact actual_zero_width_proxy_interval (R + M + (ν : ℝ)) (4 * Lc) R
    (add_nonneg (add_nonneg h.R_nonneg h.M_nonneg) ν.coe_nonneg)
    (by positivity) h.R_nonneg h.feedback ω hb u v hv k
end Concrete
end Part2.CNDProcess.SG
end
