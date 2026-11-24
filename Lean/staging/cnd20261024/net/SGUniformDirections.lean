import staging.cnd20261024.net.ConfidenceCube
import staging.cnd20261024.net.SGNetExtension
import staging.cnd20261024.probability.SGOriginalUniform

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter ProbabilityTheory Finset
open scoped ProbabilityTheory BigOperators NNReal Matrix

namespace Part2.CNDSGNet
open CNDNet

variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}

/-- The actual unbounded observation score, including physical noise even at R=0. -/
def actualScoreSum (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (n : ℕ) (ω : Ω) : ι → ℝ := fun i => ∑ t ∈ Finset.range n,
      (PairConfidence.actionIndicator (h.action t) i ω - h.p t i ω) *
        (θ (h.action t ω) + h.drift t ω + h.noise t (h.action t ω) ω -
          h.error t (h.action t ω) ω)

def actualEstimator (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (n : ℕ) (ω : Ω) : ι → ℝ :=
  CNDPhysical.inverseInformation (fun t i => h.p t i ω) n *ᵥ actualScoreSum h n ω

/-- R=0 removes only the unknown parameter contrasts, not physical observation noise. -/
theorem zero_range_theta (h : CNDProbability.SGModel ℱ μ θ R M D σ σe) (hR : R = 0) :
    θ = 0 := by
  funext i
  have hi := h.theta_range i
  rw [hR] at hi
  exact le_antisymm hi.2 hi.1

theorem zero_range_theta_contrast (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (hR : R = 0) (i j : ι) : θ i - θ j = 0 := by
  rw [zero_range_theta h hR]
  simp only [Pi.zero_apply, sub_self]

theorem zero_range_skip_statistics_cube (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (hR : R = 0) (ρ : ι → ι → ℝ) (hρ : ∀ i j, 0 ≤ ρ i j) :
    θ ∈ contrastCube (0 : ι → ℝ) ρ R := by
  rw [zero_range_theta h hR, hR]
  constructor
  · intro i
    exact ⟨le_rfl, le_rfl⟩
  · intro i j
    simpa only [Pi.zero_apply, sub_self, abs_zero] using hρ i j

theorem actual_score_decomposition (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (n : ℕ) (ω : Ω) :
    actualScoreSum h n ω =
      ((∑ t ∈ Finset.range n, CNDPhysical.covariance (fun i => h.p t i ω)) *ᵥ θ) +
        (fun i => h.coordinateSum n i ω) := by
  ext i
  simp only [actualScoreSum, CNDProbability.SGModel.coordinateSum,
    CNDProbability.SGModel.coordinateIncrement, CNDProbability.M1Model.coordinateIncrement,
    CNDNet.covarianceTheta_eq_matrix h.toM1Model, Matrix.sum_mulVec, Finset.sum_apply,
    Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  dsimp [CNDPhysical.score]
  ring

theorem actual_estimator_eq_scoreEstimator (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (n : ℕ) (ω : Ω) :
    actualEstimator h n ω = CNDNet.scoreEstimator (fun t i => h.p t i ω) n θ
      (fun i => h.coordinateSum n i ω) := by
  rw [actualEstimator, actual_score_decomposition]
  rfl

/-- Exact SG14 on the original sample space for positive Hs, with the original Lc. -/
theorem uniform_direction_event_pos (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2) (hH : 0 < R + M + (ν : ℝ))
    (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ Fintype.card ι)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ G : Set Ω, μ.real Gᶜ ≤ δ ∧
      ∀ ω ∈ G, ∀ n ≤ T, ∀ u : ι → ℝ, (∑ i, u i) = 0 →
        |∑ i, u i * h.coordinateSum n i ω| ≤
          4 * (R + M + (ν : ℝ)) * Real.sqrt (paperLc ι T δ * CND.quadratic
            (CNDPhysical.information (fun t i => h.p t i ω) n) u) +
              16 * (R + M + (ν : ℝ)) * paperLc ι T δ * oscillation u := by
  classical
  let L := paperLc ι T δ
  obtain ⟨hL, hbudget⟩ := paper_Lc_budget (ι := ι) T hδ hδ1
  obtain ⟨s, hs, hcard, hextend⟩ := exists_SG_paper_net_extension (ι := ι) T hT hK
  let α := {b // b ∈ s}
  let b : α → ι → ℝ := fun a => a.val.val
  let bad : Set Ω := {ω | ∃ a : α, ∃ n ≤ T,
    2 * Real.sqrt ((2 * (R + M + (ν : ℝ))^2) * (1 + Bernstein.sumProcess
      (CNDProbability.Directional.information h.toM1Model.statistics (b a)) n ω) * L) +
      L / (1 / (8 * (R + M + (ν : ℝ)))) ≤
        |Bernstein.sumProcess (h.directionIncrement (b a)) n ω|}
  have hb : ∀ a i j, |b a i - b a j| ≤ 1 := by
    intro a i j
    exact (pairwise_le_oscillation a.val.val i j).trans_eq (hs a.val a.property)
  have hprob := h.finite_direction_family b hb ν hν hH T (show 0 < L by dsimp [L]; linarith)
  refine ⟨badᶜ, ?_, ?_⟩
  · simp only [compl_compl]
    have hca : (Fintype.card α : ℝ) ≤ paperNetCard ι T := by simpa [α] using hcard
    exact (hprob.trans (mul_le_mul_of_nonneg_right hca (by positivity))).trans hbudget
  · intro ω hω n hn u hu
    have hp : ∀ t, (fun i => h.p t i ω) ∈ CND.simplex :=
      fun t => ⟨h.p_nonneg t ω, h.p_sum t ω⟩
    apply hextend (fun t i => h.p t i ω) hp n hn (R + M + (ν : ℝ)) L hH.le hL
      (fun i => h.coordinateSum n i ω) _ u hu
    intro v hv
    let a : α := ⟨v, hv⟩
    have hnot : ¬ (2 * Real.sqrt ((2 * (R + M + (ν : ℝ))^2) * (1 +
        Bernstein.sumProcess (CNDProbability.Directional.information h.toM1Model.statistics (b a)) n ω) * L) +
        L / (1 / (8 * (R + M + (ν : ℝ)))) ≤
          |Bernstein.sumProcess (h.directionIncrement (b a)) n ω|) := by
      intro hc
      exact hω ⟨a, n, hn, hc⟩
    have hstrict := lt_of_not_ge hnot
    rw [h.direction_sum_eq_coordinates] at hstrict
    have hbase := square_sum_lower v.val
    rw [hs v hv] at hbase
    have he := energy_square_variance (fun t i => h.p t i ω) hp n v.val
    have hq : 0 ≤ ∑ t ∈ Finset.range n,
        CNDProbability.directionVariance (fun i => h.p t i ω) v.val :=
      Finset.sum_nonneg fun t _ => CNDProbability.directionVariance_nonneg _ _ (hp t).1
    have hqE : 1 + (∑ t ∈ Finset.range n,
        CNDProbability.directionVariance (fun i => h.p t i ω) v.val) ≤
          2 * (informationEnergy (fun t i => h.p t i ω) n v.val)^2 := by nlinarith
    exact hstrict.le.trans (CNDProbability.SGModel.sg_radius_le_energy hH
      (show 0 ≤ L by dsimp [L]; linarith) (apply_nonneg _ _) hq hqE)

/-- Zero conditional sub-Gaussian scale forces the combined noise to vanish almost surely;
this is derived from the conditional kernel MGF and not a zero-noise model premise. -/
theorem combined_noise_zero_ae (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (hscale : σ^2 + σe^2 = 0) (n : ℕ) (i : ι) :
    h.combinedNoise n i =ᵐ[μ] 0 := by
  have hsg : HasSubgaussianMGF (h.combinedNoise n i) 0 μ := by
    constructor
    · exact h.combined_exp_integrable n i
    · intro t
      have hc := h.combined_conditional_mgf n i t
      rw [hscale] at hc
      have hi := integral_mono_ae (integrable_condExp (μ := μ))
        (integrable_const (Real.exp ((0 : ℝ) * t^2 / 2))) hc
      rw [integral_condExp (h.toM1Model.toSamplingModel.pre_le n)] at hi
      simpa [ProbabilityTheory.mgf] using hi
  exact hsg.ae_eq_zero_of_hasSubgaussianMGF_zero

theorem coordinate_sum_zero_ae_of_Hs_zero (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2) (hH : R + M + (ν : ℝ) = 0) :
    ∀ᵐ ω ∂μ, ∀ n i, h.coordinateSum n i ω = 0 := by
  have hR : R = 0 := by linarith [h.R_nonneg, h.M_nonneg, ν.coe_nonneg]
  have hM : M = 0 := by linarith [h.R_nonneg, h.M_nonneg, ν.coe_nonneg]
  have hν0 : (ν : ℝ) = 0 := by linarith [h.R_nonneg, h.M_nonneg, ν.coe_nonneg]
  have hscale : σ^2 + σe^2 = 0 := by rw [← hν, hν0]; norm_num
  have hθ : θ = 0 := by
    funext i
    have hi := h.theta_range i
    simp only [hR] at hi
    exact le_antisymm hi.2 hi.1
  have hz (n : ℕ) (ω : Ω) : h.drift n ω = 0 := by
    have hd := h.drift_range n ω
    exact le_antisymm (hd.2.trans_eq hM) hd.1
  have hall : ∀ᵐ ω ∂μ, ∀ n i, h.combinedNoise n i ω = 0 := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro i
    exact combined_noise_zero_ae h hscale n i
  filter_upwards [hall] with ω hω
  intro n i
  apply Finset.sum_eq_zero
  intro t _
  have he : h.noise t (h.action t ω) ω = h.error t (h.action t ω) ω :=
    sub_eq_zero.mp (hω t (h.action t ω))
  dsimp [CNDProbability.SGModel.coordinateIncrement, CNDProbability.M1Model.coordinateIncrement,
    CNDPhysical.score, CNDPhysical.covarianceTheta]
  simp only [hθ, Pi.zero_apply, hz, he, mul_zero, Finset.sum_const_zero, zero_sub, zero_add,
    sub_zero]
  ring

/-- Full SG14, including the Hs=0 branch, with no positivity restriction on Hs. -/
theorem uniform_direction_event (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ Fintype.card ι)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ G : Set Ω, μ.real Gᶜ ≤ δ ∧
      ∀ ω ∈ G, ∀ n ≤ T, ∀ u : ι → ℝ, (∑ i, u i) = 0 →
        |∑ i, u i * h.coordinateSum n i ω| ≤
          4 * (R + M + (ν : ℝ)) * Real.sqrt (paperLc ι T δ * CND.quadratic
            (CNDPhysical.information (fun t i => h.p t i ω) n) u) +
              16 * (R + M + (ν : ℝ)) * paperLc ι T δ * oscillation u := by
  have hH0 : 0 ≤ R + M + (ν : ℝ) := by linarith [h.R_nonneg, h.M_nonneg, ν.coe_nonneg]
  rcases hH0.eq_or_lt with hzero | hpos
  · have hzero' := hzero.symm
    have hae := coordinate_sum_zero_ae_of_Hs_zero h ν hν hzero'
    let G : Set Ω := {ω | ∀ n i, h.coordinateSum n i ω = 0}
    have hG : μ Gᶜ = 0 := by simpa only [G, Set.compl_setOf] using (ae_iff.mp hae)
    refine ⟨G, ?_, ?_⟩
    · simp only [Measure.real, hG, ENNReal.toReal_zero]
      exact hδ.le
    · intro ω hω n hn u hu
      simp only [hzero', mul_zero, zero_mul, add_zero, hω n, Finset.sum_const_zero, abs_zero]
      exact le_refl 0
  · exact uniform_direction_event_pos h ν hν hpos T hT hK hδ hδ1

/-- The SG constants are exactly the old bounded confidence form evaluated at L=4Lc. -/
theorem sg_full_direction_to_scaled_form (p : ℕ → ι → ℝ) (n : ℕ) (Z : ι → ℝ)
    {H L : ℝ} (hL : 0 ≤ L)
    (hfull : ∀ u : ι → ℝ, (∑ i, u i) = 0 →
      |∑ i, u i * Z i| ≤ 4 * H * Real.sqrt (L * CND.quadratic (CNDPhysical.information p n) u) +
        16 * H * L * oscillation u) :
    ∀ u : ι → ℝ, (∑ i, u i) = 0 →
      |∑ i, u i * Z i| ≤ 2 * H * Real.sqrt ((4 * L) * CND.quadratic
        (CNDPhysical.information p n) u) + 4 * H * (4 * L) * oscillation u := by
  intro u hu
  have hr : Real.sqrt ((4 * L) * CND.quadratic (CNDPhysical.information p n) u) =
      2 * Real.sqrt (L * CND.quadratic (CNDPhysical.information p n) u) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [hr]
  nlinarith [hfull u hu]

theorem sg_pairRadius_eq (p : ℕ → ι → ℝ) (n : ℕ) (H L R : ℝ) (i j : ι) :
    CNDPhysical.pairRadius p n H (4 * L) R i j =
      4 * H * Real.sqrt (L * CNDPhysical.resistance p n i j) +
        (16 * H * L + R * (Fintype.card ι : ℝ)) * CNDPhysical.resistance p n i j := by
  unfold CNDPhysical.pairRadius
  rw [mul_assoc 4 L, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring

/-- Original SG all-time pairwise radius and true-parameter cube for the actual unbounded score.
Hs may vanish; R=0 keeps the actual noise in the estimator. -/
theorem confidence_cube_event (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ Fintype.card ι)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ G : Set Ω, μ.real Gᶜ ≤ δ ∧ ∀ ω ∈ G, ∀ n ≤ T,
      θ ∈ contrastCube (actualEstimator h n ω)
        (CNDPhysical.pairRadius (fun t i => h.p t i ω) n (R + M + (ν : ℝ))
          (4 * paperLc ι T δ) R) R := by
  obtain ⟨G, hG, hfull⟩ := uniform_direction_event h ν hν T hT hK hδ hδ1
  refine ⟨G, hG, ?_⟩
  intro ω hω n hn
  rw [actual_estimator_eq_scoreEstimator]
  have hL : 0 ≤ paperLc ι T δ := (zero_le_one.trans (paper_Lc_budget (ι := ι) T hδ hδ1).1)
  exact CNDNet.true_parameter_mem_cube (fun t i => h.p t i ω)
    (fun t => ⟨h.p_nonneg t ω, h.p_sum t ω⟩) n θ (fun i => h.coordinateSum n i ω)
    (by linarith [h.R_nonneg, h.M_nonneg, ν.coe_nonneg]) (by positivity)
    h.R_nonneg h.theta_range (sg_full_direction_to_scaled_form _ _ _ hL (hfull ω hω n hn))

/-- One original-space good event simultaneously carries SG14, the actual inverse-score
pairwise radius, and membership of the true parameter in the actual cube. -/
theorem confidence_event (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)
    (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ Fintype.card ι)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ G : Set Ω, μ.real Gᶜ ≤ δ ∧ ∀ ω ∈ G, ∀ n ≤ T,
      (∀ u : ι → ℝ, (∑ i, u i) = 0 →
        |∑ i, u i * h.coordinateSum n i ω| ≤
          4 * (R + M + (ν : ℝ)) * Real.sqrt (paperLc ι T δ * CND.quadratic
            (CNDPhysical.information (fun t i => h.p t i ω) n) u) +
              16 * (R + M + (ν : ℝ)) * paperLc ι T δ * oscillation u) ∧
      (∀ i j, |(actualEstimator h n ω i - actualEstimator h n ω j) - (θ i - θ j)| ≤
        4 * (R + M + (ν : ℝ)) * Real.sqrt
          (paperLc ι T δ * CNDPhysical.resistance (fun t i => h.p t i ω) n i j) +
        (16 * (R + M + (ν : ℝ)) * paperLc ι T δ + R * (Fintype.card ι : ℝ)) *
          CNDPhysical.resistance (fun t i => h.p t i ω) n i j) ∧
      θ ∈ contrastCube (actualEstimator h n ω)
        (CNDPhysical.pairRadius (fun t i => h.p t i ω) n (R + M + (ν : ℝ))
          (4 * paperLc ι T δ) R) R := by
  obtain ⟨G, hG, hfull⟩ := uniform_direction_event h ν hν T hT hK hδ hδ1
  refine ⟨G, hG, ?_⟩
  intro ω hω n hn
  have hL : 0 ≤ paperLc ι T δ := zero_le_one.trans (paper_Lc_budget (ι := ι) T hδ hδ1).1
  have hcube : θ ∈ contrastCube (actualEstimator h n ω)
      (CNDPhysical.pairRadius (fun t i => h.p t i ω) n (R + M + (ν : ℝ))
        (4 * paperLc ι T δ) R) R := by
    rw [actual_estimator_eq_scoreEstimator]
    exact CNDNet.true_parameter_mem_cube (fun t i => h.p t i ω)
      (fun t => ⟨h.p_nonneg t ω, h.p_sum t ω⟩) n θ (fun i => h.coordinateSum n i ω)
      (by linarith [h.R_nonneg, h.M_nonneg, ν.coe_nonneg]) (by positivity)
      h.R_nonneg h.theta_range (sg_full_direction_to_scaled_form _ _ _ hL (hfull ω hω n hn))
  refine ⟨hfull ω hω n hn, ?_, hcube⟩
  intro i j
  have hp := hcube.2 i j
  rwa [sg_pairRadius_eq] at hp

end Part2.CNDSGNet
