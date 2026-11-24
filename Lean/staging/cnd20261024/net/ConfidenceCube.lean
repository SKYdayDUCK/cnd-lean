import staging.cnd20261024.net.UniformDirections
import staging.cnd20261024.graph.ActualGraphBridge

noncomputable section
set_option maxHeartbeats 1200000
open Finset Matrix
open scoped Matrix
namespace Part2.CNDNet
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem inverseInformation_symmetric (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ CND.simplex) (n : ℕ) (i j : ι) :
    CNDPhysical.inverseInformation p n i j = CNDPhysical.inverseInformation p n j i := by
  have hB := (CNDPhysical.information_posDef p hp n).inv.posSemidef
  have hs := congrFun (congrFun hB.isHermitian i) j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using hs.symm

theorem inverse_contrast_evaluation (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ CND.simplex) (n : ℕ) (v : ι → ℝ) (a b : ι) :
    (CNDPhysical.inverseInformation p n *ᵥ v) a -
      (CNDPhysical.inverseInformation p n *ᵥ v) b =
        ∑ i, CNDGraphBridge.inverseContrast p n a b i * v i := by
  have hu (i : ι) : CNDGraphBridge.inverseContrast p n a b i =
      CNDPhysical.inverseInformation p n a i - CNDPhysical.inverseInformation p n b i := by
    simp only [CNDGraphBridge.inverseContrast, Matrix.mulVec, dotProduct,
      CNDPhysical.contrast, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [inverseInformation_symmetric p hp n i a, inverseInformation_symmetric p hp n i b]
  simp only [hu, sub_mul, Finset.sum_sub_distrib, Matrix.mulVec, dotProduct]

/-- The estimator is computed from the score S=(sum C)theta+Z. It is not a free error vector. -/
def scoreEstimator (p : ℕ → ι → ℝ) (n : ℕ) (θ Z : ι → ℝ) : ι → ℝ :=
  CNDPhysical.inverseInformation p n *ᵥ
    (((∑ t ∈ Finset.range n, CNDPhysical.covariance (p t)) *ᵥ θ) + Z)

theorem score_estimator_error (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ CND.simplex) (n : ℕ) (θ Z : ι → ℝ) (a b : ι) :
    (scoreEstimator p n θ Z a - scoreEstimator p n θ Z b) - (θ a - θ b) =
      (∑ i, CNDGraphBridge.inverseContrast p n a b i * Z i) -
        ∑ i, CNDGraphBridge.inverseContrast p n a b i * θ i := by
  have hfull : scoreEstimator p n θ Z = θ +
      CNDPhysical.inverseInformation p n *ᵥ (Z - θ) := by
    have he : ((∑ t ∈ Finset.range n, CNDPhysical.covariance (p t)) *ᵥ θ) + Z =
        CNDPhysical.information p n *ᵥ θ + (Z - θ) := by
      simp [CNDPhysical.information, Matrix.add_mulVec]
      abel
    rw [scoreEstimator, he, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      (CNDPhysical.inverseInformation_mul p hp n).1, Matrix.one_mulVec]
  rw [hfull]
  have hh := inverse_contrast_evaluation p hp n (Z - θ) a b
  simp only [Pi.add_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at *
  linarith

def contrastCube (θhat : ι → ℝ) (ρ : ι → ι → ℝ) (R : ℝ) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ R) ∧
    ∀ i j, |(θhat i - θhat j) - (x i - x j)| ≤ ρ i j}

/-- Full-direction confidence permits the history-dependent inverse direction. -/
theorem full_direction_implies_pair_radius (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ CND.simplex) (n : ℕ) (θ Z : ι → ℝ)
    {H L R : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ R)
    (hfull : ∀ u : ι → ℝ, (∑ i, u i) = 0 →
      |∑ i, u i * Z i| ≤ 2 * H * Real.sqrt
        (L * CND.quadratic (CNDPhysical.information p n) u) + 4 * H * L * oscillation u)
    (a b : ι) :
    |(scoreEstimator p n θ Z a - scoreEstimator p n θ Z b) - (θ a - θ b)| ≤
      CNDPhysical.pairRadius p n H L R a b := by
  let u := CNDGraphBridge.inverseContrast p n a b
  have hz := hfull u (CNDGraphBridge.inverseContrast_zero_sum p hp n a b)
  have he := CNDGraphBridge.actual_inverse_energy_eq_resistance p hp n a b
  have ho : oscillation u ≤ CNDPhysical.resistance p n a b := by
    apply (pi_norm_le_iff_of_nonneg (CNDPhysical.actual_resistance_nonneg p hp n a b)).2
    intro ij
    exact CNDGraphBridge.actual_inverse_pairwise_bound p hp n a b ij.1 ij.2
  have hb := CNDGraphBridge.actual_regularization_bias_loose p hp n a b θ R hR hθ
  rw [score_estimator_error p hp n θ Z]
  have hh := abs_sub (∑ i, u i * Z i) (∑ i, u i * θ i)
  rw [he] at hz
  unfold CNDPhysical.pairRadius
  nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * H * L) (sub_nonneg.mpr ho)]

theorem true_parameter_mem_cube (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ CND.simplex) (n : ℕ) (θ Z : ι → ℝ)
    {H L R : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ R)
    (hfull : ∀ u : ι → ℝ, (∑ i, u i) = 0 →
      |∑ i, u i * Z i| ≤ 2 * H * Real.sqrt
        (L * CND.quadratic (CNDPhysical.information p n) u) + 4 * H * L * oscillation u) :
    θ ∈ contrastCube (scoreEstimator p n θ Z) (CNDPhysical.pairRadius p n H L R) R := by
  exact ⟨hθ, full_direction_implies_pair_radius p hp n θ Z hH hL hR hθ hfull⟩

section ActualModel
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
  {ℱ : MeasureTheory.Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ}

def actualScoreSum (h : CNDProbability.M1Model ℱ μ θ R M D)
    (n : ℕ) (ω : Ω) : ι → ℝ := fun i =>
  ∑ t ∈ Finset.range n, CNDPhysical.score (h.p t) θ (h.drift t) (h.error t) (h.action t) i ω

def actualEstimator (h : CNDProbability.M1Model ℱ μ θ R M D)
    (n : ℕ) (ω : Ω) : ι → ℝ :=
  CNDPhysical.inverseInformation (fun t i => h.p t i ω) n *ᵥ actualScoreSum h n ω

theorem covarianceTheta_eq_matrix (h : CNDProbability.M1Model ℱ μ θ R M D)
    (t : ℕ) (ω : Ω) (i : ι) :
    CNDPhysical.covarianceTheta (h.p t) θ i ω =
      (CNDPhysical.covariance (fun j => h.p t j ω) *ᵥ θ) i := by
  simp only [CNDPhysical.covarianceTheta, CNDPhysical.covariance, Matrix.mulVec,
    dotProduct, sub_mul, mul_sub, ite_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc, Finset.mul_sum]

theorem actual_score_decomposition (h : CNDProbability.M1Model ℱ μ θ R M D)
    (n : ℕ) (ω : Ω) :
    actualScoreSum h n ω =
      ((∑ t ∈ Finset.range n, CNDPhysical.covariance (fun i => h.p t i ω)) *ᵥ θ) +
        (fun i => h.coordinateSum n i ω) := by
  ext i
  simp only [actualScoreSum, CNDProbability.M1Model.coordinateSum,
    CNDProbability.M1Model.coordinateIncrement, Pi.add_apply, Finset.sum_sub_distrib,
    covarianceTheta_eq_matrix, Matrix.sum_mulVec, Finset.sum_apply]
  ring

theorem actual_estimator_eq_scoreEstimator (h : CNDProbability.M1Model ℱ μ θ R M D)
    (n : ℕ) (ω : Ω) :
    actualEstimator h n ω = scoreEstimator (fun t i => h.p t i ω) n θ
      (fun i => h.coordinateSum n i ω) := by
  rw [actualEstimator, actual_score_decomposition]
  rfl

/-- Original CND-MAIN (11)--(13), including actual score/inverse estimator and cube membership,
on the original sample space under the strong M1 conditional model. -/
theorem actual_confidence_cube_event (h : CNDProbability.M1Model ℱ μ θ R M D)
    (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ Fintype.card ι)
    (hH : 0 < R + M + D) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ G : Set Ω, μ.real Gᶜ ≤ δ ∧ ∀ ω ∈ G, ∀ n ≤ T,
      θ ∈ contrastCube (actualEstimator h n ω)
        (CNDPhysical.pairRadius (fun t i => h.p t i ω) n (R + M + D)
          (paperLc ι T δ) R) R := by
  obtain ⟨G, hG, hbound⟩ := actual_uniform_direction_event_paper h T hT hK hH hδ hδ1
  refine ⟨G, hG, ?_⟩
  intro ω hω n hn
  rw [actual_estimator_eq_scoreEstimator]
  exact true_parameter_mem_cube (fun t i => h.p t i ω)
    (fun t => ⟨h.p_nonneg t ω, h.p_sum t ω⟩) n θ (fun i => h.coordinateSum n i ω)
    hH.le (le_trans zero_le_one (paper_Lc_budget (ι := ι) T hδ hδ1).1)
    h.R_nonneg h.theta_range (hbound ω hω n hn)

end ActualModel

end Part2.CNDNet
