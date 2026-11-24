import staging.cnd20261024.process.ActualInvariants
import staging.cnd20261024.process.RadiusHistory

/-! Final process-to-probability-library interface. All decisions below are
the concrete original maps; H is the actual residual envelope R+M+D. -/
noncomputable section
open MeasureTheory
namespace Part2.CNDProcess
variable {d K : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D L W : ℝ}

def actualM1Model (h : PotentialInputs ℱ θ R M D) (hW : 0 ≤ W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hm : OriginalM1 (concreteMaps (R + M + D) L R W h.R_nonneg hW)
      (treeData d K W R) h μ) : CNDProbability.M1Model ℱ μ θ R M D :=
  OriginalM1.toM1Model _ _ h hm

theorem actualModel_probability_computed (h : PotentialInputs ℱ θ R M D) (hW : 0 ≤ W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hm : OriginalM1 (concreteMaps (R + M + D) L R W h.R_nonneg hW)
      (treeData d K W R) h μ) (t : ℕ) (a : Fin K) :
    (actualM1Model h hW μ hm).p t a =
      runProbability (concreteMaps (R + M + D) L R W h.R_nonneg hW)
        (treeData d K W R) h.feedback t a := rfl

theorem actualModel_residual_observed (h : PotentialInputs ℱ θ R M D) (hW : 0 ≤ W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hm : OriginalM1 (concreteMaps (R + M + D) L R W h.R_nonneg hW)
      (treeData d K W R) h μ) (t : ℕ) :
    (actualM1Model h hW μ hm).toSamplingModel.residual t = h.residual t := rfl

theorem actualModel_statistic_integrable (h : PotentialInputs ℱ θ R M D) (hW : 0 ≤ W)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ) (a : Fin K) :
    Integrable (runS (concreteMaps (R + M + D) L R W h.R_nonneg hW)
      (treeData d K W R) h.feedback t a) μ :=
  runS_integrable _ _ h.feedback (R + M + D)
    (by linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg]) h.residual_bound t a

end Part2.CNDProcess
end
