import staging.cnd20261024.process.ConcreteMaps

/-! Shared total Borel decision maps for the bounded and SG exponential
runs. The confidence scale and radius scale act on the raw pair radius;
the latter scale is inside the saturation exponential. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators

namespace Part2.ExponentialScaledMaps
open CNDProcess
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def confidence (H L R c : ℝ) (hR : 0 ≤ R) (s : Stats ι) : Vec ι :=
  CNDConfidenceSlabs.canonicalConfidence ι R hR
    (StatisticalMaps.estimate s, fun i j => c * StatisticalMaps.rawPairRadius H L R s i j)

def radius (H L R scale : ℝ) (s : Stats ι) (i j : ι) : ℝ :=
  CNDPhysical.saturatedRadius R (scale * StatisticalMaps.rawPairRadius H L R s i j)

theorem measurable_scaledPairRadius (H L R c : ℝ) :
    Measurable (fun s : Stats ι => fun i j => c * StatisticalMaps.rawPairRadius H L R s i j) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact measurable_const.mul ((measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp (StatisticalMaps.measurable_rawPairRadius H L R)))

theorem measurable_confidence (H L R c : ℝ) (hR : 0 ≤ R) :
    Measurable (confidence (ι := ι) H L R c hR) :=
  (CNDConfidenceSlabs.measurable_canonicalConfidence ι R hR).comp
    (StatisticalMaps.measurable_estimate.prodMk (measurable_scaledPairRadius H L R c))

theorem measurable_radius (H L R scale : ℝ) :
    Measurable (radius (ι := ι) H L R scale) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hm : Measurable (fun s : Stats ι => scale * StatisticalMaps.rawPairRadius H L R s i j) :=
    measurable_const.mul ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (StatisticalMaps.measurable_rawPairRadius H L R)))
  exact (measurable_const.sub (((hm.div_const R).neg).exp)).const_mul _

def decisionMaps {K : ℕ} [Nonempty (Fin K)] (H L R W c scale : ℝ)
    (hR : 0 ≤ R) (hW : 0 ≤ W) : DecisionMaps (Fin K) where
  confidence := confidence H L R c hR
  radius := radius H L R scale
  prox := extendedProx W hW
  transport := ExactGreedyMeasurable.actualTransport W univ_nonempty
  confidence_measurable := measurable_confidence H L R c hR
  radius_measurable := measurable_radius H L R scale
  prox_measurable := measurable_extendedProx W hW
  transport_measurable := ExactGreedyMeasurable.measurable_actualTransport W univ_nonempty
  prox_simplex := extendedProx_simplex W hW

theorem decisionMaps_one {K : ℕ} [Nonempty (Fin K)] (H L R W : ℝ)
    (hR : 0 ≤ R) (hW : 0 ≤ W) :
    decisionMaps (K := K) H L R W 1 1 hR hW = concreteMaps (K := K) H L R W hR hW := by
  unfold decisionMaps concreteMaps
  congr 1
  · funext s
    simp [confidence,StatisticalMaps.actualConfidence]
  · funext s i j
    simp [radius,StatisticalMaps.rawRadius]

#print axioms decisionMaps
#print axioms decisionMaps_one
end Part2.ExponentialScaledMaps
