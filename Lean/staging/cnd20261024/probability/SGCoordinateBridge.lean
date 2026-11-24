import staging.cnd20261024.probability.SGOriginalModel
import staging.cnd20261024.probability.CoordinateBridge

open MeasureTheory Filter ProbabilityTheory Finset
open scoped ProbabilityTheory BigOperators NNReal
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SGModel
section Coordinates
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}
variable (h : SGModel ℱ μ θ R M D σ σe)

noncomputable def coordinateIncrement (n : ℕ) (i : ι) (ω : Ω) : ℝ :=
  h.toM1Model.coordinateIncrement n i ω +
    (PairConfidence.actionIndicator (h.action n) i ω - h.p n i ω) * h.noise n (h.action n ω) ω

noncomputable def coordinateSum (n : ℕ) (i : ι) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n, h.coordinateIncrement t i ω

theorem direction_increment_decomposition (b : ι → ℝ) (n : ℕ) (ω : Ω) :
    h.directionIncrement b n ω = Directional.increment h.toM1Model.statistics b n ω +
      directionScore (fun i => h.p n i ω) b (h.action n ω) * h.noise n (h.action n ω) ω := by
  rw [h.toM1Model.direction_increment_formula]
  dsimp [directionIncrement, signalAt, SGDirectionFiber.signal, combinedNoise,
    Directional.scoreAt, directionScore, directionMean, weighted, CNDPhysical.coordinateMean,
    M1Model.statistics]
  ring

theorem direction_increment_eq_coordinates (b : ι → ℝ) (n : ℕ) (ω : Ω) :
    h.directionIncrement b n ω = ∑ i, b i * h.coordinateIncrement n i ω := by
  rw [h.direction_increment_decomposition, h.toM1Model.direction_increment_eq_coordinates,
    directionScore_coordinate, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [coordinateIncrement, PairConfidence.actionIndicator]
  ring

theorem direction_sum_eq_coordinates (b : ι → ℝ) (n : ℕ) (ω : Ω) :
    Bernstein.sumProcess (h.directionIncrement b) n ω = ∑ i, b i * h.coordinateSum n i ω := by
  simp only [Bernstein.sumProcess, h.direction_increment_eq_coordinates]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.mul_sum _ _ _).symm

theorem direction_sum_add (b c : ι → ℝ) (n : ℕ) (ω : Ω) :
    Bernstein.sumProcess (h.directionIncrement (b + c)) n ω =
      Bernstein.sumProcess (h.directionIncrement b) n ω + Bernstein.sumProcess (h.directionIncrement c) n ω := by
  simp only [h.direction_sum_eq_coordinates, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem direction_sum_smul (a : ℝ) (b : ι → ℝ) (n : ℕ) (ω : Ω) :
    Bernstein.sumProcess (h.directionIncrement (a • b)) n ω = a * Bernstein.sumProcess (h.directionIncrement b) n ω := by
  simp only [h.direction_sum_eq_coordinates, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

end Coordinates
end Part2.CNDProbability.SGModel
