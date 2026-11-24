import staging.cnd20261024.probability.ModelBridge

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators
set_option maxHeartbeats 800000

namespace Part2.CNDProbability
section FiniteAlgebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma directionScore_coordinate (p b : ι → ℝ) (a : ι) :
    directionScore p b a = ∑ i, b i * ((if a = i then 1 else 0) - p i) := by
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, directionScore, weighted]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma directionMean_coordinate (p b θ : ι → ℝ) :
    directionMean p b θ = ∑ i, b i * (p i * (θ i - weighted p θ)) := by
  rw [directionMean_covariance]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · calc
      weighted p b * weighted p θ = (∑ i, b i * p i) * weighted p θ := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = ∑ i, (b i * p i) * weighted p θ := Finset.sum_mul _ _ _
      _ = _ := by apply Finset.sum_congr rfl; intros; ring

end FiniteAlgebra

section Model
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}

namespace M1Model
variable (h : M1Model ℱ μ θ R M D)

noncomputable def coordinateIncrement (n : ℕ) (i : ι) (ω : Ω) : ℝ :=
  CNDPhysical.score (h.p n) θ (h.drift n) (h.error n) (h.action n) i ω -
    CNDPhysical.covarianceTheta (h.p n) θ i ω

noncomputable def coordinateSum (n : ℕ) (i : ι) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n, h.coordinateIncrement t i ω

/-- The scalar CND increment is the linear functional of the actual vector
XY-Cθ, including its encoded observation on the same sample path. -/
theorem direction_increment_eq_coordinates (b : ι → ℝ) (n : ℕ) (ω : Ω) :
    Directional.increment h.statistics b n ω = ∑ i, b i * h.coordinateIncrement n i ω := by
  rw [h.direction_increment_formula]
  change directionScore (fun a => h.p n a ω) b (h.action n ω) *
    (θ (h.action n ω) + h.drift n ω - h.error n (h.action n ω) ω) -
    directionMean (fun a => h.p n a ω) b θ = _
  rw [directionScore_coordinate, directionMean_coordinate]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [coordinateIncrement, CNDPhysical.score, CNDPhysical.covarianceTheta,
    PairConfidence.actionIndicator, weighted]
  ring

theorem direction_sum_eq_coordinates (b : ι → ℝ) (n : ℕ) (ω : Ω) :
    Bernstein.sumProcess (Directional.increment h.statistics b) n ω = ∑ i, b i * h.coordinateSum n i ω := by
  simp only [Bernstein.sumProcess, h.direction_increment_eq_coordinates]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.mul_sum _ _ _).symm

theorem direction_increment_add (b c : ι → ℝ) (n : ℕ) (ω : Ω) :
    Directional.increment h.statistics (b + c) n ω =
      Directional.increment h.statistics b n ω + Directional.increment h.statistics c n ω := by
  simp only [h.direction_increment_eq_coordinates, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem direction_increment_smul (a : ℝ) (b : ι → ℝ) (n : ℕ) (ω : Ω) :
    Directional.increment h.statistics (a • b) n ω = a * Directional.increment h.statistics b n ω := by
  simp only [h.direction_increment_eq_coordinates, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem direction_sum_add (b c : ι → ℝ) (n : ℕ) (ω : Ω) :
    Bernstein.sumProcess (Directional.increment h.statistics (b + c)) n ω =
      Bernstein.sumProcess (Directional.increment h.statistics b) n ω +
      Bernstein.sumProcess (Directional.increment h.statistics c) n ω := by
  simp only [Bernstein.sumProcess, h.direction_increment_add, Finset.sum_add_distrib]

theorem direction_sum_smul (a : ℝ) (b : ι → ℝ) (n : ℕ) (ω : Ω) :
    Bernstein.sumProcess (Directional.increment h.statistics (a • b)) n ω =
      a * Bernstein.sumProcess (Directional.increment h.statistics b) n ω := by
  simp only [Bernstein.sumProcess, h.direction_increment_smul, Finset.mul_sum]

end M1Model
end Model
end Part2.CNDProbability
