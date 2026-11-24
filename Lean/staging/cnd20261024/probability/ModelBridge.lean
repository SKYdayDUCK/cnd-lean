import staging.cnd20261024.probability.DirectionalStatistics
import Part2.CNDPhysical

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators

namespace Part2.CNDProbability

section Model
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}

namespace M1Model
variable (h : M1Model ℱ μ θ R M D)

/-- This projection uses only the strong action law when supplying the weak
categorical field. The duplicate inherited law is not used by this projection. -/
noncomputable def statistics : PairConfidence.SamplingModel ℱ μ θ R M D :=
  { h.toSamplingModel with categorical := h.categorical_from_strong }

/-- Strong M1 is also usable after revealing the entire potential encoder
output. This law is needed separately for the public sampling martingale. -/
theorem encoded_selected_expectation (n : ℕ) (f : ι → Ω → ℝ)
    (hfm : ∀ a, StronglyMeasurable[h.encoded n] (f a))
    (hfi : ∀ a, Integrable (f a) μ) :
    μ[fun ω => f (h.action n ω) ω | h.encoded n] =ᵐ[μ]
      fun ω => ∑ a, h.p n a ω * f a ω :=
  PairConfidence.conditional_selected
    ((h.action_measurable n).mono (h.action_le n) le_rfl)
    (h.strong_categorical n) f hfm hfi

theorem public_potential_measurable (n : ℕ) (a : ι) :
    Measurable[h.encoded n] (fun ω => h.publicCost n a ω + h.error n a ω) :=
  ((h.public_measurable n a).mono (h.pre_le_encoded n) le_rfl).add (h.error_encoded n a)

/-- CND's actual scalar variance is exactly the quadratic form of the
existing covariance matrix, so this statistic can connect to its V matrix. -/
theorem direction_information_eq_covariance (b : ι → ℝ) (n : ℕ) (ω : Ω) :
    Directional.information h.statistics b n ω =
      Part2.CND.quadratic (CNDPhysical.covariance (fun a => h.p n a ω)) b := by
  rw [CNDPhysical.covariance_variance _ _ (h.p_sum n ω)]
  rfl

/-- The raw original-space increment uses CND's physical observation and
one subtraction of the reconstructed public cost. -/
theorem direction_increment_formula (b : ι → ℝ) (n : ℕ) (ω : Ω) :
    Directional.increment h.statistics b n ω =
      (b (h.action n ω) - CNDPhysical.coordinateMean (fun a => h.p n a ω) b) *
        (θ (h.action n ω) + h.drift n ω - h.error n (h.action n ω) ω) -
      directionMean (fun a => h.p n a ω) b θ := by
  change (b (h.action n ω) - CNDPhysical.coordinateMean (fun a => h.p n a ω) b) *
    h.toSamplingModel.residual n ω - _ = _
  rw [h.toSamplingModel.residual_eq]
  rfl

theorem direction_data (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1) :
    Bernstein.BoundedIncrements ℱ μ (Directional.increment h.statistics b)
      (fun n ω => (R + M + D) ^ 2 * Directional.information h.statistics b n ω)
      (2 * (R + M + D)) := Directional.bernstein_data h.statistics b hb

end M1Model
end Model
end Part2.CNDProbability
