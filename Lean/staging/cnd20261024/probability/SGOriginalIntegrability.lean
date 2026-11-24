import staging.cnd20261024.probability.SGOriginalModel

open MeasureTheory Filter ProbabilityTheory Finset
open scoped ProbabilityTheory BigOperators NNReal
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SGModel
section Integrability
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}
variable (h : SGModel ℱ μ θ R M D σ σe) (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1)
include hb

omit hb in
lemma noise_exponent_measurable (n : ℕ) (i : ι) (t : ℝ) :
    Measurable[h.encoded n] (fun ω => Real.exp (t * Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω)) :=
  Real.measurable_exp.comp ((((Directional.scoreAt_measurable h.toM1Model.statistics b n i).mono
    ((h.past_le_pre n).trans (h.pre_le_encoded n)) le_rfl).const_mul t).mul (h.combined_measurable n i))

lemma noise_exponent_integrable (n : ℕ) (i : ι) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω)) μ := by
  apply ((h.combined_exp_integrable n i |t|).add (h.combined_exp_integrable n i (-|t|))).mono'
    (((h.noise_exponent_measurable b n i t).mono ((h.encoded_le_next n).trans (ℱ.le (n + 1))) le_rfl).stronglyMeasurable.aestronglyMeasurable)
  apply Eventually.of_forall
  intro ω
  change ‖Real.exp (t * Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω)‖ ≤
    Real.exp (|t| * h.combinedNoise n i ω) + Real.exp (-|t| * h.combinedNoise n i ω)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hs : |t * Directional.scoreAt h.toM1Model.statistics b n i ω| ≤ |t| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Directional.scoreAt_bound h.toM1Model.statistics b hb n i ω) (abs_nonneg t)
  by_cases hn : 0 ≤ h.combinedNoise n i ω
  · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hs) hn)
    exact he.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
  · have hcoef : -|t| ≤ t * Directional.scoreAt h.toM1Model.statistics b n i ω := by
      linarith [(abs_le.mp hs).1]
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hcoef (le_of_lt (lt_of_not_ge hn)))
    exact he.trans (le_add_of_nonneg_left (Real.exp_nonneg _))

omit hb in
lemma full_exponent_measurable (n : ℕ) (i : ι) (t : ℝ) :
    Measurable[h.encoded n] (fun ω => Real.exp (t *
      (h.signalAt b n i ω + Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω))) :=
  Real.measurable_exp.comp ((((h.signalAt_measurable b n i).mono (h.pre_le_encoded n) le_rfl).add
    (((Directional.scoreAt_measurable h.toM1Model.statistics b n i).mono
      ((h.past_le_pre n).trans (h.pre_le_encoded n)) le_rfl).mul (h.combined_measurable n i))).const_mul t)

lemma signal_exponent_bound (n : ℕ) (i : ι) (t : ℝ) (ω : Ω) :
    |Real.exp (t * h.signalAt b n i ω)| ≤ Real.exp (|t| * (2 * (R + M))) := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h.signalAt_bound b hb n i ω) (abs_nonneg t))

lemma full_exponent_integrable (n : ℕ) (i : ι) (t : ℝ) :
    Integrable (fun ω => Real.exp (t *
      (h.signalAt b n i ω + Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω))) μ := by
  have hprod := (h.noise_exponent_integrable b hb n i t).bdd_mul'
    (Real.continuous_exp.comp_aestronglyMeasurable
      (((h.signalAt_measurable b n i).mono (h.toM1Model.toSamplingModel.pre_le n) le_rfl).stronglyMeasurable.aestronglyMeasurable.const_mul t))
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using h.signal_exponent_bound b hb n i t ω)
  have heq : (fun ω => Real.exp (t *
      (h.signalAt b n i ω + Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω))) =
      (fun ω => Real.exp (t * h.signalAt b n i ω) *
        Real.exp (t * Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω)) := by
    funext ω
    rw [mul_add, Real.exp_add, mul_assoc]
  rw [heq]
  exact hprod

/-- All-parameter exp integrability of the actual selected CND increment,
derived from coordinate noise moments and the bounded real signal. -/
theorem direction_exp_integrable (n : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * h.directionIncrement b n ω)) μ :=
  PairConfidence.selected_integrable ((h.action_measurable n).mono (h.toM1Model.toSamplingModel.action_le n) le_rfl)
    (fun i => h.full_exponent_integrable b hb n i t)

omit hb in
theorem direction_measurable (n : ℕ) : Measurable[ℱ (n + 1)] (h.directionIncrement b n) := by
  change Measurable[ℱ (n + 1)] (fun ω =>
    (fun i ω => h.signalAt b n i ω + Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω) (h.action n ω) ω)
  exact PairConfidence.selected_measurable (m₀ := m₀) (m := ℱ (n + 1))
    (A := h.action n) (f := fun i ω => h.signalAt b n i ω +
      Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω)
    ((h.action_measurable n).mono (h.action_le_next n) le_rfl)
    (fun i => ((h.signalAt_measurable b n i).mono ((h.pre_le_action n).trans (h.action_le_next n)) le_rfl).add
      (((Directional.scoreAt_measurable h.toM1Model.statistics b n i).mono (ℱ.mono (Nat.le_succ n)) le_rfl).mul
        ((h.combined_measurable n i).mono (h.encoded_le_next n) le_rfl)))

end Integrability
end Part2.CNDProbability.SGModel
