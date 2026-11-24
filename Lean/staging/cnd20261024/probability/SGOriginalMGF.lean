import staging.cnd20261024.probability.SGOriginalIntegrability
import staging.cnd20261024.probability.SGFiniteExponential
import staging.cnd20261024.sg_random.RandomCoefficient

open MeasureTheory Filter ProbabilityTheory Finset
open scoped ProbabilityTheory BigOperators NNReal
set_option maxHeartbeats 1200000

namespace Part2.CNDProbability.SGModel
section MGF
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}
variable (h : SGModel ℱ μ θ R M D σ σe)

lemma probability_bound (n : ℕ) (i : ι) (ω : Ω) : |h.p n i ω| ≤ 1 := by
  rw [abs_of_nonneg (h.p_nonneg n ω i)]
  have hi : h.p n i ω ≤ ∑ j, h.p n j ω :=
    Finset.single_le_sum (fun j _ => h.p_nonneg n ω j) (Finset.mem_univ i)
  simpa only [h.p_sum n ω] using hi

/-- Fixed-parameter coordinate noise laws yield the bounded predictable
random-parameter law; this calls the separately proved simple/DCT theorem. -/
theorem scaled_noise_conditional_mgf (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1)
    (ν : ℝ≥0) (hν : (ν : ℝ) ^ 2 = σ ^ 2 + σe ^ 2) (n : ℕ) (i : ι) (t : ℝ) :
    μ[fun ω => Real.exp (t * Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω) | h.pre n] ≤ᵐ[μ]
      fun ω => Real.exp ((ν : ℝ) ^ 2 * t ^ 2 * Directional.scoreAt h.toM1Model.statistics b n i ω ^ 2 / 2) := by
  have hmgf : ∀ s : ℝ, μ[fun ω => Real.exp (s * h.combinedNoise n i ω) | h.pre n] ≤ᵐ[μ]
      fun _ => Real.exp ((ν : ℝ) ^ 2 * s ^ 2 / 2) := by
    intro s
    rw [hν]
    exact h.combined_conditional_mgf n i s
  have hbound : ∀ᵐ ω ∂μ, |t * Directional.scoreAt h.toM1Model.statistics b n i ω| ≤ |t| :=
    Eventually.of_forall fun ω => by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Directional.scoreAt_bound h.toM1Model.statistics b hb n i ω) (abs_nonneg t)
  have hr := SGRandom.conditional_mgf_bounded_coefficient (m₀ := m₀) (G := h.pre n) (μ := μ)
    (X := h.combinedNoise n i) (Λ := fun ω => t * Directional.scoreAt h.toM1Model.statistics b n i ω)
    (v := (ν : ℝ)) (L := |t|) (h.toM1Model.toSamplingModel.pre_le n)
    ((h.combined_measurable n i).mono ((h.encoded_le_next n).trans (ℱ.le (n + 1))) le_rfl)
    (h.combined_exp_integrable n i) hmgf
    (((Directional.scoreAt_measurable h.toM1Model.statistics b n i).stronglyMeasurable.mono (h.past_le_pre n)).const_mul t)
    (abs_nonneg t) hbound
  simpa only [mul_pow, mul_assoc] using hr

lemma weighted_full_integrable (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1) (n : ℕ) (i : ι) (t : ℝ) :
    Integrable (fun ω => h.p n i ω * Real.exp (t *
      (h.signalAt b n i ω + Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω))) μ :=
  (h.full_exponent_integrable b hb n i t).bdd_mul'
    ((h.p_measurable n i).mono (ℱ.le n) le_rfl).stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using h.probability_bound n i ω)

lemma weighted_full_conditional_bound (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1)
    (ν : ℝ≥0) (hν : (ν : ℝ) ^ 2 = σ ^ 2 + σe ^ 2) (n : ℕ) (i : ι) (t : ℝ) :
    μ[fun ω => h.p n i ω * Real.exp (t *
      (h.signalAt b n i ω + Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω)) | h.pre n] ≤ᵐ[μ]
      fun ω => h.p n i ω * Real.exp (t * h.signalAt b n i ω +
        (ν : ℝ) ^ 2 * t ^ 2 * Directional.scoreAt h.toM1Model.statistics b n i ω ^ 2 / 2) := by
  let P : Ω → ℝ := fun ω => h.p n i ω * Real.exp (t * h.signalAt b n i ω)
  let N : Ω → ℝ := fun ω => Real.exp (t * Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω)
  have hPm : StronglyMeasurable[h.pre n] P :=
    ((h.p_measurable n i).stronglyMeasurable.mono (h.past_le_pre n)).mul
      (Real.continuous_exp.comp_stronglyMeasurable ((h.signalAt_measurable b n i).stronglyMeasurable.const_mul t))
  have heq : (fun ω => P ω * N ω) = (fun ω => h.p n i ω * Real.exp (t *
      (h.signalAt b n i ω + Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω))) := by
    funext ω
    dsimp [P, N]
    rw [mul_add, Real.exp_add]
    ring
  have hNi : Integrable N μ := h.noise_exponent_integrable b hb n i t
  have hPNi : Integrable (fun ω => P ω * N ω) μ := by
    rw [heq]
    exact h.weighted_full_integrable b hb n i t
  have hpull := condExp_mul_of_stronglyMeasurable_left hPm hPNi hNi
  filter_upwards [hpull, h.scaled_noise_conditional_mgf b hb ν hν n i t] with ω hp hs
  rw [← heq]
  calc
    _ = P ω * (μ[N | h.pre n]) ω := hp
    _ ≤ P ω * Real.exp ((ν : ℝ) ^ 2 * t ^ 2 * Directional.scoreAt h.toM1Model.statistics b n i ω ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (h.p_nonneg n ω i) (Real.exp_nonneg _))
    _ = _ := by dsimp [P]; rw [Real.exp_add]; ring

/-- SG10 on the original G sigma-field, derived from raw noise/encoder
coordinate MGFs, strong action kernel, random-parameter extension, and actual
CND finite-action algebra. No action-fiber disintegration is assumed. -/
theorem direction_conditional_mgf_pre (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1)
    (ν : ℝ≥0) (hν : (ν : ℝ) ^ 2 = σ ^ 2 + σe ^ 2)
    (hH : 0 < R + M + (ν : ℝ)) (n : ℕ) {t : ℝ}
    (ht : |t| ≤ 1 / (8 * (R + M + (ν : ℝ)))) :
    μ[fun ω => Real.exp (t * h.directionIncrement b n ω) | h.pre n] ≤ᵐ[μ]
      fun ω => Real.exp (2 * (R + M + (ν : ℝ)) ^ 2 * t ^ 2 * Directional.information h.toM1Model.statistics b n ω) := by
  let f : ι → Ω → ℝ := fun i ω => Real.exp (t *
    (h.signalAt b n i ω + Directional.scoreAt h.toM1Model.statistics b n i ω * h.combinedNoise n i ω))
  have hs := h.toM1Model.encoded_selected_expectation n f
    (fun i => (h.full_exponent_measurable b n i t).stronglyMeasurable)
    (fun i => h.full_exponent_integrable b hb n i t)
  have htower := condExp_condExp_of_le (μ := μ) (f := fun ω => Real.exp (t * h.directionIncrement b n ω))
    (h.pre_le_encoded n) ((h.encoded_le_next n).trans (ℱ.le (n + 1)))
  have hcongr := condExp_congr_ae (m := h.pre n) hs
  have hsum := condExp_finset_sum (s := Finset.univ) (m := h.pre n)
    (fun i _ => h.weighted_full_integrable b hb n i t)
  filter_upwards [htower, hcongr, hsum,
    ae_all_iff.mpr (fun i => h.weighted_full_conditional_bound b hb ν hν n i t)] with ω htw hc hsum hterm
  change (μ[fun ω => Real.exp (t * h.directionIncrement b n ω) | h.pre n]) ω ≤ _
  calc
    _ = (μ[μ[fun ω => Real.exp (t * h.directionIncrement b n ω) | h.encoded n] | h.pre n]) ω := htw.symm
    _ = (μ[fun ω => ∑ i, h.p n i ω * f i ω | h.pre n]) ω := hc
    _ = ∑ i, (μ[fun ω => h.p n i ω * f i ω | h.pre n]) ω := by
      simpa only [Finset.sum_fn, Finset.sum_apply, f] using hsum
    _ ≤ ∑ i, h.p n i ω * Real.exp (t * h.signalAt b n i ω +
        (ν : ℝ) ^ 2 * t ^ 2 * Directional.scoreAt h.toM1Model.statistics b n i ω ^ 2 / 2) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ ≤ _ := SGDirectionFiber.finite_exponential_mix (fun i => h.p n i ω) b θ (h.drift n ω) R M
      (h.p_nonneg n ω) (h.p_sum n ω) hb h.R_nonneg h.M_nonneg h.theta_range (h.drift_range n ω) ν hH ht

end MGF
end Part2.CNDProbability.SGModel
