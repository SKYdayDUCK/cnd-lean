import staging.cnd20261024.probability.SGOriginalPast
import staging.cnd20261024.payment.IntervalNoiseTails

noncomputable section
open MeasureTheory Filter ProbabilityTheory Finset
open scoped ProbabilityTheory BigOperators NNReal
set_option maxHeartbeats 1600000
namespace Part2.CNDSGMain
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}
variable (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)

def noiseDifference (k : ι) (n : ℕ) (ω : Ω) : ℝ :=
  h.combinedNoise n (h.action n ω) ω - h.combinedNoise n k ω

theorem pair_exp_integrable (n : ℕ) (i k : ι) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * (h.combinedNoise n i ω - h.combinedNoise n k ω))) μ := by
  have hi := CNDProbability.SGRestricted.integrable_exp_add (μ := μ)
    (h.combined_exp_integrable n i)
    (Y := fun ω => -h.combinedNoise n k ω)
    (fun s => by simpa only [mul_neg, neg_mul] using h.combined_exp_integrable n k (-s)) t
  simpa only [sub_eq_add_neg] using hi

/-- Equal-variance conditional Cauchy--Schwarz via the elementary square inequality.
No coordinate independence is used. -/
theorem pair_conditional_mgf (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    (n : ℕ) (i k : ι) (t : ℝ) :
    μ[fun ω => Real.exp (t * (h.combinedNoise n i ω - h.combinedNoise n k ω)) | h.pre n] ≤ᵐ[μ]
      fun _ => Real.exp ((2 * (ν : ℝ))^2 * t^2 / 2) := by
  let F : Ω → ℝ := fun ω => Real.exp ((2*t) * h.combinedNoise n i ω)
  let G : Ω → ℝ := fun ω => Real.exp ((-2*t) * h.combinedNoise n k ω)
  have hFi : Integrable F μ := h.combined_exp_integrable n i (2*t)
  have hGi : Integrable G μ := h.combined_exp_integrable n k (-2*t)
  have hpoint : (fun ω => Real.exp (t * (h.combinedNoise n i ω - h.combinedNoise n k ω))) ≤ᵐ[μ]
      fun ω => (F ω + G ω) / 2 := by
    apply Eventually.of_forall
    intro ω
    have hi : Real.exp (t * h.combinedNoise n i ω)^2 = F ω := by
      dsimp [F]; rw [pow_two, ← Real.exp_add]; congr 1; ring
    have hk : Real.exp (-t * h.combinedNoise n k ω)^2 = G ω := by
      dsimp [G]; rw [pow_two, ← Real.exp_add]; congr 1; ring
    change Real.exp (t * (h.combinedNoise n i ω - h.combinedNoise n k ω)) ≤ (F ω + G ω)/2
    rw [mul_sub, Real.exp_sub]
    have he : Real.exp (t * h.combinedNoise n i ω) / Real.exp (t * h.combinedNoise n k ω) =
        Real.exp (t * h.combinedNoise n i ω) * Real.exp (-t * h.combinedNoise n k ω) := by
      rw [neg_mul, Real.exp_neg, div_eq_mul_inv]
    rw [he]
    nlinarith [sq_nonneg (Real.exp (t * h.combinedNoise n i ω) - Real.exp (-t * h.combinedNoise n k ω))]
  have hmono := condExp_mono (m := h.pre n) (pair_exp_integrable h n i k t)
    ((hFi.add hGi).div_const 2) hpoint
  have hlinear := condExp_add hFi hGi (h.pre n)
  have hscale := condExp_smul (μ := μ) (m := h.pre n) (f := F + G) (1/2 : ℝ)
  have hi := h.combined_conditional_mgf n i (2*t)
  have hk := h.combined_conditional_mgf n k (-2*t)
  have he1 : (σ^2+σe^2)*(2*t)^2/2 = (2*(ν:ℝ))^2*t^2/2 := by rw [← hν]; ring
  have he2 : (σ^2+σe^2)*(-2*t)^2/2 = (2*(ν:ℝ))^2*t^2/2 := by rw [← hν]; ring
  rw [he1] at hi
  rw [he2] at hk
  filter_upwards [hmono, hlinear, hscale, hi, hk] with ω hm hl hs hi hk
  have heq : (fun ω => (F+G) ω/2) = (1/2 : ℝ) • (F+G) := by funext ω; simp; ring
  rw [heq] at hm
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at hs hl
  rw [hs, hl] at hm
  linarith

theorem noiseDifference_measurable (k : ι) (n : ℕ) :
    Measurable[ℱ (n+1)] (noiseDifference h k n) :=
  PairConfidence.selected_measurable
    ((h.action_measurable n).mono (h.action_le_next n) le_rfl)
    (fun i => ((h.combined_measurable n i).sub (h.combined_measurable n k)).mono (h.encoded_le_next n) le_rfl)

theorem noiseDifference_exp_integrable (k : ι) (n : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * noiseDifference h k n ω)) μ :=
  PairConfidence.selected_integrable
    ((h.action_measurable n).mono (h.toM1Model.toSamplingModel.action_le n) le_rfl)
    (fun i => pair_exp_integrable h n i k t)

theorem weighted_pair_integrable (n : ℕ) (i k : ι) (t : ℝ) :
    Integrable (fun ω => h.p n i ω * Real.exp (t * (h.combinedNoise n i ω - h.combinedNoise n k ω))) μ :=
  (pair_exp_integrable h n i k t).bdd_mul'
    ((h.p_measurable n i).mono (ℱ.le n) le_rfl).stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using h.probability_bound n i ω)

theorem weighted_pair_conditional_mgf (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    (n : ℕ) (i k : ι) (t : ℝ) :
    μ[fun ω => h.p n i ω * Real.exp (t * (h.combinedNoise n i ω - h.combinedNoise n k ω)) | h.pre n] ≤ᵐ[μ]
      fun ω => h.p n i ω * Real.exp ((2*(ν:ℝ))^2*t^2/2) := by
  have hpull := condExp_mul_of_stronglyMeasurable_left
    ((h.p_measurable n i).stronglyMeasurable.mono (h.past_le_pre n))
    (weighted_pair_integrable h n i k t) (pair_exp_integrable h n i k t)
  filter_upwards [hpull, pair_conditional_mgf h ν hν n i k t] with ω hp hc
  exact hp.le.trans (mul_le_mul_of_nonneg_left hc (h.p_nonneg n ω i))

/-- The actual selected combined-noise difference is mixed using the original strong kernel. -/
theorem noiseDifference_conditional_mgf_pre (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    (k : ι) (n : ℕ) (t : ℝ) :
    μ[fun ω => Real.exp (t * noiseDifference h k n ω) | h.pre n] ≤ᵐ[μ]
      fun _ => Real.exp ((2*(ν:ℝ))^2*t^2/2) := by
  let f : ι → Ω → ℝ := fun i ω => Real.exp (t * (h.combinedNoise n i ω - h.combinedNoise n k ω))
  have hs := h.toM1Model.encoded_selected_expectation n f
    (fun i => (((h.combined_measurable n i).sub (h.combined_measurable n k)).const_mul t).exp.stronglyMeasurable)
    (fun i => pair_exp_integrable h n i k t)
  have htower := condExp_condExp_of_le (μ := μ) (f := fun ω => Real.exp (t * noiseDifference h k n ω))
    (h.pre_le_encoded n) ((h.encoded_le_next n).trans (ℱ.le (n+1)))
  have hc := condExp_congr_ae (m := h.pre n) hs
  have hsum := condExp_finset_sum (s := Finset.univ) (m := h.pre n)
    (fun i _ => weighted_pair_integrable h n i k t)
  filter_upwards [htower, hc, hsum,
    ae_all_iff.mpr (fun i => weighted_pair_conditional_mgf h ν hν n i k t)] with ω ht hc hh hb
  calc
    _ = (μ[μ[fun ω => Real.exp (t * noiseDifference h k n ω) | h.encoded n] | h.pre n]) ω := ht.symm
    _ = (μ[fun ω => ∑ i, h.p n i ω * f i ω | h.pre n]) ω := hc
    _ = ∑ i, (μ[fun ω => h.p n i ω * f i ω | h.pre n]) ω := by simpa only [Finset.sum_fn, Finset.sum_apply, f] using hh
    _ ≤ ∑ i, h.p n i ω * Real.exp ((2*(ν:ℝ))^2*t^2/2) := Finset.sum_le_sum fun i _ => hb i
    _ = _ := by rw [← Finset.sum_mul, h.p_sum n ω, one_mul]

theorem noiseDifference_conditional_mgf (ν : ℝ≥0) (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    (k : ι) (n : ℕ) (t : ℝ) :
    μ[fun ω => Real.exp (t * noiseDifference h k n ω) | ℱ n] ≤ᵐ[μ]
      fun _ => Real.exp ((2*(ν:ℝ))^2*t^2/2) := by
  have hm := condExp_mono (m := ℱ n) integrable_condExp (integrable_const _)
    (noiseDifference_conditional_mgf_pre h ν hν k n t)
  have ht := condExp_condExp_of_le (μ := μ) (f := fun ω => Real.exp (t * noiseDifference h k n ω))
    (h.past_le_pre n) (h.toM1Model.toSamplingModel.pre_le n)
  have hf := condExp_of_stronglyMeasurable (μ := μ) (ℱ.le n) stronglyMeasurable_const (integrable_const (Real.exp ((2*(ν:ℝ))^2*t^2/2)))
  filter_upwards [hm, ht] with ω hm ht
  rw [hf] at hm
  exact ht.symm.le.trans hm

end Part2.CNDSGMain
