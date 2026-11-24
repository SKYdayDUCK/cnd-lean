import staging.cnd20261024.probability.SGOriginalMGF
import staging.cnd20261024.probability.SGRestrictedTail

open MeasureTheory Filter ProbabilityTheory Finset
open scoped ProbabilityTheory BigOperators NNReal
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SGModel
section Past
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}
variable (h : SGModel ℱ μ θ R M D σ σe)

/-- SG10 descends to the actual past filtration. The upper compensator is
past-measurable and bounded because q≤1, even though observations are unbounded. -/
theorem direction_conditional_mgf_past (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1)
    (ν : ℝ≥0) (hν : (ν : ℝ) ^ 2 = σ ^ 2 + σe ^ 2)
    (hH : 0 < R + M + (ν : ℝ)) (n : ℕ) {t : ℝ}
    (ht : |t| ≤ 1 / (8 * (R + M + (ν : ℝ)))) :
    μ[fun ω => Real.exp (t * h.directionIncrement b n ω) | ℱ n] ≤ᵐ[μ]
      fun ω => Real.exp (2 * (R + M + (ν : ℝ)) ^ 2 * t ^ 2 * Directional.information h.toM1Model.statistics b n ω) := by
  let C : ℝ := 2 * (R + M + (ν : ℝ)) ^ 2 * t ^ 2
  let V : Ω → ℝ := fun ω => Real.exp (C * Directional.information h.toM1Model.statistics b n ω)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hVm : StronglyMeasurable[ℱ n] V := Real.continuous_exp.comp_stronglyMeasurable
    ((Directional.information_measurable h.toM1Model.statistics b n).stronglyMeasurable.const_mul C)
  have hVi : Integrable V μ := by
    apply (integrable_const (Real.exp C)).mono' ((hVm.mono (ℱ.le n)).aestronglyMeasurable)
    apply Eventually.of_forall
    intro ω
    change ‖Real.exp (C * Directional.information h.toM1Model.statistics b n ω)‖ ≤ Real.exp C
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Directional.information_bounds h.toM1Model.statistics b hb n ω).2 hC
  have hmono := condExp_mono (m := ℱ n)
    (f := μ[fun ω => Real.exp (t * h.directionIncrement b n ω) | h.pre n]) (g := V) integrable_condExp hVi
    (h.direction_conditional_mgf_pre b hb ν hν hH n ht)
  have htower := condExp_condExp_of_le (μ := μ)
    (f := fun ω => Real.exp (t * h.directionIncrement b n ω)) (h.past_le_pre n) (h.toM1Model.toSamplingModel.pre_le n)
  have hfix := condExp_of_stronglyMeasurable (ℱ.le n) hVm hVi
  filter_upwards [hmono, htower] with ω hm htw
  calc
    _ = (μ[μ[fun ω => Real.exp (t * h.directionIncrement b n ω) | h.pre n] | ℱ n]) ω := htw.symm
    _ ≤ (μ[V | ℱ n]) ω := hm
    _ = V ω := congrFun hfix ω

/-- A genuine nonnegative CND SG exponential supermartingale on the original
filtration. Its conditional MGF is a proved result, not a model field. -/
theorem direction_supermartingale (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1)
    (ν : ℝ≥0) (hν : (ν : ℝ) ^ 2 = σ ^ 2 + σe ^ 2) (hH : 0 < R + M + (ν : ℝ))
    {t : ℝ} (ht : |t| ≤ 1 / (8 * (R + M + (ν : ℝ)))) :
    Supermartingale (SGRestricted.process (h.directionIncrement b)
      (Directional.information h.toM1Model.statistics b) (2 * (R + M + (ν : ℝ)) ^ 2) t) ℱ μ := by
  apply SGRestricted.supermartingale_of_conditional_mgf (by positivity)
    (fun n => (h.direction_measurable b n).stronglyMeasurable)
    (fun n => (Directional.information_measurable h.toM1Model.statistics b n).stronglyMeasurable)
    (fun n ω => (Directional.information_bounds h.toM1Model.statistics b hb n ω).1)
    (h.direction_exp_integrable b hb)
  intro n
  exact h.direction_conditional_mgf_past b hb ν hν hH n ht

theorem direction_maximal (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1)
    (ν : ℝ≥0) (hν : (ν : ℝ) ^ 2 = σ ^ 2 + σe ^ 2) (hH : 0 < R + M + (ν : ℝ))
    (N : ℕ) {v L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ N,
      2 * Real.sqrt ((2 * (R + M + (ν : ℝ)) ^ 2) * v * L) + L / (1 / (8 * (R + M + (ν : ℝ)))) ≤
        Bernstein.sumProcess (h.directionIncrement b) n ω ∧
      Bernstein.sumProcess (Directional.information h.toM1Model.statistics b) n ω ≤ v} ≤ Real.exp (-L) := by
  apply SGRestricted.maximal_of_conditional_mgf (by positivity) (by positivity)
    (fun n => (h.direction_measurable b n).stronglyMeasurable)
    (fun n => (Directional.information_measurable h.toM1Model.statistics b n).stronglyMeasurable)
    (fun n ω => (Directional.information_bounds h.toM1Model.statistics b hb n ω).1)
    (h.direction_exp_integrable b hb) ?_ N hv hL
  intro t ht0 htcap n
  exact h.direction_conditional_mgf_past b hb ν hν hH n (by simpa only [abs_of_nonneg ht0] using htcap)

end Past
end Part2.CNDProbability.SGModel
