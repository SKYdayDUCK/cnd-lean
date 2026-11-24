import staging.cnd20261024.probability.SGOriginalPast
import staging.cnd20261024.probability.SGRestrictedUniform
import staging.cnd20261024.probability.SGCoordinateBridge

open MeasureTheory Filter ProbabilityTheory Finset
open scoped ProbabilityTheory BigOperators NNReal
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SGModel
section Uniform
variable {Ω ι α : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype α]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}
variable (h : SGModel ℱ μ θ R M D σ σe)

theorem direction_uniform (b : ι → ℝ) (hb : ∀ i j, |b i - b j| ≤ 1)
    (ν : ℝ≥0) (hν : (ν : ℝ) ^ 2 = σ ^ 2 + σe ^ 2) (hH : 0 < R + M + (ν : ℝ))
    (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ T,
      2 * Real.sqrt ((2 * (R + M + (ν : ℝ)) ^ 2) *
        (1 + Bernstein.sumProcess (Directional.information h.toM1Model.statistics b) n ω) * L) +
        L / (1 / (8 * (R + M + (ν : ℝ)))) ≤ |Bernstein.sumProcess (h.directionIncrement b) n ω|} ≤
      2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-L) := by
  apply SGRestricted.uniform_of_conditional_mgf (by positivity) (by positivity)
    (fun n => (h.direction_measurable b n).stronglyMeasurable)
    (fun n => (Directional.information_measurable h.toM1Model.statistics b n).stronglyMeasurable)
    (Directional.information_bounds h.toM1Model.statistics b hb) (h.direction_exp_integrable b hb) ?_ T hL
  intro t ht n
  exact h.direction_conditional_mgf_past b hb ν hν hH n ht

/-- All times and finite deterministic directions for the actual original
SG process. No independence is required across arms, times, or directions. -/
theorem finite_direction_family (b : α → ι → ℝ) (hb : ∀ a i j, |b a i - b a j| ≤ 1)
    (ν : ℝ≥0) (hν : (ν : ℝ) ^ 2 = σ ^ 2 + σe ^ 2) (hH : 0 < R + M + (ν : ℝ))
    (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ a, ∃ n ≤ T,
      2 * Real.sqrt ((2 * (R + M + (ν : ℝ)) ^ 2) *
        (1 + Bernstein.sumProcess (Directional.information h.toM1Model.statistics (b a)) n ω) * L) +
        L / (1 / (8 * (R + M + (ν : ℝ)))) ≤ |Bernstein.sumProcess (h.directionIncrement (b a)) n ω|} ≤
      (Fintype.card α : ℝ) * (2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-L)) := by
  have hset : {ω | ∃ a, ∃ n ≤ T,
      2 * Real.sqrt ((2 * (R + M + (ν : ℝ)) ^ 2) *
        (1 + Bernstein.sumProcess (Directional.information h.toM1Model.statistics (b a)) n ω) * L) +
        L / (1 / (8 * (R + M + (ν : ℝ)))) ≤ |Bernstein.sumProcess (h.directionIncrement (b a)) n ω|} =
      ⋃ a, {ω | ∃ n ≤ T,
        2 * Real.sqrt ((2 * (R + M + (ν : ℝ)) ^ 2) *
          (1 + Bernstein.sumProcess (Directional.information h.toM1Model.statistics (b a)) n ω) * L) +
          L / (1 / (8 * (R + M + (ν : ℝ)))) ≤ |Bernstein.sumProcess (h.directionIncrement (b a)) n ω|} := by ext ω; simp
  rw [hset]
  calc
    _ ≤ ∑ a, μ.real {ω | ∃ n ≤ T,
        2 * Real.sqrt ((2 * (R + M + (ν : ℝ)) ^ 2) *
          (1 + Bernstein.sumProcess (Directional.information h.toM1Model.statistics (b a)) n ω) * L) +
          L / (1 / (8 * (R + M + (ν : ℝ)))) ≤ |Bernstein.sumProcess (h.directionIncrement (b a)) n ω|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : α, (2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-L)) :=
      Finset.sum_le_sum fun a _ => h.direction_uniform (b a) (hb a) ν hν hH T hL
    _ = _ := by simp

end Uniform

/-- Exact deterministic bridge from peeled SG variance to the paper's net
bound 4Hs sqrt(L)*energy+8Hs L. -/
lemma sg_radius_le_energy {H q L E : ℝ} (hH : 0 < H) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hq0 : 0 ≤ q) (hqE : 1 + q ≤ 2 * E ^ 2) :
    2 * Real.sqrt ((2 * H ^ 2) * (1 + q) * L) + L / (1 / (8 * H)) ≤
      4 * H * Real.sqrt L * E + 8 * H * L := by
  have harg : 0 ≤ (2 * H ^ 2) * (1 + q) * L := by positivity
  have hs : Real.sqrt ((2 * H ^ 2) * (1 + q) * L) ^ 2 = (2 * H ^ 2) * (1 + q) * L := Real.sq_sqrt harg
  have hsq : (2 * H * Real.sqrt L * E) ^ 2 = 4 * H ^ 2 * L * E ^ 2 := by rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hL]; ring
  have hmul := mul_le_mul_of_nonneg_right hqE (by positivity : 0 ≤ 2 * H ^ 2 * L)
  have hB0 : 0 ≤ 2 * H * Real.sqrt L * E := by positivity
  have hroot : Real.sqrt ((2 * H ^ 2) * (1 + q) * L) ≤ 2 * H * Real.sqrt L * E := by
    nlinarith [Real.sqrt_nonneg ((2 * H ^ 2) * (1 + q) * L), hB0]
  have hinv : L / (1 / (8 * H)) = 8 * H * L := by simp only [one_div, div_inv_eq_mul]; ring
  rw [hinv]
  nlinarith

end Part2.CNDProbability.SGModel
