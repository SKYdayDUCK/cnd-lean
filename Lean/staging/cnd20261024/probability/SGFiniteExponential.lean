import staging.cnd20261024.probability.SGDirectionFiber

open MeasureTheory Filter ProbabilityTheory Finset Real
open scoped ProbabilityTheory BigOperators NNReal
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SGDirectionFiber
variable {ι : Type*} [Fintype ι]

/-- The deterministic finite mixture needed after original-space conditional
integration of the noise. It retains the actual CND signal and score. -/
theorem finite_exponential_mix (p b θ : ι → ℝ) (z R M : ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp : ∑ a, p a = 1)
    (hb : ∀ i j, |b i - b j| ≤ 1) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hθ : ∀ a, 0 ≤ θ a ∧ θ a ≤ R) (hz : 0 ≤ z ∧ z ≤ M)
    (ν : ℝ≥0) (hH : 0 < R + M + (ν : ℝ)) {t : ℝ}
    (ht : |t| ≤ 1 / (8 * (R + M + (ν : ℝ)))) :
    (∑ a, p a * exp (t * signal p b θ z a + (ν : ℝ) ^ 2 * t ^ 2 * directionScore p b a ^ 2 / 2)) ≤
      exp (2 * (R + M + (ν : ℝ)) ^ 2 * t ^ 2 * directionVariance p b) := by
  let B := signal p b θ z
  let X := directionScore p b
  let v := directionVariance p b
  have hv : 0 ≤ v := directionVariance_nonneg p b hp0
  have hH0 : 0 ≤ R + M := add_nonneg hR hM
  have hBbound := signal_bound p b θ z R M hp0 hp hb hθ hz
  have htmul : |t| * (8 * (R + M + (ν : ℝ))) ≤ 1 := (le_div_iff₀ (by positivity)).mp ht
  have hBsmall (a : ι) : |2 * t * B a| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hm := mul_le_mul_of_nonneg_left (hBbound a) (by positivity : 0 ≤ 2 * |t|)
    have hn := mul_nonneg (abs_nonneg t) ν.coe_nonneg
    nlinarith
  have hνt0 : 0 ≤ (ν : ℝ) * |t| := mul_nonneg ν.coe_nonneg (abs_nonneg t)
  have hνt : (ν : ℝ) * |t| ≤ 1 := by
    nlinarith [mul_nonneg hH0 (abs_nonneg t)]
  have hνsmall : (ν : ℝ) ^ 2 * t ^ 2 ≤ 1 := by
    have hq := mul_le_mul hνt hνt hνt0 zero_le_one
    simpa only [← pow_two, mul_pow, sq_abs, one_pow] using hq
  have hX (a : ι) : X a ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 (directionScore_bound p b hp0 hp hb a)
  have hA := Part2.SubGaussian.finite_centered_exp_bound p B hp0 hp
    (signal_mean p b θ z hp) (signal_second p b θ z R M hp0 hp hθ hz) hBsmall
  have hC := Part2.SubGaussian.finite_score_exp_bound p X hp0 hp hX (show ∑ a, p a * X a ^ 2 = v from rfl)
    (mul_nonneg (sq_nonneg (ν : ℝ)) (sq_nonneg t)) hνsmall
  have hCS := Part2.SubGaussian.finite_exp_cauchy p B X hp0 t (ν : ℝ)
  have hC' : (∑ a, p a * exp ((ν : ℝ) ^ 2 * t ^ 2 * X a ^ 2)) ≤ exp (2 * ((ν : ℝ) ^ 2 * t ^ 2) * v) := hC
  have hprod := mul_le_mul hA hC' (Finset.sum_nonneg fun a _ => mul_nonneg (hp0 a) (exp_nonneg _)) (exp_nonneg _)
  have hcoeff : 4 * (R + M) ^ 2 + 2 * (ν : ℝ) ^ 2 ≤ 4 * (R + M + (ν : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg hH0 ν.coe_nonneg, sq_nonneg (ν : ℝ)]
  have hexp : exp (4 * t ^ 2 * (R + M) ^ 2 * v) * exp (2 * ((ν : ℝ) ^ 2 * t ^ 2) * v) ≤
      exp (4 * (R + M + (ν : ℝ)) ^ 2 * t ^ 2 * v) := by
    rw [← exp_add, exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (sq_nonneg t) hv)]
  have hsq := hCS.trans (hprod.trans hexp)
  have hsq' : (∑ a, p a * exp (t * B a + (ν : ℝ) ^ 2 * t ^ 2 * X a ^ 2 / 2)) ^ 2 ≤
      (exp (2 * (R + M + (ν : ℝ)) ^ 2 * t ^ 2 * v)) ^ 2 := by
    rw [Part2.SubGaussian.exp_square]
    convert hsq using 1 <;> congr 1 <;> ring
  nlinarith [exp_pos (2 * (R + M + (ν : ℝ)) ^ 2 * t ^ 2 * v)]

end Part2.CNDProbability.SGDirectionFiber
