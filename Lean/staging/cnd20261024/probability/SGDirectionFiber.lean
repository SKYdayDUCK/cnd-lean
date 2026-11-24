import staging.cnd20261024.probability.DirectionalStatistics
import staging.cnd20261024.probability.SGConditional

open MeasureTheory Filter ProbabilityTheory Finset
open scoped ProbabilityTheory BigOperators NNReal
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SGDirectionFiber

section Signal
variable {ι : Type*} [Fintype ι]

lemma centered_second (p W : ι → ℝ) (m : ℝ) (hp : ∑ a, p a = 1)
    (hmean : ∑ a, p a * W a = m) :
    (∑ a, p a * (W a - m) ^ 2) = (∑ a, p a * W a ^ 2) - m ^ 2 := by
  have hterm (a : ι) : p a * (W a - m) ^ 2 = p a * W a ^ 2 - 2 * m * (p a * W a) + m ^ 2 * p a := by ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hp, hmean]
  ring

def signal (p b θ : ι → ℝ) (z : ℝ) (a : ι) : ℝ :=
  directionScore p b a * (θ a + z) - directionMean p b θ

lemma signal_mean (p b θ : ι → ℝ) (z : ℝ) (hp : ∑ a, p a = 1) :
    (∑ a, p a * signal p b θ z a) = 0 := by
  simp only [signal, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hp, one_mul, mul_assoc]
  rw [show (∑ a, p a * (directionScore p b a * (θ a + z))) = directionMean p b θ by
    simpa only [mul_assoc] using directionScore_signal p b θ z hp]
  ring

lemma signal_bound (p b θ : ι → ℝ) (z R M : ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp : ∑ a, p a = 1) (hb : ∀ i j, |b i - b j| ≤ 1)
    (hθ : ∀ a, 0 ≤ θ a ∧ θ a ≤ R) (hz : 0 ≤ z ∧ z ≤ M) (a : ι) :
    |signal p b θ z a| ≤ 2 * (R + M) := by
  have hR : 0 ≤ R := (hθ a).1.trans (hθ a).2
  have hM : 0 ≤ M := hz.1.trans hz.2
  have hW : |directionScore p b a * (θ a + z)| ≤ R + M := by
    rw [abs_mul, abs_of_nonneg (add_nonneg (hθ a).1 hz.1)]
    exact (mul_le_mul_of_nonneg_right (directionScore_bound p b hp0 hp hb a)
      (add_nonneg (hθ a).1 hz.1)).trans (by linarith [(hθ a).2, hz.2])
  exact (abs_sub _ _).trans (by linarith [directionMean_bound p b θ hp0 hp hb hθ])

lemma signal_second (p b θ : ι → ℝ) (z R M : ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp : ∑ a, p a = 1) (hθ : ∀ a, 0 ≤ θ a ∧ θ a ≤ R) (hz : 0 ≤ z ∧ z ≤ M) :
    (∑ a, p a * signal p b θ z a ^ 2) ≤ (R + M) ^ 2 * directionVariance p b := by
  have heq := centered_second p (fun a => directionScore p b a * (θ a + z))
    (directionMean p b θ) hp (by simpa only [mul_assoc] using directionScore_signal p b θ z hp)
  change (∑ a, p a * signal p b θ z a ^ 2) = _ at heq
  rw [heq]
  calc
    _ ≤ ∑ a, p a * (directionScore p b a * (θ a + z)) ^ 2 := sub_le_self _ (sq_nonneg _)
    _ ≤ (R + M) ^ 2 * directionVariance p b := by
      rw [directionVariance, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      have hlow : 0 ≤ θ a + z := add_nonneg (hθ a).1 hz.1
      have hhi : θ a + z ≤ R + M := by linarith [(hθ a).2, hz.2]
      have hsq : (θ a + z) ^ 2 ≤ (R + M) ^ 2 := (sq_le_sq₀ hlow (hlow.trans hhi)).2 hhi
      have hmul := mul_le_mul_of_nonneg_left hsq (mul_nonneg (hp0 a) (sq_nonneg (directionScore p b a)))
      simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hmul

end Signal

section Fiber
variable {ι Ξ : Type*} [Fintype ι] [mΞ : MeasurableSpace Ξ]

/-- CND's actual signal moments instantiate the finite-action SG theorem;
the signal centering/variance are conclusions above, not model premises. -/
theorem finite_direction_sg2 (p b θ : ι → ℝ) (z R M : ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp : ∑ a, p a = 1)
    (hb : ∀ i j, |b i - b j| ≤ 1) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hθ : ∀ a, 0 ≤ θ a ∧ θ a ≤ R) (hz : 0 ≤ z ∧ z ≤ M)
    (μa : ι → Measure Ξ) [∀ a, IsProbabilityMeasure (μa a)]
    (η : ι → Ξ → ℝ) (ν : ℝ≥0)
    (hη : ∀ a, HasSubgaussianMGF (η a) (ν ^ 2) (μa a))
    (hH : 0 < R + M + (ν : ℝ)) {t : ℝ} (ht : |t| ≤ 1 / (8 * (R + M + (ν : ℝ)))) :
    (∑ a, p a * mgf (fun w => directionScore p b a * (θ a + z + η a w) - directionMean p b θ) (μa a) t) ≤
      Real.exp (2 * (R + M + (ν : ℝ)) ^ 2 * t ^ 2 * directionVariance p b) := by
  have hX (a : ι) : directionScore p b a ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 (directionScore_bound p b hp0 hp hb a)
  have hbase := Part2.SubGaussian.finite_action_sg2 p (signal p b θ z) (directionScore p b)
    hp0 hp μa η ν hη (add_nonneg hR hM) hH (directionVariance_nonneg p b hp0)
    (signal_mean p b θ z hp) (signal_second p b θ z R M hp0 hp hθ hz)
    (signal_bound p b θ z R M hp0 hp hb hθ hz) hX rfl ht
  have heq (a : ι) : (fun w => signal p b θ z a + directionScore p b a * η a w) =
      (fun w => directionScore p b a * (θ a + z + η a w) - directionMean p b θ) := by
    funext w
    unfold signal
    ring
  simpa only [heq] using hbase

/-- Physical-noise/encoder conditional towers provide the action-fiber noise
law without imposing unconditional independence. A connection from SG-M1 to
the chosen regular conditional action fibers remains a separate obligation. -/
theorem finite_direction_sequential (p b θ : ι → ℝ) (z R M : ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp : ∑ a, p a = 1)
    (hb : ∀ i j, |b i - b j| ≤ 1) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hθ : ∀ a, 0 ≤ θ a ∧ θ a ≤ R) (hz : 0 ≤ z ∧ z ≤ M)
    [StandardBorelSpace Ξ] (μa : ι → Measure Ξ) [∀ a, IsProbabilityMeasure (μa a)]
    (ξ e : ι → Ξ → ℝ) (Hinfo : ι → MeasurableSpace Ξ) (hHinfo : ∀ a, Hinfo a ≤ mΞ)
    (σ2 σe2 ν : ℝ≥0) (hν : ν ^ 2 = σ2 + σe2)
    (hξm : ∀ a, Measurable[Hinfo a] (ξ a))
    (hξ : ∀ a, HasSubgaussianMGF (ξ a) σ2 (μa a))
    (he : ∀ a, HasCondSubgaussianMGF (Hinfo a) (hHinfo a) (e a) σe2 (μa a))
    (hH : 0 < R + M + (ν : ℝ)) {t : ℝ} (ht : |t| ≤ 1 / (8 * (R + M + (ν : ℝ)))) :
    (∑ a, p a * mgf (fun w => directionScore p b a * (θ a + z + (ξ a w - e a w)) - directionMean p b θ) (μa a) t) ≤
      Real.exp (2 * (R + M + (ν : ℝ)) ^ 2 * t ^ 2 * directionVariance p b) := by
  apply finite_direction_sg2 p b θ z R M hp0 hp hb hR hM hθ hz μa (fun a w => ξ a w - e a w) ν ?_ hH ht
  intro a
  rw [hν]
  exact SGConditional.encoded_noise_subGaussian_sequential (hHinfo a) (hξm a) (hξ a) (he a)

end Fiber
end Part2.CNDProbability.SGDirectionFiber
