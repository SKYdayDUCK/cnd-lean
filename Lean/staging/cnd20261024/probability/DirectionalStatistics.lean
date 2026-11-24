import Part2.PairConfidence
import staging.cnd20261024.probability.FiniteVille

set_option maxHeartbeats 800000

/-! CND's actual directional statistic `(b_A - p·b) Y`, on the original space.
This is distinct from the pair score in `Part2.PairConfidence`.
Only the elementary categorical/conditional-expectation lemmas are reused.
The strong action kernel is kept separate from the weaker sufficient laws
for the statistic, so the public-sampling condition is not lost. -/

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators

namespace Part2.CNDProbability

section FiniteAlgebra
variable {ι : Type*} [Fintype ι]

def weighted (p b : ι → ℝ) : ℝ := ∑ a, p a * b a
def directionScore (p b : ι → ℝ) (a : ι) : ℝ := b a - weighted p b
def directionVariance (p b : ι → ℝ) : ℝ := ∑ a, p a * (directionScore p b a) ^ 2
def directionMean (p b θ : ι → ℝ) : ℝ := ∑ a, p a * directionScore p b a * θ a

lemma directionScore_centered (p b : ι → ℝ) (hp : ∑ a, p a = 1) :
    (∑ a, p a * directionScore p b a) = 0 := by
  simp only [directionScore, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hp, one_mul, weighted]
  ring

lemma directionScore_signal (p b θ : ι → ℝ) (z : ℝ) (hp : ∑ a, p a = 1) :
    (∑ a, p a * directionScore p b a * (θ a + z)) = directionMean p b θ := by
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    directionScore_centered p b hp, zero_mul, add_zero, directionMean]

lemma directionScore_bound (p b : ι → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp : ∑ a, p a = 1) (hb : ∀ i j, |b i - b j| ≤ 1) (a : ι) :
    |directionScore p b a| ≤ 1 := by
  have heq : directionScore p b a = ∑ j, p j * (b a - b j) := by
    simp only [directionScore, weighted, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hp, one_mul]
  rw [heq]
  calc
    _ ≤ ∑ j, |p j * (b a - b j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, p j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hp0 j)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb a j) (hp0 j)
    _ = 1 := hp

lemma directionVariance_nonneg (p b : ι → ℝ) (hp0 : ∀ a, 0 ≤ p a) :
    0 ≤ directionVariance p b := Finset.sum_nonneg fun a _ => mul_nonneg (hp0 a) (sq_nonneg _)

lemma directionVariance_le_one (p b : ι → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp : ∑ a, p a = 1) (hb : ∀ i j, |b i - b j| ≤ 1) :
    directionVariance p b ≤ 1 := by
  calc
    _ ≤ ∑ a, p a := by
      apply Finset.sum_le_sum
      intro a _
      have hs := directionScore_bound p b hp0 hp hb a
      have hsq : directionScore p b a ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 hs
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (hp0 a)
    _ = 1 := hp

lemma directionMean_bound (p b θ : ι → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp : ∑ a, p a = 1) (hb : ∀ i j, |b i - b j| ≤ 1) {R : ℝ}
    (hθ : ∀ a, 0 ≤ θ a ∧ θ a ≤ R) : |directionMean p b θ| ≤ R := by
  calc
    _ ≤ ∑ a, |p a * directionScore p b a * θ a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, p a * R := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_mul, abs_of_nonneg (hp0 a), abs_of_nonneg (hθ a).1]
      have hs := mul_le_mul_of_nonneg_left (directionScore_bound p b hp0 hp hb a) (hp0 a)
      simp only [mul_one] at hs
      exact mul_le_mul hs (hθ a).2 (hθ a).1 (hp0 a)
    _ = R := by rw [← Finset.sum_mul, hp, one_mul]

/-- The scalar score variance equals the quadratic form of diag(p)-ppᵀ. -/
lemma directionVariance_covariance (p b : ι → ℝ) (hp : ∑ a, p a = 1) :
    directionVariance p b = (∑ a, p a * (b a) ^ 2) - (weighted p b) ^ 2 := by
  simp only [directionVariance, directionScore, sub_sq, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have heq : (∑ a, p a * (2 * b a * weighted p b)) = 2 * weighted p b * weighted p b := by
    calc
      _ = ∑ a, (p a * b a) * (2 * weighted p b) := by apply Finset.sum_congr rfl; intros; ring
      _ = _ := by rw [← Finset.sum_mul]; unfold weighted; ring
  rw [heq, ← Finset.sum_mul, hp, one_mul]
  ring

/-- The directional mean is bᵀ C(p) θ. -/
lemma directionMean_covariance (p b θ : ι → ℝ) :
    directionMean p b θ = (∑ a, p a * b a * θ a) - weighted p b * weighted p θ := by
  simp only [directionMean, directionScore, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  calc
    _ = ∑ a, weighted p b * (p a * θ a) := by apply Finset.sum_congr rfl; intros; ring
    _ = _ := by rw [← Finset.mul_sum]; rfl

end FiniteAlgebra

section Model
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}

/-- Strong M1 model. The base supplies chronological raw sampling/encoder
laws. `encoded` contains G and the full potential encoder output, and its
categorical law ensures revealing that output does not change action masses.
No confidence event, tail bound, or exponential moment is a model field. -/
structure M1Model (ℱ : Filtration ℕ m₀) (μ : Measure Ω) (θ : ι → ℝ) (R M D : ℝ)
    extends PairConfidence.SamplingModel ℱ μ θ R M D where
  encoded : ℕ → MeasurableSpace Ω
  pre_le_encoded : ∀ n, pre n ≤ encoded n
  encoded_le_next : ∀ n, encoded n ≤ ℱ (n + 1)
  error_encoded : ∀ n a, Measurable[encoded n] (error n a)
  strong_categorical : ∀ n a,
    μ[PairConfidence.actionIndicator (action n) a | encoded n] =ᵐ[μ] p n a

namespace M1Model
variable (h : M1Model ℱ μ θ R M D)

/-- The weaker action law needed by orthogonal statistics is a proved
projection of the strong M1 kernel, not a replacement of its full content. -/
theorem categorical_from_strong (n : ℕ) (a : ι) :
    μ[PairConfidence.actionIndicator (h.action n) a | h.pre n] =ᵐ[μ] h.p n a := by
  have hpi : Integrable (h.p n a) μ := PairConfidence.bounded_integrable
    ((h.p_measurable n a).mono (ℱ.le n) le_rfl) (fun ω => by
      rw [abs_of_nonneg (h.p_nonneg n ω a)]
      have hle : h.p n a ω ≤ ∑ j, h.p n j ω :=
        Finset.single_le_sum (fun j _ => h.p_nonneg n ω j) (Finset.mem_univ a)
      simpa only [h.p_sum n ω] using hle)
  exact PairConfidence.conditional_down (h.pre_le_encoded n)
    ((h.encoded_le_next n).trans (ℱ.le (n + 1))) (h.strong_categorical n a)
    ((h.p_measurable n a).stronglyMeasurable.mono (h.past_le_pre n)) hpi

end M1Model

namespace Directional
variable (h : PairConfidence.SamplingModel ℱ μ θ R M D) (b : ι → ℝ)

noncomputable def scoreAt (n : ℕ) (a : ι) (ω : Ω) : ℝ := directionScore (fun j => h.p n j ω) b a
noncomputable def score (n : ℕ) (ω : Ω) : ℝ := scoreAt h b n (h.action n ω) ω
noncomputable def information (n : ℕ) (ω : Ω) : ℝ := directionVariance (fun j => h.p n j ω) b
noncomputable def predictableMean (n : ℕ) (ω : Ω) : ℝ := directionMean (fun j => h.p n j ω) b θ
noncomputable def statistic (n : ℕ) (ω : Ω) : ℝ := score h b n ω * h.residual n ω
noncomputable def increment (n : ℕ) (ω : Ω) : ℝ := statistic h b n ω - predictableMean h b n ω
noncomputable def noiseStatistic (n : ℕ) (ω : Ω) : ℝ := score h b n ω * h.selectedError n ω
noncomputable def signalStatistic (n : ℕ) (ω : Ω) : ℝ := score h b n ω * (θ (h.action n ω) + h.drift n ω)

lemma scoreAt_measurable (n : ℕ) (a : ι) : Measurable[ℱ n] (scoreAt h b n a) :=
  measurable_const.sub (Finset.measurable_fun_sum _ fun j _ => (h.p_measurable n j).mul_const (b j))

lemma information_measurable (n : ℕ) : Measurable[ℱ n] (information h b n) :=
  Finset.measurable_fun_sum _ fun a _ => (h.p_measurable n a).mul ((scoreAt_measurable h b n a).pow_const 2)

lemma mean_measurable (n : ℕ) : Measurable[ℱ n] (predictableMean h b n) :=
  Finset.measurable_fun_sum _ fun a _ => ((h.p_measurable n a).mul (scoreAt_measurable h b n a)).mul_const (θ a)

lemma score_measurable (n : ℕ) : Measurable[h.afterAction n] (score h b n) :=
  PairConfidence.selected_measurable (h.action_measurable n) fun a =>
    (scoreAt_measurable h b n a).mono ((h.past_le_pre n).trans (h.pre_le_action n)) le_rfl

lemma statistic_measurable (n : ℕ) : Measurable[ℱ (n + 1)] (statistic h b n) :=
  ((score_measurable h b n).mono (h.action_le_next n) le_rfl).mul (h.residual_measurable n)

lemma increment_measurable (n : ℕ) : Measurable[ℱ (n + 1)] (increment h b n) :=
  (statistic_measurable h b n).sub ((mean_measurable h b n).mono (ℱ.mono (Nat.le_succ n)) le_rfl)

variable (hb : ∀ i j, |b i - b j| ≤ 1)
include hb

lemma scoreAt_bound (n : ℕ) (a : ι) (ω : Ω) : |scoreAt h b n a ω| ≤ 1 :=
  directionScore_bound _ _ (h.p_nonneg n ω) (h.p_sum n ω) hb a

lemma information_bounds (n : ℕ) (ω : Ω) : 0 ≤ information h b n ω ∧ information h b n ω ≤ 1 :=
  ⟨directionVariance_nonneg _ _ (h.p_nonneg n ω),
    directionVariance_le_one _ _ (h.p_nonneg n ω) (h.p_sum n ω) hb⟩

lemma mean_bound (n : ℕ) (ω : Ω) : |predictableMean h b n ω| ≤ R :=
  directionMean_bound _ _ _ (h.p_nonneg n ω) (h.p_sum n ω) hb h.theta_range

lemma statistic_bound (n : ℕ) (ω : Ω) : |statistic h b n ω| ≤ R + M + D := by
  rw [statistic, abs_mul]
  exact (mul_le_mul_of_nonneg_right (scoreAt_bound h b hb n (h.action n ω) ω) (abs_nonneg _)).trans
    (by simpa only [one_mul] using h.residual_bound n ω)

lemma increment_bound (n : ℕ) (ω : Ω) : |increment h b n ω| ≤ 2 * (R + M + D) := by
  exact (abs_sub _ _).trans (by
    have hs := statistic_bound h b hb n ω
    have hm := mean_bound h b hb n ω
    linarith [h.M_nonneg, h.D_nonneg])

lemma information_integrable (n : ℕ) : Integrable (information h b n) μ :=
  PairConfidence.bounded_integrable ((information_measurable h b n).mono (ℱ.le n) le_rfl)
    (fun ω => by simpa only [abs_of_nonneg (information_bounds h b hb n ω).1] using (information_bounds h b hb n ω).2)

lemma mean_integrable (n : ℕ) : Integrable (predictableMean h b n) μ :=
  PairConfidence.bounded_integrable ((mean_measurable h b n).mono (ℱ.le n) le_rfl) (mean_bound h b hb n)

lemma statistic_integrable (n : ℕ) : Integrable (statistic h b n) μ :=
  PairConfidence.bounded_integrable ((statistic_measurable h b n).mono (ℱ.le (n + 1)) le_rfl)
    (statistic_bound h b hb n)

theorem score_conditional_zero (n : ℕ) : μ[score h b n | ℱ n] =ᵐ[μ] fun _ => 0 := by
  have ht := PairConfidence.conditional_selected
    ((h.action_measurable n).mono (h.action_le n) le_rfl) (h.categorical n) (scoreAt h b n)
    (fun a => (scoreAt_measurable h b n a).stronglyMeasurable.mono (h.past_le_pre n))
    (fun a => PairConfidence.bounded_integrable ((scoreAt_measurable h b n a).mono (ℱ.le n) le_rfl)
      (scoreAt_bound h b hb n a))
  have hp : μ[score h b n | h.pre n] =ᵐ[μ] fun _ => 0 := by
    filter_upwards [ht] with ω ht
    exact ht.trans (directionScore_centered _ _ (h.p_sum n ω))
  exact PairConfidence.conditional_zero_down (h.past_le_pre n) (h.pre_le n) hp

theorem score_conditional_second (n : ℕ) :
    μ[fun ω => (score h b n ω) ^ 2 | ℱ n] =ᵐ[μ] information h b n := by
  let f : ι → Ω → ℝ := fun a ω => (scoreAt h b n a ω) ^ 2
  have hfm (a : ι) : Measurable[ℱ n] (f a) := (scoreAt_measurable h b n a).pow_const 2
  have hfb (a : ι) (ω : Ω) : |f a ω| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 (scoreAt_bound h b hb n a ω)
  have ht := PairConfidence.conditional_selected
    ((h.action_measurable n).mono (h.action_le n) le_rfl) (h.categorical n) f
    (fun a => (hfm a).stronglyMeasurable.mono (h.past_le_pre n))
    (fun a => PairConfidence.bounded_integrable ((hfm a).mono (ℱ.le n) le_rfl) (hfb a))
  have hp : μ[fun ω => (score h b n ω) ^ 2 | h.pre n] =ᵐ[μ] information h b n := ht
  exact PairConfidence.conditional_down (h.past_le_pre n) (h.pre_le n) hp
    (information_measurable h b n).stronglyMeasurable (information_integrable h b hb n)

lemma noiseStatistic_integrable (n : ℕ) : Integrable (noiseStatistic h b n) μ := by
  apply PairConfidence.bounded_integrable
    ((((score_measurable h b n).mono (h.action_le_next n) le_rfl).mul
      (h.selectedError_measurable n)).mono (ℱ.le (n + 1)) le_rfl)
  intro ω
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (scoreAt_bound h b hb n (h.action n ω) ω) (abs_nonneg _)).trans
    (by simpa only [one_mul] using h.error_bound n (h.action n ω) ω)

theorem noiseStatistic_conditional_zero (n : ℕ) :
    μ[noiseStatistic h b n | h.pre n] =ᵐ[μ] fun _ => 0 := by
  have hpull := condExp_mul_of_stronglyMeasurable_left (score_measurable h b n).stronglyMeasurable
    (noiseStatistic_integrable h b hb n) (h.selectedError_integrable n)
  have hp : μ[noiseStatistic h b n | h.afterAction n] =ᵐ[μ] fun _ => 0 := by
    filter_upwards [hpull, h.selectedError_conditional_zero n] with ω hp hz
    change (μ[noiseStatistic h b n | h.afterAction n]) ω =
      score h b n ω * (μ[h.selectedError n | h.afterAction n]) ω at hp
    simpa only [hz, mul_zero] using hp
  exact PairConfidence.conditional_zero_down (h.pre_le_action n) (h.action_le n) hp

omit hb in
lemma signalAt_measurable (n : ℕ) (a : ι) :
    Measurable[h.pre n] (fun ω => scoreAt h b n a ω * (θ a + h.drift n ω)) :=
  ((scoreAt_measurable h b n a).mono (h.past_le_pre n) le_rfl).mul
    (measurable_const.add (h.drift_measurable n))

lemma signalAt_bound (n : ℕ) (a : ι) (ω : Ω) :
    |scoreAt h b n a ω * (θ a + h.drift n ω)| ≤ R + M := by
  rw [abs_mul]
  have hz0 : 0 ≤ θ a + h.drift n ω := by linarith [(h.theta_range a).1, (h.drift_range n ω).1]
  have hzu : θ a + h.drift n ω ≤ R + M := by linarith [(h.theta_range a).2, (h.drift_range n ω).2]
  exact (mul_le_mul_of_nonneg_right (scoreAt_bound h b hb n a ω) (abs_nonneg _)).trans
    (by simpa only [one_mul, abs_of_nonneg hz0] using hzu)

lemma signalStatistic_integrable (n : ℕ) : Integrable (signalStatistic h b n) μ :=
  PairConfidence.selected_integrable ((h.action_measurable n).mono (h.action_le n) le_rfl)
    (fun a => PairConfidence.bounded_integrable ((signalAt_measurable h b n a).mono (h.pre_le n) le_rfl)
      (signalAt_bound h b hb n a))

theorem signalStatistic_conditional_mean (n : ℕ) :
    μ[signalStatistic h b n | h.pre n] =ᵐ[μ] predictableMean h b n := by
  have ht := PairConfidence.conditional_selected
    ((h.action_measurable n).mono (h.action_le n) le_rfl) (h.categorical n)
    (fun a ω => scoreAt h b n a ω * (θ a + h.drift n ω))
    (fun a => (signalAt_measurable h b n a).stronglyMeasurable)
    (fun a => PairConfidence.bounded_integrable ((signalAt_measurable h b n a).mono (h.pre_le n) le_rfl)
      (signalAt_bound h b hb n a))
  filter_upwards [ht] with ω ht
  exact ht.trans (by
    simpa only [scoreAt, mul_assoc] using directionScore_signal (fun a => h.p n a ω) b θ (h.drift n ω) (h.p_sum n ω))

theorem statistic_conditional_mean (n : ℕ) :
    μ[statistic h b n | ℱ n] =ᵐ[μ] predictableMean h b n := by
  have heq : statistic h b n = signalStatistic h b n - noiseStatistic h b n := by
    funext ω
    dsimp [statistic, signalStatistic, noiseStatistic, PairConfidence.SamplingModel.selectedError]
    rw [h.residual_eq]
    ring
  have hs := condExp_sub (signalStatistic_integrable h b hb n) (noiseStatistic_integrable h b hb n) (h.pre n)
  have hp : μ[statistic h b n | h.pre n] =ᵐ[μ] predictableMean h b n := by
    rw [heq]
    filter_upwards [hs, signalStatistic_conditional_mean h b hb n, noiseStatistic_conditional_zero h b hb n] with ω hs hm hz
    change (μ[signalStatistic h b n - noiseStatistic h b n | h.pre n]) ω =
      (μ[signalStatistic h b n | h.pre n]) ω - (μ[noiseStatistic h b n | h.pre n]) ω at hs
    simpa only [hm, hz, sub_zero] using hs
  exact PairConfidence.conditional_down (h.past_le_pre n) (h.pre_le n) hp
    (mean_measurable h b n).stronglyMeasurable (mean_integrable h b hb n)

theorem increment_conditional_zero (n : ℕ) : μ[increment h b n | ℱ n] =ᵐ[μ] fun _ => 0 := by
  have ht := condExp_sub (statistic_integrable h b hb n) (mean_integrable h b hb n) (ℱ n)
  have hm := condExp_of_stronglyMeasurable (ℱ.le n) (mean_measurable h b n).stronglyMeasurable (mean_integrable h b hb n)
  filter_upwards [ht, statistic_conditional_mean h b hb n] with ω ht hs
  change (μ[increment h b n | ℱ n]) ω = (μ[statistic h b n | ℱ n]) ω - (μ[predictableMean h b n | ℱ n]) ω at ht
  simpa only [hm, hs, sub_self] using ht

lemma statistic_conditional_second_le (n : ℕ) :
    μ[fun ω => (statistic h b n ω) ^ 2 | ℱ n] ≤ᵐ[μ]
      fun ω => (R + M + D) ^ 2 * information h b n ω := by
  have hSi := PairConfidence.bounded_square_integrable (μ := μ)
    ((score_measurable h b n).mono (h.action_le n) le_rfl)
    (fun ω => scoreAt_bound h b hb n (h.action n ω) ω)
  have hWi := PairConfidence.bounded_square_integrable (μ := μ)
    ((statistic_measurable h b n).mono (ℱ.le (n + 1)) le_rfl) (statistic_bound h b hb n)
  have hpoint (ω : Ω) : (statistic h b n ω) ^ 2 ≤ (R + M + D) ^ 2 * (score h b n ω) ^ 2 := by
    have hH : 0 ≤ R + M + D := by linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg]
    have hy : (h.residual n ω) ^ 2 ≤ (R + M + D) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hH).2 (h.residual_bound n ω)
    dsimp [statistic]
    rw [mul_pow]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hy (sq_nonneg (score h b n ω))
  have hmono := condExp_mono (m := ℱ n) hWi (hSi.const_mul ((R + M + D) ^ 2)) (Eventually.of_forall hpoint)
  have hm := condExp_smul (μ := μ) ((R + M + D) ^ 2) (fun ω => (score h b n ω) ^ 2) (ℱ n)
  filter_upwards [hmono, hm, score_conditional_second h b hb n] with ω hl hm hs
  change (μ[fun ω => (R + M + D) ^ 2 * (score h b n ω) ^ 2 | ℱ n]) ω =
    (R + M + D) ^ 2 * (μ[fun ω => (score h b n ω) ^ 2 | ℱ n]) ω at hm
  simpa only [hm, hs] using hl

theorem increment_conditional_second_le (n : ℕ) :
    μ[fun ω => (increment h b n ω) ^ 2 | ℱ n] ≤ᵐ[μ]
      fun ω => (R + M + D) ^ 2 * information h b n ω := by
  have hwm := (statistic_measurable h b n).mono (ℱ.le (n + 1)) le_rfl
  have hmm := (mean_measurable h b n).mono (ℱ.le n) le_rfl
  have hWi := statistic_integrable h b hb n
  have hW2i := PairConfidence.bounded_square_integrable (μ := μ) hwm (statistic_bound h b hb n)
  have hb2i := PairConfidence.bounded_square_integrable (μ := μ) hmm (mean_bound h b hb n)
  have hbWi := hWi.bdd_mul' hmm.stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using mean_bound h b hb n ω)
  exact (PairConfidence.centered_square_le (ℱ.le n) (mean_measurable h b n).stronglyMeasurable
    hWi hW2i hbWi hb2i (statistic_conditional_mean h b hb n)).trans (statistic_conditional_second_le h b hb n)

/-- CND's genuine direction data, derived from the action/encoder laws. -/
theorem bernstein_data :
    Bernstein.BoundedIncrements ℱ μ (increment h b)
      (fun n ω => (R + M + D) ^ 2 * information h b n ω) (2 * (R + M + D)) := by
  refine ⟨by linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg],
    fun n => (increment_measurable h b n).stronglyMeasurable,
    fun n => ((information_measurable h b n).const_mul _).stronglyMeasurable,
    increment_bound h b hb, ?_, increment_conditional_zero h b hb,
    increment_conditional_second_le h b hb⟩
  intro n ω
  exact mul_nonneg (sq_nonneg _) (information_bounds h b hb n ω).1

/-- A concrete nonnegative exponential supermartingale for CND directions. -/
theorem directional_supermartingale {t : ℝ} (ht : 0 ≤ t) (hsmall : t * (2 * (R + M + D)) ≤ 3 / 2) :
    Supermartingale (Bernstein.exponentialProcess (increment h b)
      (fun n ω => (R + M + D) ^ 2 * information h b n ω) t) ℱ μ :=
  Bernstein.exponential_supermartingale (bernstein_data h b hb) ht hsmall

theorem directional_maximal (hH : 0 < R + M + D) (N : ℕ) {v L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ N,
      2 * Real.sqrt (v * L) + (4 * (R + M + D) / 3) * L ≤ Bernstein.sumProcess (increment h b) n ω ∧
      Bernstein.sumProcess (fun i ω => (R + M + D) ^ 2 * information h b i ω) n ω ≤ v} ≤ Real.exp (-L) :=
  by
    have hc : 2 * (2 * (R + M + D)) = 4 * (R + M + D) := by ring
    simpa only [hc] using bernstein_maximal (bernstein_data h b hb) (by linarith) N hv hL

end Directional
end Model
end Part2.CNDProbability
