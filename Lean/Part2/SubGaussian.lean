import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Convert

/-!
# Single-round exponential moment for finite-action orthogonal scores

The measures `μ a` are the noise laws conditional on the current action and on a
fixed legal pre-round information state. They are probability measures on the
original noise space, not laws conditioned on a confidence/success event.

`finite_action_sg2` derives the target exponential moment from conditional noise
sub-Gaussianity and deterministic score moments. It does not assume SG2. The
identification of these fiber laws with a concrete online game's disintegration,
and the sequential Bernstein/peeling argument, are separate obligations.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace Part2.SubGaussian

lemma exp_le_quadratic {x : ℝ} (hx : |x| ≤ 1) :
    exp x ≤ 1 + x + x ^ 2 := by
  have h := (abs_le.mp (abs_exp_sub_one_sub_id_le hx)).2
  linarith

lemma exp_chord {a y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    exp (a * y) ≤ 1 + (exp a - 1) * y := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ a)
    (show 0 ≤ 1 - y by linarith) hy0 (show 1 - y + y = 1 by ring)
  calc
    exp (a * y) = exp ((1 - y) • (0 : ℝ) + y • a) := by
      congr 1
      simp [smul_eq_mul, mul_comm]
    _ ≤ (1 - y) • exp 0 + y • exp a := h
    _ = 1 + (exp a - 1) * y := by simp [smul_eq_mul]; ring

lemma exp_small_sub_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    exp a - 1 ≤ 2 * a := by
  have h := abs_exp_sub_one_le (show |a| ≤ 1 by rwa [abs_of_nonneg ha0])
  rw [abs_of_nonneg ha0] at h
  exact (le_abs_self _).trans h

lemma exp_square (a : ℝ) : (exp a) ^ 2 = exp (2 * a) := by
  rw [pow_two, ← exp_add]
  congr 1
  ring

section Finite

variable {ι : Type*} [Fintype ι]

lemma finite_centered_exp_bound (p B : ι → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (hmean : ∑ a, p a * B a = 0)
    {H0 v t : ℝ} (hsecond : ∑ a, p a * (B a) ^ 2 ≤ H0 ^ 2 * v)
    (hsmall : ∀ a, |2 * t * B a| ≤ 1) :
    (∑ a, p a * exp (2 * t * B a)) ≤ exp (4 * t ^ 2 * H0 ^ 2 * v) := by
  calc
    (∑ a, p a * exp (2 * t * B a))
        ≤ ∑ a, p a * (1 + 2 * t * B a + (2 * t * B a) ^ 2) := by
          exact Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left (exp_le_quadratic (hsmall a)) (hp a)
    _ = (∑ a, p a) + 2 * t * (∑ a, p a * B a) +
        4 * t ^ 2 * (∑ a, p a * (B a) ^ 2) := by
          simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = 1 + 4 * t ^ 2 * (∑ a, p a * (B a) ^ 2) := by rw [hpsum, hmean]; ring
    _ ≤ 1 + 4 * t ^ 2 * (H0 ^ 2 * v) := by gcongr
    _ ≤ exp (4 * t ^ 2 * H0 ^ 2 * v) := by
          have h := add_one_le_exp (4 * t ^ 2 * H0 ^ 2 * v)
          nlinarith

lemma finite_score_exp_bound (p X : ι → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (hX : ∀ a, (X a) ^ 2 ≤ 1)
    {v a : ℝ} (hsecond : ∑ i, p i * (X i) ^ 2 = v)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ i, p i * exp (a * (X i) ^ 2)) ≤ exp (2 * a * v) := by
  have hv : 0 ≤ v := by
    rw [← hsecond]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)
  calc
    (∑ i, p i * exp (a * (X i) ^ 2))
        ≤ ∑ i, p i * (1 + (exp a - 1) * (X i) ^ 2) := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (exp_chord (sq_nonneg _) (hX i)) (hp i)
    _ = (∑ i, p i) + (exp a - 1) * (∑ i, p i * (X i) ^ 2) := by
          simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = 1 + (exp a - 1) * v := by rw [hpsum, hsecond]
    _ ≤ 1 + 2 * a * v := by
          nlinarith [mul_le_mul_of_nonneg_right (exp_small_sub_one ha0 ha1) hv]
    _ ≤ exp (2 * a * v) := by linarith [add_one_le_exp (2 * a * v)]

lemma finite_exp_cauchy (p B X : ι → ℝ) (hp : ∀ a, 0 ≤ p a) (t ν : ℝ) :
    (∑ a, p a * exp (t * B a + ν ^ 2 * t ^ 2 * (X a) ^ 2 / 2)) ^ 2 ≤
      (∑ a, p a * exp (2 * t * B a)) *
      (∑ a, p a * exp (ν ^ 2 * t ^ 2 * (X a) ^ 2)) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
  · intro i _
    exact mul_nonneg (hp i) (exp_nonneg _)
  · intro i _
    exact mul_nonneg (hp i) (exp_nonneg _)
  · intro i _
    rw [mul_pow, exp_square, mul_mul_mul_comm, ← exp_add]
    congr 2 <;> ring

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The exponential defining each mixed mgf is genuinely integrable; the Bochner
integral's default value at nonintegrable functions is never used as a shortcut. -/
lemma action_exp_integrable (B X : ι → ℝ) (μ : ι → Measure Ω)
    (η : ι → Ω → ℝ) (ν : ℝ≥0)
    (hη : ∀ a, HasSubgaussianMGF (η a) (ν ^ 2) (μ a)) (t : ℝ) (a : ι) :
    Integrable (fun ω => exp (t * (B a + X a * η a ω))) (μ a) := by
  have h := ((hη a).integrable_exp_mul (t * X a)).const_mul (exp (t * B a))
  convert h using 1
  ext ω
  rw [← exp_add]
  congr 1
  ring

/-- The first step of SG1: integrate the action-conditional unbounded noise.
No independence between `B`, the score, and the selected noise is imposed:
`B a` and `X a` are constants inside the conditional fiber `μ a`. -/
lemma finite_action_mgf_bound (p B X : ι → ℝ) (hp : ∀ a, 0 ≤ p a)
    (μ : ι → Measure Ω) (η : ι → Ω → ℝ) (ν : ℝ≥0)
    (hη : ∀ a, HasSubgaussianMGF (η a) (ν ^ 2) (μ a)) (t : ℝ) :
    (∑ a, p a * mgf (fun ω => B a + X a * η a ω) (μ a) t) ≤
      ∑ a, p a * exp (t * B a + (ν : ℝ) ^ 2 * t ^ 2 * (X a) ^ 2 / 2) := by
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hp a)
  calc
    mgf (fun ω => B a + X a * η a ω) (μ a) t =
        exp (t * B a) * mgf (η a) (μ a) (t * X a) := by
          unfold mgf
          simp_rw [mul_add, ← mul_assoc, exp_add]
          rw [integral_const_mul]
    _ ≤ exp (t * B a) * exp ((ν : ℝ) ^ 2 * (t * X a) ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
          simpa only [NNReal.coe_pow] using (hη a).mgf_le (t * X a)
    _ = exp (t * B a + (ν : ℝ) ^ 2 * t ^ 2 * (X a) ^ 2 / 2) := by
          rw [← exp_add]
          congr 1
          ring

/-- SG2 on a fixed pre-round fiber, with the scalar smallness conditions made
explicit. `hmean` and `hBsecond` concern only the finite-action signal, not an
assumed mgf bound. The conditional noise can be unbounded. -/
theorem finite_action_sg2_of_small (p B X : ι → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (μ : ι → Measure Ω)
    (η : ι → Ω → ℝ) (ν : ℝ≥0)
    (hη : ∀ a, HasSubgaussianMGF (η a) (ν ^ 2) (μ a))
    {H0 v t : ℝ} (hH0 : 0 ≤ H0) (hv : 0 ≤ v)
    (hmean : ∑ a, p a * B a = 0)
    (hBsecond : ∑ a, p a * (B a) ^ 2 ≤ H0 ^ 2 * v)
    (hX : ∀ a, (X a) ^ 2 ≤ 1) (hXsecond : ∑ a, p a * (X a) ^ 2 = v)
    (hBsmall : ∀ a, |2 * t * B a| ≤ 1) (hνsmall : (ν : ℝ) ^ 2 * t ^ 2 ≤ 1) :
    (∑ a, p a * mgf (fun ω => B a + X a * η a ω) (μ a) t) ≤
      exp (2 * (H0 + (ν : ℝ)) ^ 2 * t ^ 2 * v) := by
  have hA := finite_centered_exp_bound p B hp hpsum hmean hBsecond hBsmall
  have hC := finite_score_exp_bound p X hp hpsum hX hXsecond
    (mul_nonneg (sq_nonneg (ν : ℝ)) (sq_nonneg t)) hνsmall
  have hCS := finite_exp_cauchy p B X hp t (ν : ℝ)
  have hC' : (∑ a, p a * exp ((ν : ℝ) ^ 2 * t ^ 2 * (X a) ^ 2)) ≤
      exp (2 * ((ν : ℝ) ^ 2 * t ^ 2) * v) := hC
  have hprod := mul_le_mul hA hC'
    (Finset.sum_nonneg fun a _ => mul_nonneg (hp a) (exp_nonneg _)) (exp_nonneg _)
  have hcoeff : 4 * H0 ^ 2 + 2 * (ν : ℝ) ^ 2 ≤ 4 * (H0 + (ν : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg hH0 ν.coe_nonneg, sq_nonneg (ν : ℝ)]
  have hexp : exp (4 * t ^ 2 * H0 ^ 2 * v) *
      exp (2 * ((ν : ℝ) ^ 2 * t ^ 2) * v) ≤
      exp (4 * (H0 + (ν : ℝ)) ^ 2 * t ^ 2 * v) := by
    rw [← exp_add, exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (sq_nonneg t) hv)]
  have hsquare := hCS.trans (hprod.trans hexp)
  have hsquare' : (∑ a, p a *
      exp (t * B a + (ν : ℝ) ^ 2 * t ^ 2 * (X a) ^ 2 / 2)) ^ 2 ≤
      (exp (2 * (H0 + (ν : ℝ)) ^ 2 * t ^ 2 * v)) ^ 2 := by
    rw [exp_square]
    convert hsquare using 1 <;> congr 1 <;> ring
  have hbound : (∑ a, p a *
      exp (t * B a + (ν : ℝ) ^ 2 * t ^ 2 * (X a) ^ 2 / 2)) ≤
      exp (2 * (H0 + (ν : ℝ)) ^ 2 * t ^ 2 * v) := by
    nlinarith [exp_pos (2 * (H0 + (ν : ℝ)) ^ 2 * t ^ 2 * v)]
  exact (finite_action_mgf_bound p B X hp μ η ν hη t).trans hbound

/-- The paper's parameter range implies both elementary smallness conditions.
This is the full single-round SG2 estimate under explicit signal moments and
action-conditional sub-Gaussian noise laws. -/
theorem finite_action_sg2 (p B X : ι → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (μ : ι → Measure Ω)
    [∀ a, IsProbabilityMeasure (μ a)] (η : ι → Ω → ℝ) (ν : ℝ≥0)
    (hη : ∀ a, HasSubgaussianMGF (η a) (ν ^ 2) (μ a))
    {H0 v t : ℝ} (hH0 : 0 ≤ H0) (hH : 0 < H0 + (ν : ℝ)) (hv : 0 ≤ v)
    (hmean : ∑ a, p a * B a = 0)
    (hBsecond : ∑ a, p a * (B a) ^ 2 ≤ H0 ^ 2 * v)
    (hBbound : ∀ a, |B a| ≤ 2 * H0)
    (hX : ∀ a, (X a) ^ 2 ≤ 1) (hXsecond : ∑ a, p a * (X a) ^ 2 = v)
    (ht : |t| ≤ 1 / (8 * (H0 + (ν : ℝ)))) :
    (∑ a, p a * mgf (fun ω => B a + X a * η a ω) (μ a) t) ≤
      exp (2 * (H0 + (ν : ℝ)) ^ 2 * t ^ 2 * v) := by
  have htmul : |t| * (8 * (H0 + (ν : ℝ))) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp ht
  have hBsmall (a : ι) : |2 * t * B a| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hm := mul_le_mul_of_nonneg_left (hBbound a)
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (abs_nonneg t))
    have hn := mul_nonneg (abs_nonneg t) ν.coe_nonneg
    nlinarith
  have hνt0 : 0 ≤ (ν : ℝ) * |t| := mul_nonneg ν.coe_nonneg (abs_nonneg t)
  have hνt : (ν : ℝ) * |t| ≤ 1 := by
    have hm := mul_nonneg hH0 (abs_nonneg t)
    nlinarith
  have hνsmall : (ν : ℝ) ^ 2 * t ^ 2 ≤ 1 := by
    have hq := mul_le_mul hνt hνt hνt0 zero_le_one
    simpa only [← pow_two, mul_pow, sq_abs, one_pow] using hq
  exact finite_action_sg2_of_small p B X hp hpsum μ η ν hη hH0 hv
    hmean hBsecond hX hXsecond hBsmall hνsmall

end Finite

section Encoder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ e : Ω → ℝ} {σ2 : ℝ≥0}

/-- A centered independent bounded encoder adds its Hoeffding variance proxy.
Apply inside the legal pre-action physical/noise fiber; marginal centering alone
does not establish these hypotheses. -/
theorem encoded_noise_subGaussian {a b : ℝ} (hξ : HasSubgaussianMGF ξ σ2 μ)
    (he : AEMeasurable e μ) (hbound : ∀ᵐ ω ∂μ, e ω ∈ Set.Icc a b)
    (hcenter : ∫ ω, e ω ∂μ = 0) (hindep : IndepFun ξ e μ) :
    HasSubgaussianMGF (fun ω => ξ ω - e ω)
      (σ2 + (‖b - a‖₊ / 2) ^ 2) μ := by
  have heSG := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero he hbound hcenter
  have h := hξ.add_of_indepFun heSG.neg (hindep.neg_right)
  simpa [sub_eq_add_neg] using h

/-- Correlation between comparator and selected noise is allowed. Equal
variance proxies `ν2` produce the conservative proxy `4 * ν2`, i.e. standard
deviation proxy `2ν`. -/
theorem correlated_noise_difference {X Y : Ω → ℝ} {ν2 : ℝ≥0}
    (hX : HasSubgaussianMGF X ν2 μ) (hY : HasSubgaussianMGF Y ν2 μ) :
    HasSubgaussianMGF (fun ω => X ω - Y ω) (4 * ν2) μ := by
  have h := hX.add hY.neg
  have hc : (ν2.sqrt + ν2.sqrt) ^ 2 = 4 * ν2 := by
    rw [← two_mul, mul_pow, NNReal.sq_sqrt]
    norm_num
  rw [hc] at h
  simpa [sub_eq_add_neg] using h

end Encoder

end Part2.SubGaussian
