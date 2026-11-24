import Part2.HinfExpected
import Part2.HinfStability
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Real categorical sampling, integrability, and expected H-INF regret.
This staging module is not part of the frozen root certification. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace Part2.HinfProbability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def categoricalPMF (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (p i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hs]
    simp)

variable {H : Type*} [MeasurableSpace H]

/-- An actual Markov categorical sampler, not an expected-loss oracle. -/
def categoricalKernel (p : H → ι → ℝ) (hp : ∀ h i, 0 ≤ p h i)
    (hs : ∀ h, ∑ i, p h i = 1) (hm : ∀ i, Measurable (fun h => p h i)) : Kernel H ι where
  toFun h := (categoricalPMF (p h) (hp h) (hs h)).toMeasure
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s _
    simp only [PMF.toMeasure_apply_fintype]
    apply Finset.measurable_sum
    intro i _
    by_cases hi : i ∈ s
    · simpa [Set.indicator_apply, hi, categoricalPMF] using (hm i).ennreal_ofReal
    · simp [Set.indicator_apply, hi]

instance categoricalKernel_markov (p : H → ι → ℝ) (hp : ∀ h i, 0 ≤ p h i)
    (hs : ∀ h, ∑ i, p h i = 1) (hm : ∀ i, Measurable (fun h => p h i)) :
    IsMarkovKernel (categoricalKernel p hp hs hm) :=
  ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩

theorem categoricalKernel_singleton (p : H → ι → ℝ) (hp : ∀ h i, 0 ≤ p h i)
    (hs : ∀ h, ∑ i, p h i = 1) (hm : ∀ i, Measurable (fun h => p h i)) (h : H) (a : ι) :
    categoricalKernel p hp hs hm h {a} = ENNReal.ofReal (p h a) := by
  change (categoricalPMF (p h) (hp h) (hs h)).toMeasure {a} = _
  simp [PMF.toMeasure_apply_fintype, Set.indicator_apply, categoricalPMF]

/-- Finite fibers do not require a uniform bound across histories. -/
theorem finite_integrable (ν : Measure ι) [IsFiniteMeasure ν] (f : ι → ℝ) :
    Integrable f ν := by
  apply (integrable_const (∑ i, |f i|)).mono'
    (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ fun i => by
    simpa only [Real.norm_eq_abs] using
      (Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg (f j))
        (Finset.mem_univ i))

theorem categorical_integral (p : H → ι → ℝ) (hp : ∀ h i, 0 ≤ p h i)
    (hs : ∀ h, ∑ i, p h i = 1) (hm : ∀ i, Measurable (fun h => p h i))
    (h : H) (f : ι → ℝ) :
    ∫ a, f a ∂categoricalKernel p hp hs hm h = ∑ a, p h a * f a := by
  rw [integral_fintype f (finite_integrable _ f)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Measure.real, categoricalKernel_singleton, ENNReal.toReal_ofReal (hp h a),
    smul_eq_mul]

/-- The conditional categorical norm is sufficient to prove joint L1
integrability, even when the realized importance weight is unbounded. -/
theorem joint_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    (p : H → ι → ℝ) (hp : ∀ h i, 0 ≤ p h i)
    (hs : ∀ h, ∑ i, p h i = 1) (hm : ∀ i, Measurable (fun h => p h i))
    (F : H × ι → ℝ) (hF : Measurable F)
    (hnorm : Integrable (fun h => ∑ a, p h a * ‖F (h, a)‖) μ) :
    Integrable F (μ ⊗ₘ categoricalKernel p hp hs hm) := by
  apply (Measure.integrable_compProd_iff hF.aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ fun h => finite_integrable _ (fun a => F (h, a))
  · simpa only [categorical_integral] using hnorm

theorem joint_integral (μ : Measure H) [IsProbabilityMeasure μ]
    (p : H → ι → ℝ) (hp : ∀ h i, 0 ≤ p h i)
    (hs : ∀ h, ∑ i, p h i = 1) (hm : ∀ i, Measurable (fun h => p h i))
    (F : H × ι → ℝ) (hF : Measurable F)
    (hnorm : Integrable (fun h => ∑ a, p h a * ‖F (h, a)‖) μ) :
    ∫ z, F z ∂(μ ⊗ₘ categoricalKernel p hp hs hm) =
      ∫ h, ∑ a, p h a * F (h, a) ∂μ := by
  rw [Measure.integral_compProd (joint_integrable μ p hp hs hm F hF hnorm)]
  simp only [categorical_integral]

theorem joint_integrable_of_fiber_bound (μ : Measure H) [IsProbabilityMeasure μ]
    (p : H → ι → ℝ) (hp : ∀ h i, 0 ≤ p h i)
    (hs : ∀ h, ∑ i, p h i = 1) (hm : ∀ i, Measurable (fun h => p h i))
    (F : H × ι → ℝ) (hF : Measurable F) (C : ℝ)
    (hbound : ∀ h, ∑ a, p h a * ‖F (h, a)‖ ≤ C) :
    Integrable F (μ ⊗ₘ categoricalKernel p hp hs hm) := by
  apply joint_integrable μ p hp hs hm F hF
  have hmeas : Measurable (fun h => ∑ a, p h a * ‖F (h, a)‖) :=
    Finset.measurable_sum _ fun a _ => (hm a).mul
      ((hF.comp (measurable_id.prodMk measurable_const)).norm)
  apply (integrable_const C).mono' hmeas.aestronglyMeasurable
  exact ae_of_all _ fun h => by
    have hnonneg : 0 ≤ ∑ a, p h a * ‖F (h, a)‖ :=
      Finset.sum_nonneg fun a _ => mul_nonneg (hp h a) (norm_nonneg _)
    change |∑ a, p h a * ‖F (h, a)‖| ≤ C
    rw [abs_of_nonneg hnonneg]
    exact hbound h

section OriginalConditionalLaw

variable {Ω : Type*} [MeasurableSpace Ω] [Nonempty ι] [StandardBorelSpace ι]
  (ν : Measure Ω) [IsProbabilityMeasure ν] (history : Ω → H) (A : Ω → ι)
  (hH : Measurable history) (hA : Measurable A)
  (p : H → ι → ℝ) (hp : ∀ h i, 0 ≤ p h i)
  (hs : ∀ h, ∑ i, p h i = 1) (hm : ∀ i, Measurable (fun h => p h i))

include hH hA

/-- The paper's conditional sampling law, expressed directly as conditional
expectations of action indicators, determines the actual joint law. No
independence of history, opponents' samples, or the environment is added. -/
theorem joint_law_of_conditional_sampling
    (hsample : ∀ i, ν[(A ⁻¹' {i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace H).comap history] =ᵐ[ν]
        fun ω => p (history ω) i) :
    ν.map (fun ω => (history ω, A ω)) =
      (ν.map history) ⊗ₘ categoricalKernel p hp hs hm := by
  have hcoord (i : ι) : ∀ᵐ h ∂ν.map history,
      (condDistrib A history ν h).real {i} = p h i := by
    apply (ae_map_iff hH.aemeasurable ?_).2
    · exact (condDistrib_ae_eq_condExp hH hA (measurableSet_singleton i)).trans (hsample i)
    · exact measurableSet_eq_fun
        ((Kernel.measurable_coe _ (measurableSet_singleton i)).ennreal_toReal) (hm i)
  have heq : condDistrib A history ν =ᵐ[ν.map history] categoricalKernel p hp hs hm := by
    filter_upwards [ae_all_iff.mpr hcoord] with h hh
    apply ext_iff_measureReal_singleton.mpr
    intro i
    rw [hh i]
    simp only [Measure.real, categoricalKernel_singleton, ENNReal.toReal_ofReal (hp h i)]
  exact (condDistrib_ae_eq_iff_measure_eq_compProd history hA.aemeasurable _).mp heq

end OriginalConditionalLaw

def rawEstimate (b ρ p : H → ι → ℝ) (z : H × ι) (k : ι) : ℝ :=
  b z.1 k + if z.2 = k then ρ z.1 k / p z.1 k else 0

theorem rawEstimate_measurable (b ρ p : H → ι → ℝ)
    (hb : ∀ i, Measurable (fun h => b h i))
    (hρ : ∀ i, Measurable (fun h => ρ h i))
    (hp : ∀ i, Measurable (fun h => p h i)) (k : ι) :
    Measurable (fun z : H × ι => rawEstimate b ρ p z k) := by
  apply measurable_from_prod_countable_left
  intro a
  by_cases ha : a = k
  · simpa [rawEstimate, ha] using (hb k).add ((hρ k).div (hp k))
  · simpa [rawEstimate, ha] using hb k

/-- Exact unbiasedness is for d=b+rho. In canonical learn-loss notation this
is ell+delta, so conversion to ell costs its separate quantization term. -/
theorem rawEstimate_fiber_mean (b ρ p : H → ι → ℝ)
    (hp : ∀ h i, 0 < p h i) (hs : ∀ h, ∑ i, p h i = 1)
    (hm : ∀ i, Measurable (fun h => p h i)) (h : H) (k : ι) :
    ∫ a, rawEstimate b ρ p (h, a) k
      ∂categoricalKernel p (fun h i => (hp h i).le) hs hm h = b h k + ρ h k := by
  rw [categorical_integral]
  simp only [rawEstimate, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul,
    mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp [(hp h k).ne']

theorem rawEstimate_nonneg (b ρ p : H → ι → ℝ)
    (hb : ∀ h i, 0 ≤ b h i) (hρ : ∀ h i, 0 ≤ ρ h i) (hp : ∀ h i, 0 < p h i)
    (z : H × ι) (k : ι) : 0 ≤ rawEstimate b ρ p z k := by
  unfold rawEstimate
  split_ifs
  · exact add_nonneg (hb z.1 k) (div_nonneg (hρ z.1 k) (hp z.1 k).le)
  · simpa using hb z.1 k

theorem rawEstimate_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    (b ρ p : H → ι → ℝ) (B R : ℝ)
    (hp : ∀ h i, 0 < p h i) (hs : ∀ h, ∑ i, p h i = 1)
    (hpm : ∀ i, Measurable (fun h => p h i))
    (hbm : ∀ i, Measurable (fun h => b h i))
    (hρm : ∀ i, Measurable (fun h => ρ h i))
    (hb : ∀ h i, 0 ≤ b h i ∧ b h i ≤ B)
    (hρ : ∀ h i, 0 ≤ ρ h i ∧ ρ h i ≤ R) (k : ι) :
    Integrable (fun z => rawEstimate b ρ p z k)
      (μ ⊗ₘ categoricalKernel p (fun h i => (hp h i).le) hs hpm) := by
  apply joint_integrable_of_fiber_bound μ p (fun h i => (hp h i).le) hs hpm _
    (rawEstimate_measurable b ρ p hbm hρm hpm k) (B + R)
  intro h
  have hmean := rawEstimate_fiber_mean b ρ p hp hs hpm h k
  rw [categorical_integral] at hmean
  simp_rw [Real.norm_eq_abs,
    abs_of_nonneg (rawEstimate_nonneg b ρ p (fun h i => (hb h i).1)
      (fun h i => (hρ h i).1) hp _ k)]
  rw [hmean]
  linarith [(hb h k).2, (hρ h k).2]

theorem residualMoment_measurable (q : ℝ) (hq : 1 < q) (p ρ : H → ι → ℝ)
    (hpm : ∀ i, Measurable (fun h => p h i))
    (hρm : ∀ i, Measurable (fun h => ρ h i)) :
    Measurable (fun z : H × ι => HinfExpected.residualMoment q (p z.1) (ρ z.1) z.2) := by
  apply measurable_from_prod_countable_left
  intro a
  have he : 0 ≤ 1 + 1 / q := by linarith [one_div_pos.mpr (lt_trans zero_lt_one hq)]
  exact ((Real.continuous_rpow_const he).measurable.comp (hpm a)).mul
    (((hρm a).div (hpm a)).pow_const 2)

/-- The actual residual moment is integrable with the original random
probabilities; its bound has no numerical probability floor. -/
theorem residualMoment_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    (q R : ℝ) (p ρ : H → ι → ℝ) (hq : 1 < q)
    (hp : ∀ h i, 0 < p h i) (hs : ∀ h, ∑ i, p h i = 1)
    (hpm : ∀ i, Measurable (fun h => p h i))
    (hρm : ∀ i, Measurable (fun h => ρ h i))
    (hρ : ∀ h i, 0 ≤ ρ h i ∧ ρ h i ≤ R) :
    Integrable (fun z : H × ι => HinfExpected.residualMoment q (p z.1) (ρ z.1) z.2)
      (μ ⊗ₘ categoricalKernel p (fun h i => (hp h i).le) hs hpm) := by
  apply joint_integrable_of_fiber_bound μ p (fun h i => (hp h i).le) hs hpm _
    (residualMoment_measurable q hq p ρ hpm hρm)
    (R ^ 2 * (Fintype.card ι : ℝ) ^ (1 - 1 / q))
  intro h
  simp_rw [Real.norm_eq_abs, HinfExpected.residualMoment,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hp h _).le _) (sq_nonneg _))]
  exact HinfExpected.mean_residualMoment_le q R (p h) (ρ h) hq (hp h) (hs h) (hρ h)

theorem integral_residualMoment_le (μ : Measure H) [IsProbabilityMeasure μ]
    (q R : ℝ) (p ρ : H → ι → ℝ) (hq : 1 < q)
    (hp : ∀ h i, 0 < p h i) (hs : ∀ h, ∑ i, p h i = 1)
    (hpm : ∀ i, Measurable (fun h => p h i))
    (hρm : ∀ i, Measurable (fun h => ρ h i))
    (hρ : ∀ h i, 0 ≤ ρ h i ∧ ρ h i ≤ R) :
    (∫ z, HinfExpected.residualMoment q (p z.1) (ρ z.1) z.2
      ∂(μ ⊗ₘ categoricalKernel p (fun h i => (hp h i).le) hs hpm)) ≤
        R ^ 2 * (Fintype.card ι : ℝ) ^ (1 - 1 / q) := by
  rw [Measure.integral_compProd (residualMoment_integrable μ q R p ρ hq hp hs hpm hρm hρ)]
  simp_rw [categorical_integral]
  calc
    _ ≤ ∫ _h, R ^ 2 * (Fintype.card ι : ℝ) ^ (1 - 1 / q) ∂μ := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun h => Finset.sum_nonneg fun a _ =>
          mul_nonneg (hp h a).le (mul_nonneg (Real.rpow_nonneg (hp h a).le _) (sq_nonneg _)))
        (integrable_const _)
      exact ae_of_all _ fun h =>
        HinfExpected.mean_residualMoment_le q R (p h) (ρ h) hq (hp h) (hs h) (hρ h)
    _ = _ := by simp

theorem raw_dot_identity (b ρ p : H → ι → ℝ) (hp : ∀ h i, 0 < p h i)
    (h : H) (a : ι) :
    HinfExpected.dot (rawEstimate b ρ p (h, a)) (p h) =
      HinfExpected.dot (b h) (p h) + ρ h a := by
  simp only [HinfExpected.dot, rawEstimate, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul]
  simp [(hp h a).ne']

theorem integral_residualMoment_eq (μ : Measure H) [IsProbabilityMeasure μ]
    (q R : ℝ) (p ρ : H → ι → ℝ) (hq : 1 < q)
    (hp : ∀ h i, 0 < p h i) (hs : ∀ h, ∑ i, p h i = 1)
    (hpm : ∀ i, Measurable (fun h => p h i))
    (hρm : ∀ i, Measurable (fun h => ρ h i))
    (hρ : ∀ h i, 0 ≤ ρ h i ∧ ρ h i ≤ R) :
    (∫ z, HinfExpected.residualMoment q (p z.1) (ρ z.1) z.2
      ∂(μ ⊗ₘ categoricalKernel p (fun h i => (hp h i).le) hs hpm)) =
      ∫ h, ∑ i, (p h i) ^ (1 / q) * (ρ h i) ^ 2 ∂μ := by
  rw [Measure.integral_compProd (residualMoment_integrable μ q R p ρ hq hp hs hpm hρm hρ)]
  apply integral_congr_ae
  exact ae_of_all _ fun h => by
    change (∫ a, HinfExpected.residualMoment q (p h) (ρ h) a
      ∂categoricalKernel p (fun h i => (hp h i).le) hs hpm h) = _
    rw [categorical_integral, HinfExpected.mean_residualMoment q (p h) (ρ h) (hp h)]

def fedComparison (b ρ p : H → ι → ℝ) (k : ι) (z : H × ι) : ℝ :=
  HinfExpected.dot (rawEstimate b ρ p z) (p z.1) - rawEstimate b ρ p z k

def physicalComparison (b ρ : H → ι → ℝ) (k : ι) (z : H × ι) : ℝ :=
  (b z.1 z.2 + ρ z.1 z.2) - (b z.1 k + ρ z.1 k)

theorem fedComparison_fiber_mean (b ρ p : H → ι → ℝ)
    (hp : ∀ h i, 0 < p h i) (hs : ∀ h, ∑ i, p h i = 1)
    (hm : ∀ i, Measurable (fun h => p h i)) (h : H) (k : ι) :
    (∫ a, fedComparison b ρ p k (h, a)
      ∂categoricalKernel p (fun h i => (hp h i).le) hs hm h) =
    ∫ a, physicalComparison b ρ k (h, a)
      ∂categoricalKernel p (fun h i => (hp h i).le) hs hm h := by
  unfold fedComparison
  simp_rw [raw_dot_identity b ρ p hp h]
  rw [integral_sub (finite_integrable _ _) (finite_integrable _ _),
    integral_add (finite_integrable _ _) (finite_integrable _ _),
    integral_const, measureReal_univ_eq_one, one_smul,
    rawEstimate_fiber_mean b ρ p hp hs hm h k]
  unfold physicalComparison
  dsimp only [Prod.fst, Prod.snd]
  rw [integral_sub (finite_integrable _ _) (finite_integrable _ _),
    integral_add (finite_integrable _ _) (finite_integrable _ _),
    integral_const, measureReal_univ_eq_one, one_smul, categorical_integral]
  simp_rw [categorical_integral]
  have hbase : HinfExpected.dot (b h) (p h) = ∑ a, p h a * b h a := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hbase]

theorem fedComparison_measurable (b ρ p : H → ι → ℝ)
    (hbm : ∀ i, Measurable (fun h => b h i))
    (hρm : ∀ i, Measurable (fun h => ρ h i))
    (hpm : ∀ i, Measurable (fun h => p h i)) (k : ι) :
    Measurable (fedComparison b ρ p k) := by
  exact (Finset.measurable_sum _ fun i _ =>
    (rawEstimate_measurable b ρ p hbm hρm hpm i).mul ((hpm i).comp measurable_fst)).sub
      (rawEstimate_measurable b ρ p hbm hρm hpm k)

theorem physicalComparison_measurable (b ρ : H → ι → ℝ)
    (hbm : ∀ i, Measurable (fun h => b h i))
    (hρm : ∀ i, Measurable (fun h => ρ h i)) (k : ι) :
    Measurable (physicalComparison b ρ k) := by
  apply measurable_from_prod_countable_left
  intro a
  exact ((hbm a).add (hρm a)).sub ((hbm k).add (hρm k))

theorem physicalComparison_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    (b ρ p : H → ι → ℝ) (B R : ℝ)
    (hp : ∀ h i, 0 < p h i) (hs : ∀ h, ∑ i, p h i = 1)
    (hpm : ∀ i, Measurable (fun h => p h i))
    (hbm : ∀ i, Measurable (fun h => b h i))
    (hρm : ∀ i, Measurable (fun h => ρ h i))
    (hb : ∀ h i, 0 ≤ b h i ∧ b h i ≤ B)
    (hρ : ∀ h i, 0 ≤ ρ h i ∧ ρ h i ≤ R) (k : ι) :
    Integrable (physicalComparison b ρ k)
      (μ ⊗ₘ categoricalKernel p (fun h i => (hp h i).le) hs hpm) := by
  apply joint_integrable_of_fiber_bound μ p (fun h i => (hp h i).le) hs hpm _
    (physicalComparison_measurable b ρ hbm hρm k) (B + R)
  intro h
  calc
    _ ≤ ∑ a, p h a * (B + R) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hp h a).le
      rw [Real.norm_eq_abs, abs_le]
      unfold physicalComparison
      constructor <;> linarith [(hb h a).1, (hb h a).2, (hρ h a).1, (hρ h a).2,
        (hb h k).1, (hb h k).2, (hρ h k).1, (hρ h k).2]
    _ = B + R := by rw [← Finset.sum_mul, hs, one_mul]

theorem fedComparison_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    (b ρ p : H → ι → ℝ) (B R : ℝ)
    (hp : ∀ h i, 0 < p h i) (hs : ∀ h, ∑ i, p h i = 1)
    (hpm : ∀ i, Measurable (fun h => p h i))
    (hbm : ∀ i, Measurable (fun h => b h i))
    (hρm : ∀ i, Measurable (fun h => ρ h i))
    (hb : ∀ h i, 0 ≤ b h i ∧ b h i ≤ B)
    (hρ : ∀ h i, 0 ≤ ρ h i ∧ ρ h i ≤ R) (k : ι) :
    Integrable (fedComparison b ρ p k)
      (μ ⊗ₘ categoricalKernel p (fun h i => (hp h i).le) hs hpm) := by
  have hD : Integrable (fun z : H × ι => HinfExpected.dot (rawEstimate b ρ p z) (p z.1))
      (μ ⊗ₘ categoricalKernel p (fun h i => (hp h i).le) hs hpm) := by
    apply joint_integrable_of_fiber_bound μ p (fun h i => (hp h i).le) hs hpm _
      (Finset.measurable_sum _ fun i _ =>
        (rawEstimate_measurable b ρ p hbm hρm hpm i).mul ((hpm i).comp measurable_fst)) (B + R)
    intro h
    change (∑ a, p h a * ‖HinfExpected.dot (rawEstimate b ρ p (h, a)) (p h)‖) ≤ B + R
    have hdot (a : ι) : 0 ≤ HinfExpected.dot (rawEstimate b ρ p (h, a)) (p h) :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (rawEstimate_nonneg b ρ p (fun h i => (hb h i).1)
          (fun h i => (hρ h i).1) hp (h, a) i) (hp h i).le
    have hnormdot (a : ι) : ‖HinfExpected.dot (rawEstimate b ρ p (h, a)) (p h)‖ =
        HinfExpected.dot (b h) (p h) + ρ h a := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hdot a), raw_dot_identity b ρ p hp h]
    simp_rw [hnormdot]
    have hbase : HinfExpected.dot (b h) (p h) ≤ B := by
      calc
        _ ≤ ∑ i, B * p h i := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hb h i).2 (hp h i).le
        _ = B := by rw [← Finset.mul_sum, hs, mul_one]
    calc
      _ ≤ ∑ a, p h a * (B + R) := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (by linarith [(hρ h a).2]) (hp h a).le
      _ = B + R := by rw [← Finset.sum_mul, hs, one_mul]
  exact hD.sub (rawEstimate_integrable μ b ρ p B R hp hs hpm hbm hρm hb hρ k)

theorem joint_comparison_mean (μ : Measure H) [IsProbabilityMeasure μ]
    (b ρ p : H → ι → ℝ) (B R : ℝ)
    (hp : ∀ h i, 0 < p h i) (hs : ∀ h, ∑ i, p h i = 1)
    (hpm : ∀ i, Measurable (fun h => p h i))
    (hbm : ∀ i, Measurable (fun h => b h i))
    (hρm : ∀ i, Measurable (fun h => ρ h i))
    (hb : ∀ h i, 0 ≤ b h i ∧ b h i ≤ B)
    (hρ : ∀ h i, 0 ≤ ρ h i ∧ ρ h i ≤ R) (k : ι) :
    (∫ z, fedComparison b ρ p k z
      ∂(μ ⊗ₘ categoricalKernel p (fun h i => (hp h i).le) hs hpm)) =
    ∫ z, physicalComparison b ρ k z
      ∂(μ ⊗ₘ categoricalKernel p (fun h i => (hp h i).le) hs hpm) := by
  rw [Measure.integral_compProd (fedComparison_integrable μ b ρ p B R hp hs hpm hbm hρm hb hρ k),
    Measure.integral_compProd (physicalComparison_integrable μ b ρ p B R hp hs hpm hbm hρm hb hρ k)]
  apply integral_congr_ae
  exact ae_of_all _ fun h => fedComparison_fiber_mean b ρ p hp hs hpm h k

section Pushforward

variable {Ω : Type*} [MeasurableSpace Ω]

theorem original_integrable (ν : Measure Ω) (μ : Measure (H × ι))
    (J : Ω → H × ι) (hJ : Measurable J) (hlaw : ν.map J = μ)
    (F : H × ι → ℝ) (hF : Integrable F μ) : Integrable (fun ω => F (J ω)) ν := by
  exact (show MeasurePreserving J ν μ from ⟨hJ, hlaw⟩).integrable_comp_of_integrable hF

theorem original_integral (ν : Measure Ω) (μ : Measure (H × ι))
    (J : Ω → H × ι) (hJ : Measurable J) (hlaw : ν.map J = μ)
    (F : H × ι → ℝ) (hF : Measurable F) :
    (∫ ω, F (J ω) ∂ν) = ∫ z, F z ∂μ := by
  rw [← hlaw, integral_map hJ.aemeasurable hF.aestronglyMeasurable]

end Pushforward

theorem dot_fixed_comparator (L p : ι → ℝ) (k : ι) :
    HinfExpected.dot L (fun i => p i - if i = k then 1 else 0) =
      HinfExpected.dot L p - L k := by
  simp [HinfExpected.dot, mul_sub, mul_ite, Finset.sum_sub_distrib]

section MainTheorem

variable {Ω : Type*} [MeasurableSpace Ω] [Nonempty ι] [StandardBorelSpace ι]

/-- The complete physical expected-regret inequality, for every deterministic
comparator. Stability is discharged by the genuine Tsallis Taylor/FTRL theorem.
Only primitive measurability, conditional categorical sampling, envelopes, and
the actual exact projection update occur among the premises. `Cbase` is solely
an integrability envelope; the rate uses the separate public span `B`. -/
theorem expected_physical_regret_le
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (history : ℕ → Ω → H) (A : ℕ → Ω → ι)
    (p b ρ : ℕ → H → ι → ℝ) (x : ℕ → Ω → ℝ) (m : ℕ → H → ℝ)
    (q η Cbase B R : ℝ) (T : ℕ)
    (hq : 1 < q) (hη : 0 < η) (hB : 0 ≤ B)
    (hH : ∀ t, Measurable (history t)) (hA : ∀ t, Measurable (A t))
    (hpm : ∀ t i, Measurable (fun h => p t h i))
    (hbm : ∀ t i, Measurable (fun h => b t h i))
    (hρm : ∀ t i, Measurable (fun h => ρ t h i))
    (hp : ∀ t h i, 0 < p t h i) (hs : ∀ t h, ∑ i, p t h i = 1)
    (hb : ∀ t h i, 0 ≤ b t h i ∧ b t h i ≤ Cbase)
    (hρ : ∀ t h i, 0 ≤ ρ t h i ∧ ρ t h i ≤ R)
    (hspan : ∀ t h i, m t h ≤ b t h i ∧ b t h i ≤ m t h + B)
    (hsample : ∀ t i, ν[((A t) ⁻¹' {i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace H).comap (history t)] =ᵐ[ν]
        fun ω => p t (history t ω) i)
    (hproj : ∀ ω t, HinfExpected.IsProjection q η
      (HinfExpected.cumulative
        (fun s => rawEstimate (b s) (ρ s) (p s) (history s ω, A s ω)) t)
      (p t (history t ω)) (x t ω)) (k : ι) :
    (∫ ω, ∑ t ∈ Finset.range T,
      physicalComparison (b t) (ρ t) k (history t ω, A t ω) ∂ν) ≤
      (q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)) / η +
        q * η * T * (2 * B ^ 2 + R ^ 2 * (Fintype.card ι : ℝ) ^ (1 - 1 / q)) := by
  let J : ℕ → Ω → H × ι := fun t ω => (history t ω, A t ω)
  let κ (t : ℕ) := categoricalKernel (p t) (fun h i => (hp t h i).le) (hs t) (hpm t)
  let μ (t : ℕ) := (ν.map (history t)) ⊗ₘ κ t
  have hJ (t : ℕ) : Measurable (J t) := (hH t).prodMk (hA t)
  have hmap (t : ℕ) : ν.map (J t) = μ t :=
    joint_law_of_conditional_sampling ν (history t) (A t) (hH t) (hA t)
      (p t) (fun h i => (hp t h i).le) (hs t) (hpm t) (hsample t)
  have hμ0 (t : ℕ) : IsProbabilityMeasure (ν.map (history t)) :=
    Measure.isProbabilityMeasure_map (hH t).aemeasurable
  have hFi (t : ℕ) : Integrable (fun ω => fedComparison (b t) (ρ t) (p t) k (J t ω)) ν := by
    letI := hμ0 t
    exact original_integrable ν (μ t) (J t) (hJ t) (hmap t) _
      (fedComparison_integrable (ν.map (history t)) (b t) (ρ t) (p t) Cbase R
        (hp t) (hs t) (hpm t) (hbm t) (hρm t) (hb t) (hρ t) k)
  have hPi (t : ℕ) : Integrable (fun ω => physicalComparison (b t) (ρ t) k (J t ω)) ν := by
    letI := hμ0 t
    exact original_integrable ν (μ t) (J t) (hJ t) (hmap t) _
      (physicalComparison_integrable (ν.map (history t)) (b t) (ρ t) (p t) Cbase R
        (hp t) (hs t) (hpm t) (hbm t) (hρm t) (hb t) (hρ t) k)
  let V : ℕ → Ω → ℝ := fun t ω =>
    HinfExpected.residualMoment q (p t (history t ω)) (ρ t (history t ω)) (A t ω)
  have hVi (t : ℕ) : Integrable (V t) ν := by
    letI := hμ0 t
    exact original_integrable ν (μ t) (J t) (hJ t) (hmap t) _
      (residualMoment_integrable (ν.map (history t)) q R (p t) (ρ t) hq (hp t)
        (hs t) (hpm t) (hρm t) (hρ t))
  have hVmean (t : ℕ) : (∫ ω, V t ω ∂ν) ≤
      R ^ 2 * (Fintype.card ι : ℝ) ^ (1 - 1 / q) := by
    letI := hμ0 t
    rw [show (∫ ω, V t ω ∂ν) = ∫ z, HinfExpected.residualMoment q (p t z.1) (ρ t z.1) z.2
        ∂μ t from original_integral ν (μ t) (J t) (hJ t) (hmap t) _
          (residualMoment_measurable q hq (p t) (ρ t) (hpm t) (hρm t))]
    exact integral_residualMoment_le (ν.map (history t)) q R (p t) (ρ t) hq
      (hp t) (hs t) (hpm t) (hρm t) (hρ t)
  have hmean (t : ℕ) :
      (∫ ω, physicalComparison (b t) (ρ t) k (J t ω) ∂ν) =
      ∫ ω, fedComparison (b t) (ρ t) (p t) k (J t ω) ∂ν := by
    letI := hμ0 t
    rw [original_integral ν (μ t) (J t) (hJ t) (hmap t) _
        (physicalComparison_measurable (b t) (ρ t) (hbm t) (hρm t) k),
      original_integral ν (μ t) (J t) (hJ t) (hmap t) _
        (fedComparison_measurable (b t) (ρ t) (p t) (hbm t) (hρm t) (hpm t) k)]
    exact (joint_comparison_mean (ν.map (history t)) (b t) (ρ t) (p t) Cbase R
      (hp t) (hs t) (hpm t) (hbm t) (hρm t) (hb t) (hρ t) k).symm
  let RF : ℝ := q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)
  have hpath (ω : Ω) : (∑ t ∈ Finset.range T, fedComparison (b t) (ρ t) (p t) k (J t ω)) ≤
      RF / η + q * η * ∑ t ∈ Finset.range T, (2 * B ^ 2 + V t ω) := by
    have hL (t : ℕ) (i : ι) : rawEstimate (b t) (ρ t) (p t) (J t ω) i =
        HinfExpected.composite (b t (history t ω))
          (ρ t (history t ω) (A t ω) / p t (history t ω) (A t ω)) (A t ω) i := by
      by_cases hi : A t ω = i
      · subst i; simp [rawEstimate, HinfExpected.composite, J]
      · simp [rawEstimate, HinfExpected.composite, J, hi, Ne.symm hi]
    have hdet := HinfStability.ftrl_hybrid_regret_le_span q η
      (fun t => rawEstimate (b t) (ρ t) (p t) (J t ω))
      (fun t => p t (history t ω)) (fun t => b t (history t ω))
      (fun t => ρ t (history t ω)) (fun t => x t ω) (fun _ => B)
      (fun t => m t (history t ω)) (fun t => A t ω) hq hη (hproj ω) hL
      (fun _ => hB) (fun t i => (hρ t (history t ω) i).1)
      (fun t i => hspan t (history t ω) i)
      (fun i => if i = k then 1 else 0) (fun i => by dsimp only; split_ifs <;> positivity)
      (by simp) T
    simpa only [dot_fixed_comparator, fedComparison, RF, V, J] using hdet
  have hsumF : Integrable (fun ω => ∑ t ∈ Finset.range T,
      fedComparison (b t) (ρ t) (p t) k (J t ω)) ν :=
    integrable_finset_sum _ fun t _ => hFi t
  have hsumV : Integrable (fun ω => ∑ t ∈ Finset.range T, (2 * B ^ 2 + V t ω)) ν :=
    integrable_finset_sum _ fun t _ => (integrable_const _).add (hVi t)
  have hi := integral_mono hsumF ((integrable_const (RF / η)).add (hsumV.const_mul (q * η))) hpath
  change (∫ ω, ∑ t ∈ Finset.range T, fedComparison (b t) (ρ t) (p t) k (J t ω) ∂ν) ≤
    ∫ ω, RF / η + q * η * ∑ t ∈ Finset.range T, (2 * B ^ 2 + V t ω) ∂ν at hi
  have hstepIntegral (t : ℕ) : (∫ ω, 2 * B ^ 2 + V t ω ∂ν) =
      2 * B ^ 2 + ∫ ω, V t ω ∂ν := by
    rw [integral_add (integrable_const _) (hVi t)]
    simp
  have hsumIntegral : (∫ ω, ∑ t ∈ Finset.range T, (2 * B ^ 2 + V t ω) ∂ν) =
      ∑ t ∈ Finset.range T, ∫ ω, 2 * B ^ 2 + V t ω ∂ν :=
    integral_finset_sum (Finset.range T) (f := fun t ω => 2 * B ^ 2 + V t ω)
      (fun t _ => (integrable_const _).add (hVi t))
  rw [integral_add (integrable_const _) (hsumV.const_mul (q * η)),
    integral_const_mul, hsumIntegral] at hi
  simp only [integral_const, measureReal_univ_eq_one, one_smul, hstepIntegral] at hi
  have hqη : 0 ≤ q * η := mul_nonneg (lt_trans zero_lt_one hq).le hη.le
  calc
    _ = ∑ t ∈ Finset.range T, ∫ ω, physicalComparison (b t) (ρ t) k (J t ω) ∂ν :=
      integral_finset_sum _ fun t _ => hPi t
    _ = ∑ t ∈ Finset.range T, ∫ ω, fedComparison (b t) (ρ t) (p t) k (J t ω) ∂ν := by
      apply Finset.sum_congr rfl
      intro t _
      exact hmean t
    _ = ∫ ω, ∑ t ∈ Finset.range T, fedComparison (b t) (ρ t) (p t) k (J t ω) ∂ν :=
      (integral_finset_sum _ fun t _ => hFi t).symm
    _ ≤ RF / η + q * η * ∑ t ∈ Finset.range T, (2 * B ^ 2 + ∫ ω, V t ω ∂ν) := by
      exact hi
    _ ≤ RF / η + q * η * ∑ _t ∈ Finset.range T,
        (2 * B ^ 2 + R ^ 2 * (Fintype.card ι : ℝ) ^ (1 - 1 / q)) := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left _ hqη
      exact Finset.sum_le_sum fun t _ => add_le_add_left (hVmean t) _
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, RF]; ring

/-- Refined P/V expected bound retaining every realized span-square and the exact
conditional residual second moment. No stability bound is a premise. The
finite public/residual envelopes below supply L1 only; they do not replace P or V
in the conclusion. The original normalized physical model implies envelopes 1. -/
theorem expected_physical_regret_le_refined
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (history : ℕ → Ω → H) (A : ℕ → Ω → ι)
    (p b ρ : ℕ → H → ι → ℝ) (x : ℕ → Ω → ℝ) (m : ℕ → H → ℝ)
    (q η Cbase R : ℝ) (B : ℕ → H → ℝ) (T : ℕ)
    (hq : 1 < q) (hη : 0 < η) (hB : ∀ t h, 0 ≤ B t h)
    (hB2i : ∀ t, Integrable (fun ω => (B t (history t ω)) ^ 2) ν)
    (hH : ∀ t, Measurable (history t)) (hA : ∀ t, Measurable (A t))
    (hpm : ∀ t i, Measurable (fun h => p t h i))
    (hbm : ∀ t i, Measurable (fun h => b t h i))
    (hρm : ∀ t i, Measurable (fun h => ρ t h i))
    (hp : ∀ t h i, 0 < p t h i) (hs : ∀ t h, ∑ i, p t h i = 1)
    (hb : ∀ t h i, 0 ≤ b t h i ∧ b t h i ≤ Cbase)
    (hρ : ∀ t h i, 0 ≤ ρ t h i ∧ ρ t h i ≤ R)
    (hspan : ∀ t h i, m t h ≤ b t h i ∧ b t h i ≤ m t h + B t h)
    (hsample : ∀ t i, ν[((A t) ⁻¹' {i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace H).comap (history t)] =ᵐ[ν]
        fun ω => p t (history t ω) i)
    (hproj : ∀ ω t, HinfExpected.IsProjection q η
      (HinfExpected.cumulative
        (fun s => rawEstimate (b s) (ρ s) (p s) (history s ω, A s ω)) t)
      (p t (history t ω)) (x t ω)) (k : ι) :
    (∫ ω, ∑ t ∈ Finset.range T,
      physicalComparison (b t) (ρ t) k (history t ω, A t ω) ∂ν) ≤
      (q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)) / η +
        q * η * (2 * (∑ t ∈ Finset.range T, ∫ ω, (B t (history t ω)) ^ 2 ∂ν) +
          ∑ t ∈ Finset.range T, ∫ ω, ∑ i,
            (p t (history t ω) i) ^ (1 / q) * (ρ t (history t ω) i) ^ 2 ∂ν) := by
  let J : ℕ → Ω → H × ι := fun t ω => (history t ω, A t ω)
  let κ (t : ℕ) := categoricalKernel (p t) (fun h i => (hp t h i).le) (hs t) (hpm t)
  let μ (t : ℕ) := (ν.map (history t)) ⊗ₘ κ t
  have hJ (t : ℕ) : Measurable (J t) := (hH t).prodMk (hA t)
  have hmap (t : ℕ) : ν.map (J t) = μ t :=
    joint_law_of_conditional_sampling ν (history t) (A t) (hH t) (hA t)
      (p t) (fun h i => (hp t h i).le) (hs t) (hpm t) (hsample t)
  have hμ0 (t : ℕ) : IsProbabilityMeasure (ν.map (history t)) :=
    Measure.isProbabilityMeasure_map (hH t).aemeasurable
  have hFi (t : ℕ) : Integrable (fun ω => fedComparison (b t) (ρ t) (p t) k (J t ω)) ν := by
    letI := hμ0 t
    exact original_integrable ν (μ t) (J t) (hJ t) (hmap t) _
      (fedComparison_integrable (ν.map (history t)) (b t) (ρ t) (p t) Cbase R
        (hp t) (hs t) (hpm t) (hbm t) (hρm t) (hb t) (hρ t) k)
  have hPi (t : ℕ) : Integrable (fun ω => physicalComparison (b t) (ρ t) k (J t ω)) ν := by
    letI := hμ0 t
    exact original_integrable ν (μ t) (J t) (hJ t) (hmap t) _
      (physicalComparison_integrable (ν.map (history t)) (b t) (ρ t) (p t) Cbase R
        (hp t) (hs t) (hpm t) (hbm t) (hρm t) (hb t) (hρ t) k)
  let V : ℕ → Ω → ℝ := fun t ω =>
    HinfExpected.residualMoment q (p t (history t ω)) (ρ t (history t ω)) (A t ω)
  have hVi (t : ℕ) : Integrable (V t) ν := by
    letI := hμ0 t
    exact original_integrable ν (μ t) (J t) (hJ t) (hmap t) _
      (residualMoment_integrable (ν.map (history t)) q R (p t) (ρ t) hq (hp t)
        (hs t) (hpm t) (hρm t) (hρ t))
  have hVexact (t : ℕ) : (∫ ω, V t ω ∂ν) =
      ∫ ω, ∑ i, (p t (history t ω) i) ^ (1 / q) *
        (ρ t (history t ω) i) ^ 2 ∂ν := by
    letI := hμ0 t
    have hM : Measurable (fun h => ∑ i, (p t h i) ^ (1 / q) * (ρ t h i) ^ 2) :=
      Finset.measurable_sum _ fun i _ =>
        ((Real.continuous_rpow_const (one_div_pos.mpr (lt_trans zero_lt_one hq)).le).measurable.comp
          (hpm t i)).mul ((hρm t i).pow_const 2)
    rw [show (∫ ω, V t ω ∂ν) = ∫ z, HinfExpected.residualMoment q (p t z.1) (ρ t z.1) z.2
        ∂μ t from original_integral ν (μ t) (J t) (hJ t) (hmap t) _
          (residualMoment_measurable q hq (p t) (ρ t) (hpm t) (hρm t))]
    rw [integral_residualMoment_eq (ν.map (history t)) q R (p t) (ρ t) hq
      (hp t) (hs t) (hpm t) (hρm t) (hρ t)]
    exact integral_map (hH t).aemeasurable hM.aestronglyMeasurable
  have hmean (t : ℕ) :
      (∫ ω, physicalComparison (b t) (ρ t) k (J t ω) ∂ν) =
      ∫ ω, fedComparison (b t) (ρ t) (p t) k (J t ω) ∂ν := by
    letI := hμ0 t
    rw [original_integral ν (μ t) (J t) (hJ t) (hmap t) _
        (physicalComparison_measurable (b t) (ρ t) (hbm t) (hρm t) k),
      original_integral ν (μ t) (J t) (hJ t) (hmap t) _
        (fedComparison_measurable (b t) (ρ t) (p t) (hbm t) (hρm t) (hpm t) k)]
    exact (joint_comparison_mean (ν.map (history t)) (b t) (ρ t) (p t) Cbase R
      (hp t) (hs t) (hpm t) (hbm t) (hρm t) (hb t) (hρ t) k).symm
  let RF : ℝ := q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)
  have hpath (ω : Ω) : (∑ t ∈ Finset.range T, fedComparison (b t) (ρ t) (p t) k (J t ω)) ≤
      RF / η + q * η * ∑ t ∈ Finset.range T, (2 * (B t (history t ω)) ^ 2 + V t ω) := by
    have hL (t : ℕ) (i : ι) : rawEstimate (b t) (ρ t) (p t) (J t ω) i =
        HinfExpected.composite (b t (history t ω))
          (ρ t (history t ω) (A t ω) / p t (history t ω) (A t ω)) (A t ω) i := by
      by_cases hi : A t ω = i
      · subst i; simp [rawEstimate, HinfExpected.composite, J]
      · simp [rawEstimate, HinfExpected.composite, J, hi, Ne.symm hi]
    have hdet := HinfStability.ftrl_hybrid_regret_le_span q η
      (fun t => rawEstimate (b t) (ρ t) (p t) (J t ω))
      (fun t => p t (history t ω)) (fun t => b t (history t ω))
      (fun t => ρ t (history t ω)) (fun t => x t ω) (fun t => B t (history t ω))
      (fun t => m t (history t ω)) (fun t => A t ω) hq hη (hproj ω) hL
      (fun t => hB t (history t ω)) (fun t i => (hρ t (history t ω) i).1)
      (fun t i => hspan t (history t ω) i)
      (fun i => if i = k then 1 else 0) (fun i => by dsimp only; split_ifs <;> positivity)
      (by simp) T
    simpa only [dot_fixed_comparator, fedComparison, RF, V, J] using hdet
  have hsumF : Integrable (fun ω => ∑ t ∈ Finset.range T,
      fedComparison (b t) (ρ t) (p t) k (J t ω)) ν :=
    integrable_finset_sum _ fun t _ => hFi t
  let G : ℕ → Ω → ℝ := fun t ω => 2 * (B t (history t ω)) ^ 2 + V t ω
  have hGi (t : ℕ) : Integrable (G t) ν := ((hB2i t).const_mul 2).add (hVi t)
  have hsumG : Integrable (fun ω => ∑ t ∈ Finset.range T, G t ω) ν :=
    integrable_finset_sum _ fun t _ => hGi t
  have hi := integral_mono hsumF ((integrable_const (RF / η)).add (hsumG.const_mul (q * η))) hpath
  change (∫ ω, ∑ t ∈ Finset.range T, fedComparison (b t) (ρ t) (p t) k (J t ω) ∂ν) ≤
    ∫ ω, RF / η + q * η * ∑ t ∈ Finset.range T, G t ω ∂ν at hi
  have hsumIntegral : (∫ ω, ∑ t ∈ Finset.range T, G t ω ∂ν) =
      ∑ t ∈ Finset.range T, ∫ ω, G t ω ∂ν :=
    integral_finset_sum _ (fun t _ => hGi t)
  have hstepIntegral (t : ℕ) : (∫ ω, G t ω ∂ν) =
      2 * (∫ ω, (B t (history t ω)) ^ 2 ∂ν) + ∫ ω, V t ω ∂ν := by
    unfold G
    rw [integral_add ((hB2i t).const_mul 2) (hVi t), integral_const_mul]
  rw [integral_add (integrable_const _) (hsumG.const_mul (q * η)),
    integral_const_mul, hsumIntegral] at hi
  simp only [integral_const, measureReal_univ_eq_one, one_smul, hstepIntegral] at hi
  calc
    _ = ∑ t ∈ Finset.range T, ∫ ω, physicalComparison (b t) (ρ t) k (J t ω) ∂ν :=
      integral_finset_sum _ fun t _ => hPi t
    _ = ∑ t ∈ Finset.range T, ∫ ω, fedComparison (b t) (ρ t) (p t) k (J t ω) ∂ν := by
      apply Finset.sum_congr rfl
      intro t _
      exact hmean t
    _ = ∫ ω, ∑ t ∈ Finset.range T, fedComparison (b t) (ρ t) (p t) k (J t ω) ∂ν :=
      (integral_finset_sum _ fun t _ => hFi t).symm
    _ ≤ RF / η + q * η * ∑ t ∈ Finset.range T,
        (2 * (∫ ω, (B t (history t ω)) ^ 2 ∂ν) + ∫ ω, V t ω ∂ν) := hi
    _ = _ := by
      simp_rw [hVexact]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]


end MainTheorem

section CanonicalTarget

variable {Ω : Type*} [MeasurableSpace Ω] [Nonempty ι] [StandardBorelSpace ι]

theorem integrable_abs_bounded (ν : Measure Ω) [IsFiniteMeasure ν]
    (f : Ω → ℝ) (hm : Measurable f) (C : ℝ) (hb : ∀ ω, |f ω| ≤ C) :
    Integrable f ν :=
  (integrable_const C).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

/-- Canonical Theorem 1, including its precise additive quantization budget.
The raw estimator is unbiased for d=ell+delta, and this theorem explicitly
converts the physical bound to the quantized learn-loss target. -/
theorem canonical_expected_regret_le
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (history : ℕ → Ω → H) (A : ℕ → Ω → ι)
    (p b ρ ell δ : ℕ → H → ι → ℝ) (x : ℕ → Ω → ℝ)
    (q η ε : ℝ) (T : ℕ) (hq : 1 < q) (hη : 0 < η) (hε : 0 ≤ ε)
    (hH : ∀ t, Measurable (history t)) (hA : ∀ t, Measurable (A t))
    (hpm : ∀ t i, Measurable (fun h => p t h i))
    (hbm : ∀ t i, Measurable (fun h => b t h i))
    (hρm : ∀ t i, Measurable (fun h => ρ t h i))
    (hellm : ∀ t i, Measurable (fun h => ell t h i))
    (hp : ∀ t h i, 0 < p t h i) (hs : ∀ t h, ∑ i, p t h i = 1)
    (hb : ∀ t h i, 0 ≤ b t h i ∧ b t h i ≤ 1)
    (hρ : ∀ t h i, 0 ≤ ρ t h i ∧ ρ t h i ≤ 1)
    (hδ : ∀ t h i, |δ t h i| ≤ ε)
    (hsplit : ∀ t h i, b t h i + ρ t h i = ell t h i + δ t h i)
    (hsample : ∀ t i, ν[((A t) ⁻¹' {i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace H).comap (history t)] =ᵐ[ν]
        fun ω => p t (history t ω) i)
    (hproj : ∀ ω t, HinfExpected.IsProjection q η
      (HinfExpected.cumulative
        (fun s => rawEstimate (b s) (ρ s) (p s) (history s ω, A s ω)) t)
      (p t (history t ω)) (x t ω)) (k : ι) :
    (∫ ω, ∑ t ∈ Finset.range T,
      (ell t (history t ω) (A t ω) - ell t (history t ω) k) ∂ν) ≤
      (q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)) / η +
        q * η * T * (2 + (Fintype.card ι : ℝ) ^ (1 - 1 / q)) + 2 * T * ε := by
  have hphysical := expected_physical_regret_le ν history A p b ρ x (fun _ _ => 0)
    q η 1 1 1 T hq hη zero_le_one hH hA hpm hbm hρm hp hs hb hρ
    (fun t h i => by simpa using hb t h i) hsample hproj k
  have hellbounds (t : ℕ) (h : H) (i : ι) : -ε ≤ ell t h i ∧ ell t h i ≤ 2 + ε := by
    have hδi := abs_le.mp (hδ t h i)
    constructor <;> linarith [(hb t h i).1, (hb t h i).2, (hρ t h i).1,
      (hρ t h i).2, hsplit t h i]
  have hellprod (t : ℕ) : Measurable (fun z : H × ι => ell t z.1 z.2) :=
    measurable_from_prod_countable_left (fun i => hellm t i)
  have hli (t : ℕ) : Integrable (fun ω => ell t (history t ω) (A t ω) -
      ell t (history t ω) k) ν := by
    apply integrable_abs_bounded ν _
      (((hellprod t).comp ((hH t).prodMk (hA t))).sub
        ((hellm t k).comp (hH t))) (2 + 2 * ε)
    intro ω
    change |ell t (history t ω) (A t ω) - ell t (history t ω) k| ≤ 2 + 2 * ε
    rw [abs_le]
    constructor <;> linarith [(hellbounds t (history t ω) (A t ω)).1,
      (hellbounds t (history t ω) (A t ω)).2, (hellbounds t (history t ω) k).1,
      (hellbounds t (history t ω) k).2]
  have hpi (t : ℕ) : Integrable (fun ω =>
      physicalComparison (b t) (ρ t) k (history t ω, A t ω)) ν := by
    apply integrable_abs_bounded ν _
      ((physicalComparison_measurable (b t) (ρ t) (hbm t) (hρm t) k).comp
        ((hH t).prodMk (hA t))) 2
    intro ω
    change |(b t (history t ω) (A t ω) + ρ t (history t ω) (A t ω)) -
      (b t (history t ω) k + ρ t (history t ω) k)| ≤ 2
    rw [abs_le]
    constructor <;> linarith [(hb t (history t ω) (A t ω)).1,
      (hb t (history t ω) (A t ω)).2, (hρ t (history t ω) (A t ω)).1,
      (hρ t (history t ω) (A t ω)).2, (hb t (history t ω) k).1,
      (hb t (history t ω) k).2, (hρ t (history t ω) k).1, (hρ t (history t ω) k).2]
  have hlocal (t : ℕ) (ω : Ω) :
      ell t (history t ω) (A t ω) - ell t (history t ω) k ≤
      physicalComparison (b t) (ρ t) k (history t ω, A t ω) + 2 * ε := by
    unfold physicalComparison
    have hδa := abs_le.mp (hδ t (history t ω) (A t ω))
    have hδk := abs_le.mp (hδ t (history t ω) k)
    linarith [hsplit t (history t ω) (A t ω), hsplit t (history t ω) k]
  have hsumli := integrable_finset_sum (Finset.range T) (fun t _ => hli t)
  have hsumpi := integrable_finset_sum (Finset.range T) (fun t _ => hpi t)
  have hdom (ω : Ω) : (∑ t ∈ Finset.range T,
      (ell t (history t ω) (A t ω) - ell t (history t ω) k)) ≤
      (∑ t ∈ Finset.range T, physicalComparison (b t) (ρ t) k (history t ω, A t ω)) +
      2 * T * ε := by
    calc
      _ ≤ ∑ t ∈ Finset.range T,
          (physicalComparison (b t) (ρ t) k (history t ω, A t ω) + 2 * ε) :=
        Finset.sum_le_sum fun t _ => hlocal t ω
      _ = _ := by rw [Finset.sum_add_distrib]; simp only [Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]; ring
  have hi := integral_mono hsumli (hsumpi.add (integrable_const (2 * T * ε))) hdom
  change (∫ ω, ∑ t ∈ Finset.range T,
    (ell t (history t ω) (A t ω) - ell t (history t ω) k) ∂ν) ≤
    ∫ ω, (∑ t ∈ Finset.range T,
      physicalComparison (b t) (ρ t) k (history t ω, A t ω)) + 2 * T * ε ∂ν at hi
  rw [integral_add hsumpi (integrable_const _)] at hi
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hi
  have hphysical' : (∫ ω, ∑ t ∈ Finset.range T,
      physicalComparison (b t) (ρ t) k (history t ω, A t ω) ∂ν) ≤
      (q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)) / η +
        q * η * T * (2 + (Fintype.card ι : ℝ) ^ (1 - 1 / q)) := by
    simpa only [one_pow, mul_one, one_mul] using hphysical
  exact hi.trans (add_le_add_right hphysical' _)

/-- Comparator maximization is outside expectation. This helper does not
claim a bound on the expectation of realized hindsight regret. -/
def pseudoRegret (ν : Measure Ω) (comparison : ι → Ω → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k => ∫ ω, comparison k ω ∂ν)

theorem pseudoRegret_le (ν : Measure Ω) (comparison : ι → Ω → ℝ) (U : ℝ)
    (h : ∀ k, (∫ ω, comparison k ω ∂ν) ≤ U) : pseudoRegret ν comparison ≤ U := by
  unfold pseudoRegret
  exact Finset.sup'_le Finset.univ_nonempty _ (fun k _ => h k)

theorem pseudoRegret_eq_expected_sub_min (ν : Measure Ω)
    (played : Ω → ℝ) (fixed : ι → Ω → ℝ)
    (hplayed : Integrable played ν) (hfixed : ∀ k, Integrable (fixed k) ν) :
    pseudoRegret ν (fun k ω => played ω - fixed k ω) =
      (∫ ω, played ω ∂ν) - Finset.univ.inf' Finset.univ_nonempty
        (fun k => ∫ ω, fixed k ω ∂ν) := by
  unfold pseudoRegret
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro k _
    rw [integral_sub hplayed (hfixed k)]
    linarith [Finset.inf'_le (fun j => ∫ ω, fixed j ω ∂ν) (Finset.mem_univ k)]
  · obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun k => ∫ ω, fixed k ω ∂ν)
    have h := Finset.le_sup' (fun j => ∫ ω, played ω - fixed j ω ∂ν) (Finset.mem_univ k)
    rw [integral_sub hplayed (hfixed k)] at h
    rw [hk]
    exact h

/-- Canonical fixed-learning-rate pseudo-regret with the comparator maximum
outside expectation and the complete base and quantization terms. -/
theorem canonical_expected_pseudo_regret_le
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (history : ℕ → Ω → H) (A : ℕ → Ω → ι)
    (p b ρ ell δ : ℕ → H → ι → ℝ) (x : ℕ → Ω → ℝ)
    (q η ε : ℝ) (T : ℕ) (hq : 1 < q) (hη : 0 < η) (hε : 0 ≤ ε)
    (hH : ∀ t, Measurable (history t)) (hA : ∀ t, Measurable (A t))
    (hpm : ∀ t i, Measurable (fun h => p t h i))
    (hbm : ∀ t i, Measurable (fun h => b t h i))
    (hρm : ∀ t i, Measurable (fun h => ρ t h i))
    (hellm : ∀ t i, Measurable (fun h => ell t h i))
    (hp : ∀ t h i, 0 < p t h i) (hs : ∀ t h, ∑ i, p t h i = 1)
    (hb : ∀ t h i, 0 ≤ b t h i ∧ b t h i ≤ 1)
    (hρ : ∀ t h i, 0 ≤ ρ t h i ∧ ρ t h i ≤ 1)
    (hδ : ∀ t h i, |δ t h i| ≤ ε)
    (hsplit : ∀ t h i, b t h i + ρ t h i = ell t h i + δ t h i)
    (hsample : ∀ t i, ν[((A t) ⁻¹' {i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace H).comap (history t)] =ᵐ[ν]
        fun ω => p t (history t ω) i)
    (hproj : ∀ ω t, HinfExpected.IsProjection q η
      (HinfExpected.cumulative
        (fun s => rawEstimate (b s) (ρ s) (p s) (history s ω, A s ω)) t)
      (p t (history t ω)) (x t ω)) :
    pseudoRegret ν (fun k ω => ∑ t ∈ Finset.range T,
      (ell t (history t ω) (A t ω) - ell t (history t ω) k)) ≤
      (q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)) / η +
        q * η * T * (2 + (Fintype.card ι : ℝ) ^ (1 - 1 / q)) + 2 * T * ε := by
  apply pseudoRegret_le
  intro k
  exact canonical_expected_regret_le ν history A p b ρ ell δ x q η ε T hq hη hε
    hH hA hpm hbm hρm hellm hp hs hb hρ hδ hsplit hsample hproj k

end CanonicalTarget

section NormalizedV3

variable {Ω : Type*} [MeasurableSpace Ω] [Nonempty ι] [StandardBorelSpace ι]

def publicMin (b : ι → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty b
def publicMax (b : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty b
def publicSpan (b : ι → ℝ) : ℝ := publicMax b - publicMin b

theorem public_interval (b : ι → ℝ) (i : ι) :
    publicMin b ≤ b i ∧ b i ≤ publicMin b + publicSpan b := by
  constructor
  · exact Finset.inf'_le b (Finset.mem_univ i)
  · have h : b i ≤ publicMax b := Finset.le_sup' b (Finset.mem_univ i)
    change b i ≤ publicMin b + (publicMax b - publicMin b)
    linarith

theorem publicSpan_bounds (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    0 ≤ publicSpan b ∧ publicSpan b ≤ 1 := by
  have hlo : 0 ≤ publicMin b := Finset.le_inf' Finset.univ_nonempty b (fun i _ => (hb i).1)
  have hhi : publicMax b ≤ 1 := Finset.sup'_le Finset.univ_nonempty b (fun i _ => (hb i).2)
  let i : ι := Classical.choice inferInstance
  have hmi : publicMin b ≤ b i := Finset.inf'_le b (Finset.mem_univ i)
  have hma : b i ≤ publicMax b := Finset.le_sup' b (Finset.mem_univ i)
  unfold publicSpan
  constructor <;> linarith

theorem publicSpan_measurable (b : H → ι → ℝ) (hb : ∀ i, Measurable (fun h => b h i)) :
    Measurable (fun h => publicSpan (b h)) := by
  have hmax : Measurable (fun h => publicMax (b h)) := by
    change Measurable (fun h => Finset.univ.sup' Finset.univ_nonempty (b h))
    convert (Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hb i)) using 1
    funext h
    rw [Finset.sup'_apply]
  have hmin : Measurable (fun h => publicMin (b h)) := by
    have heq : (fun h => publicMin (b h)) =
        Finset.univ.inf' Finset.univ_nonempty (fun i h => b h i) := by
      funext h
      rw [Finset.inf'_apply]
      rfl
    rw [heq]
    exact Finset.measurable_sup' (α := ℝᵒᵈ) Finset.univ_nonempty
      (f := fun i h => (b h i : ℝᵒᵈ)) (fun i _ => hb i)
  exact hmax.sub hmin

/-- v3's refined expected inequality with the actual random public spans and
the expectation-outside-max comparator. The original normalized physical
envelopes imply all temporary uniform L1 bounds and span-square integrability.
No uniform R/B is substituted for the exact P/V terms in this conclusion. -/
theorem v3_expected_pseudo_regret_le_refined
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (history : ℕ → Ω → H) (A : ℕ → Ω → ι)
    (p b ρ d : ℕ → H → ι → ℝ) (x : ℕ → Ω → ℝ)
    (q η : ℝ) (T : ℕ) (hq : 1 < q) (hη : 0 < η)
    (hH : ∀ t, Measurable (history t)) (hA : ∀ t, Measurable (A t))
    (hpm : ∀ t i, Measurable (fun h => p t h i))
    (hbm : ∀ t i, Measurable (fun h => b t h i))
    (hρm : ∀ t i, Measurable (fun h => ρ t h i))
    (hp : ∀ t h i, 0 < p t h i) (hs : ∀ t h, ∑ i, p t h i = 1)
    (hb0 : ∀ t h i, 0 ≤ b t h i) (hρ0 : ∀ t h i, 0 ≤ ρ t h i)
    (hd : ∀ t h i, d t h i = b t h i + ρ t h i) (hd1 : ∀ t h i, d t h i ≤ 1)
    (hsample : ∀ t i, ν[((A t) ⁻¹' {i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace H).comap (history t)] =ᵐ[ν]
        fun ω => p t (history t ω) i)
    (hproj : ∀ ω t, HinfExpected.IsProjection q η
      (HinfExpected.cumulative
        (fun s => rawEstimate (b s) (ρ s) (p s) (history s ω, A s ω)) t)
      (p t (history t ω)) (x t ω)) :
    pseudoRegret ν (fun k ω => ∑ t ∈ Finset.range T,
      (d t (history t ω) (A t ω) - d t (history t ω) k)) ≤
      (q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)) / η +
        q * η * (2 * (∑ t ∈ Finset.range T,
          ∫ ω, (publicSpan (b t (history t ω))) ^ 2 ∂ν) +
          ∑ t ∈ Finset.range T, ∫ ω, ∑ i,
            (p t (history t ω) i) ^ (1 / q) * (ρ t (history t ω) i) ^ 2 ∂ν) := by
  have hb (t : ℕ) (h : H) (i : ι) : 0 ≤ b t h i ∧ b t h i ≤ 1 := by
    constructor
    · exact hb0 t h i
    · linarith [hd t h i, hd1 t h i, hρ0 t h i]
  have hρ (t : ℕ) (h : H) (i : ι) : 0 ≤ ρ t h i ∧ ρ t h i ≤ 1 := by
    constructor
    · exact hρ0 t h i
    · linarith [hd t h i, hd1 t h i, hb0 t h i]
  have hB2i (t : ℕ) : Integrable (fun ω => (publicSpan (b t (history t ω))) ^ 2) ν := by
    apply integrable_abs_bounded ν _
      (((publicSpan_measurable (b t) (hbm t)).comp (hH t)).pow_const 2) 1
    intro ω
    have hs := publicSpan_bounds (b t (history t ω)) (hb t (history t ω))
    change |(publicSpan (b t (history t ω))) ^ 2| ≤ 1
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  apply pseudoRegret_le
  intro k
  have hfixed := expected_physical_regret_le_refined ν history A p b ρ x
    (fun t h => publicMin (b t h)) q η 1 1 (fun t h => publicSpan (b t h)) T hq hη
    (fun t h => (publicSpan_bounds (b t h) (hb t h)).1) hB2i
    hH hA hpm hbm hρm hp hs hb hρ (fun t h i => public_interval (b t h) i)
    hsample hproj k
  simpa only [hd, physicalComparison] using hfixed

/-- The same refined bound in the paper's literal E[cumulative played cost]
minus min_k E[cumulative fixed-arm cost] form. -/
theorem v3_expected_regret_le_refined
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (history : ℕ → Ω → H) (A : ℕ → Ω → ι)
    (p b ρ d : ℕ → H → ι → ℝ) (x : ℕ → Ω → ℝ)
    (q η : ℝ) (T : ℕ) (hq : 1 < q) (hη : 0 < η)
    (hH : ∀ t, Measurable (history t)) (hA : ∀ t, Measurable (A t))
    (hpm : ∀ t i, Measurable (fun h => p t h i))
    (hbm : ∀ t i, Measurable (fun h => b t h i))
    (hρm : ∀ t i, Measurable (fun h => ρ t h i))
    (hp : ∀ t h i, 0 < p t h i) (hs : ∀ t h, ∑ i, p t h i = 1)
    (hb0 : ∀ t h i, 0 ≤ b t h i) (hρ0 : ∀ t h i, 0 ≤ ρ t h i)
    (hd : ∀ t h i, d t h i = b t h i + ρ t h i) (hd1 : ∀ t h i, d t h i ≤ 1)
    (hsample : ∀ t i, ν[((A t) ⁻¹' {i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace H).comap (history t)] =ᵐ[ν]
        fun ω => p t (history t ω) i)
    (hproj : ∀ ω t, HinfExpected.IsProjection q η
      (HinfExpected.cumulative
        (fun s => rawEstimate (b s) (ρ s) (p s) (history s ω, A s ω)) t)
      (p t (history t ω)) (x t ω)) :
    (∫ ω, ∑ t ∈ Finset.range T, d t (history t ω) (A t ω) ∂ν) -
      Finset.univ.inf' Finset.univ_nonempty
        (fun k => ∫ ω, ∑ t ∈ Finset.range T, d t (history t ω) k ∂ν) ≤
      (q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)) / η +
        q * η * (2 * (∑ t ∈ Finset.range T,
          ∫ ω, (publicSpan (b t (history t ω))) ^ 2 ∂ν) +
          ∑ t ∈ Finset.range T, ∫ ω, ∑ i,
            (p t (history t ω) i) ^ (1 / q) * (ρ t (history t ω) i) ^ 2 ∂ν) := by
  have hmain := v3_expected_pseudo_regret_le_refined ν history A p b ρ d x q η T hq hη
    hH hA hpm hbm hρm hp hs hb0 hρ0 hd hd1 hsample hproj
  have hdm (t : ℕ) (i : ι) : Measurable (fun h => d t h i) := by
    simpa only [hd] using (hbm t i).add (hρm t i)
  have hdp (t : ℕ) : Measurable (fun z : H × ι => d t z.1 z.2) :=
    measurable_from_prod_countable_left (fun i => hdm t i)
  have hd0 (t : ℕ) (h : H) (i : ι) : 0 ≤ d t h i := by
    rw [hd]
    exact add_nonneg (hb0 t h i) (hρ0 t h i)
  have hplayed (t : ℕ) : Integrable (fun ω => d t (history t ω) (A t ω)) ν := by
    apply integrable_abs_bounded ν _
      ((hdp t).comp ((hH t).prodMk (hA t))) 1
    intro ω
    change |d t (history t ω) (A t ω)| ≤ 1
    rw [abs_of_nonneg (hd0 t (history t ω) (A t ω))]
    exact hd1 t (history t ω) (A t ω)
  have hfixed (t : ℕ) (k : ι) : Integrable (fun ω => d t (history t ω) k) ν := by
    apply integrable_abs_bounded ν _ ((hdm t k).comp (hH t)) 1
    intro ω
    change |d t (history t ω) k| ≤ 1
    rw [abs_of_nonneg (hd0 t (history t ω) k)]
    exact hd1 t (history t ω) k
  have hid := pseudoRegret_eq_expected_sub_min ν
    (fun ω => ∑ t ∈ Finset.range T, d t (history t ω) (A t ω))
    (fun k ω => ∑ t ∈ Finset.range T, d t (history t ω) k)
    (integrable_finset_sum _ (fun t _ => hplayed t))
    (fun k => integrable_finset_sum _ (fun t _ => hfixed t k))
  simp only [Finset.sum_sub_distrib] at hmain
  rw [hid] at hmain
  exact hmain

end NormalizedV3

end Part2.HinfProbability
