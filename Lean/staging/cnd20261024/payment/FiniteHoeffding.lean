import Part2.HinfProbability
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Data.Finset.Max

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal NNReal
set_option maxHeartbeats 800000

namespace Part2.CNDPayment
section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def safeCentered (p l : ι → ℝ) (i : ι) : ℝ :=
  if 0 < p i then l i - ∑ j, p j * l j else 0

theorem safeCentered_mean (p l : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∑ i, p i * safeCentered p l i = 0 := by
  have heq (i : ι) : p i * safeCentered p l i = p i * (l i - ∑ j, p j * l j) := by
    by_cases hi : 0 < p i
    · simp [safeCentered, hi]
    · have hz : p i = 0 := le_antisymm (le_of_not_gt hi) (hp i)
      simp [safeCentered, hi, hz]
  simp_rw [heq, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul, sub_self]

theorem safeCentered_bound (p l : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    {W : ℝ} (hW : 0 ≤ W)
    (hspan : ∀ i j, 0 < p i → 0 < p j → |l i - l j| ≤ 2 * W) (i : ι) :
    |safeCentered p l i| ≤ 2 * W := by
  by_cases hi : 0 < p i
  · have heq : safeCentered p l i = ∑ j, p j * (l i - l j) := by
      simp [safeCentered, hi, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
    rw [heq]
    calc
      _ ≤ ∑ j, |p j * (l i - l j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, p j * (2 * W) := Finset.sum_le_sum fun j _ => by
        by_cases hj : 0 < p j
        · rw [abs_mul, abs_of_nonneg (hp j)]
          exact mul_le_mul_of_nonneg_left (hspan i j hi hj) (hp j)
        · have hz : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
          simp [hz]
      _ = 2 * W := by rw [← Finset.sum_mul, hs, one_mul]
  · simp only [safeCentered, if_neg hi, abs_zero]
    linarith

theorem safeCentered_span (p l : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    {W : ℝ} (hW : 0 ≤ W)
    (hspan : ∀ i j, 0 < p i → 0 < p j → |l i - l j| ≤ 2 * W) (i j : ι) :
    |safeCentered p l i - safeCentered p l j| ≤ 2 * W := by
  by_cases hi : 0 < p i <;> by_cases hj : 0 < p j
  · simpa [safeCentered, hi, hj] using hspan i j hi hj
  · simpa [safeCentered, hj] using safeCentered_bound p l hp hs hW hspan i
  · simpa [safeCentered, hi, abs_neg] using safeCentered_bound p l hp hs hW hspan j
  · simp [safeCentered, hi, hj, hW]

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem centered_finite_hoeffding (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hc : ∑ i, p i * f i = 0) {W : ℝ} (hW : 0 ≤ W)
    (hspan : ∀ i j, |f i - f j| ≤ 2 * W) (t : ℝ) :
    ∑ i, p i * Real.exp (t * f i) ≤ Real.exp (W ^ 2 * t ^ 2 / 2) := by
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  let ν := (HinfProbability.categoricalPMF p hp hs).toMeasure
  have hInt (g : ι → ℝ) : ∫ i, g i ∂ν = ∑ i, p i * g i := by
    rw [integral_fintype g (HinfProbability.finite_integrable _ g)]
    apply Finset.sum_congr rfl
    intro i _
    simp [ν, HinfProbability.categoricalPMF, Measure.real, PMF.toMeasure_apply_fintype,
      Set.indicator_apply, ENNReal.toReal_ofReal (hp i), smul_eq_mul]
  have hsg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (measurable_of_countable f).aemeasurable
    (ae_of_all ν fun i => show f i ∈ Set.Icc (f a) (f b) from
      ⟨ha i (Finset.mem_univ i), hb i (Finset.mem_univ i)⟩)
    (show ∫ i, f i ∂ν = 0 by rw [hInt]; exact hc)
  have hab : 0 ≤ f b - f a := sub_nonneg.mpr (ha b (Finset.mem_univ b))
  have hwidth : |f b - f a| ≤ 2 * W := hspan b a
  have hproxy : ((‖f b - f a‖₊ / 2 : ℝ≥0) ^ 2 : ℝ) ≤ W ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs]
    nlinarith [abs_nonneg (f b - f a)]
  calc
    _ = mgf f ν t := (hInt _).symm
    _ ≤ Real.exp (((‖f b - f a‖₊ / 2 : ℝ≥0) ^ 2 : ℝ) * t ^ 2 / 2) := hsg.mgf_le t
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hproxy (sq_nonneg t)])

theorem safeCentered_hoeffding (p l : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) {W : ℝ} (hW : 0 ≤ W)
    (hspan : ∀ i j, 0 < p i → 0 < p j → |l i - l j| ≤ 2 * W) (t : ℝ) :
    ∑ i, p i * Real.exp (t * safeCentered p l i) ≤ Real.exp (W ^ 2 * t ^ 2 / 2) :=
  centered_finite_hoeffding p _ hp hs (safeCentered_mean p l hp hs) hW
    (safeCentered_span p l hp hs hW hspan) t

end Finite
end Part2.CNDPayment
