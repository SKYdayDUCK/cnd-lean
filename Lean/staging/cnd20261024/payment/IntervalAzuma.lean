import staging.cnd20261024.payment.IntervalBasic
import Mathlib.Probability.Moments.SubGaussian

noncomputable section
open MeasureTheory Filter Finset ProbabilityTheory
open scoped BigOperators NNReal
set_option maxHeartbeats 800000

namespace Part2.CNDPayment
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀} {X : ℕ → Ω → ℝ} {B σ : ℝ}

theorem interval_exponential_integrable
    (hXm : ∀ n, Measurable[ℱ (n + 1)] (X n)) (hXb : ∀ n ω, |X n ω| ≤ B)
    (u n : ℕ) (t : ℝ) : Integrable (fun ω => Real.exp (t * intervalSum X u n ω)) μ := by
  apply PairConfidence.bounded_integrable
    ((measurable_const.mul ((intervalSum_measurable ℱ X hXm u n).mono (ℱ.le _) le_rfl)).exp)
    (B := Real.exp (|t| * ((n : ℝ) * B)))
  intro ω
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (intervalSum_bound X hXb u n ω) (abs_nonneg t))

/-- Unconditional interval MGF is constructed by actual conditional towers.
The one-step MGF premise is discharged by M1 in the public/encoder wrappers. -/
theorem interval_mgf
    (hXm : ∀ n, Measurable[ℱ (n + 1)] (X n)) (hXb : ∀ n ω, |X n ω| ≤ B)
    (hmgf : ∀ n t, μ[fun ω => Real.exp (t * X n ω) | ℱ n] ≤ᵐ[μ]
      fun _ => Real.exp (σ ^ 2 * t ^ 2 / 2)) (u n : ℕ) (t : ℝ) :
    mgf (intervalSum X u n) μ t ≤ Real.exp ((n : ℝ) * σ ^ 2 * t ^ 2 / 2) := by
  induction n with
  | zero => simp [mgf, intervalSum]
  | succ n ih =>
    let F : Ω → ℝ := fun ω => Real.exp (t * intervalSum X u n ω)
    let G : Ω → ℝ := fun ω => Real.exp (t * X (u + n) ω)
    have hFi := interval_exponential_integrable (μ := μ) hXm hXb u n t
    have hGi : Integrable G μ := by
      have hi := interval_exponential_integrable (μ := μ) hXm hXb (u + n) 1 t
      simpa only [intervalSum, Finset.sum_range_one, Nat.add_zero] using hi
    have hEq : (fun ω => Real.exp (t * intervalSum X u (n + 1) ω)) = F * G := by
      funext ω
      simp only [intervalSum, Finset.sum_range_succ, mul_add, Real.exp_add, F, G, Pi.mul_apply]
    have hFGi : Integrable (F * G) μ := by
      rw [← hEq]
      exact interval_exponential_integrable hXm hXb u (n + 1) t
    have hFm : StronglyMeasurable[ℱ (u + n)] F :=
      (measurable_const.mul (intervalSum_measurable ℱ X hXm u n)).exp.stronglyMeasurable
    have hpull := condExp_mul_of_stronglyMeasurable_left hFm hFGi hGi
    have hFCEi : Integrable (F * μ[G | ℱ (u + n)]) μ := integrable_condExp.congr hpull
    have hle : F * μ[G | ℱ (u + n)] ≤ᵐ[μ]
        fun ω => F ω * Real.exp (σ ^ 2 * t ^ 2 / 2) := by
      filter_upwards [hmgf (u + n) t] with ω hω
      exact mul_le_mul_of_nonneg_left hω (Real.exp_nonneg _)
    calc
      _ = ∫ ω, F ω * G ω ∂μ := by rw [mgf, hEq]; rfl
      _ = ∫ ω, (F * μ[G | ℱ (u + n)]) ω ∂μ := by
        rw [← integral_condExp (ℱ.le (u + n))]
        exact integral_congr_ae hpull
      _ ≤ ∫ ω, F ω * Real.exp (σ ^ 2 * t ^ 2 / 2) ∂μ :=
        integral_mono_ae hFCEi (hFi.mul_const _) hle
      _ = (∫ ω, F ω ∂μ) * Real.exp (σ ^ 2 * t ^ 2 / 2) := integral_mul_const _ _
      _ ≤ Real.exp ((n : ℝ) * σ ^ 2 * t ^ 2 / 2) * Real.exp (σ ^ 2 * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

theorem interval_subGaussian
    (hXm : ∀ n, Measurable[ℱ (n + 1)] (X n)) (hXb : ∀ n ω, |X n ω| ≤ B)
    (hmgf : ∀ n t, μ[fun ω => Real.exp (t * X n ω) | ℱ n] ≤ᵐ[μ]
      fun _ => Real.exp (σ ^ 2 * t ^ 2 / 2)) (u n : ℕ) :
    HasSubgaussianMGF (intervalSum X u n) ⟨(n : ℝ) * σ ^ 2, by positivity⟩ μ where
  integrable_exp_mul t := interval_exponential_integrable hXm hXb u n t
  mgf_le t := by
    simpa only [NNReal.coe_mk, mul_assoc] using interval_mgf hXm hXb hmgf u n t

/-- Exact Azuma-Hoeffding scale, including zero scale and empty intervals.
The strict failure event avoids counting equality at the zero threshold. -/
theorem interval_hoeffding
    (hXm : ∀ n, Measurable[ℱ (n + 1)] (X n)) (hXb : ∀ n ω, |X n ω| ≤ B)
    (hmgf : ∀ n t, μ[fun ω => Real.exp (t * X n ω) | ℱ n] ≤ᵐ[μ]
      fun _ => Real.exp (σ ^ 2 * t ^ 2 / 2)) (hσ : 0 ≤ σ)
    (u n : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | σ * Real.sqrt (2 * (n : ℝ) * L) < intervalSum X u n ω} ≤ Real.exp (-L) := by
  have hsg := interval_subGaussian hXm hXb hmgf u n
  by_cases hn : n = 0
  · simp [hn, intervalSum, Real.exp_nonneg]
  by_cases hs : σ = 0
  · have hzsg : HasSubgaussianMGF (intervalSum X u n) 0 μ := by simpa [hs] using hsg
    have hz := hzsg.ae_eq_zero_of_hasSubgaussianMGF_zero
    have heq : {ω | σ * Real.sqrt (2 * (n : ℝ) * L) < intervalSum X u n ω} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hz] with ω hω
      apply propext
      change (σ * Real.sqrt (2 * (n : ℝ) * L) < intervalSum X u n ω) ↔ False
      have hw : intervalSum X u n ω = 0 := hω
      simp only [hs, zero_mul, hw, lt_self_iff_false]
    rw [measureReal_congr heq]
    simpa only [measureReal_empty] using Real.exp_nonneg (-L)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsR : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hs)
  have hε : 0 ≤ σ * Real.sqrt (2 * (n : ℝ) * L) := mul_nonneg hσ (Real.sqrt_nonneg _)
  have ht := hsg.measure_ge_le hε
  have hexp : -(σ * Real.sqrt (2 * (n : ℝ) * L)) ^ 2 /
      (2 * ((n : ℝ) * σ ^ 2)) = -L := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [ne_of_gt hnR, ne_of_gt hsR]
  simp only [NNReal.coe_mk, hexp] at ht
  exact (measureReal_mono (show {ω | σ * Real.sqrt (2 * (n : ℝ) * L) < intervalSum X u n ω} ⊆
    {ω | σ * Real.sqrt (2 * (n : ℝ) * L) ≤ intervalSum X u n ω} from fun ω hw => (show σ * Real.sqrt (2 * (n : ℝ) * L) < intervalSum X u n ω from hw).le)).trans ht

end Part2.CNDPayment
