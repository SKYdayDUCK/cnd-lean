import staging.cnd20261024.payment.IntervalBasic
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators

namespace Part2.CNDPayment

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Complete original-space compensated interval concentration. Adaptedness,
boundedness and the primitive conditional mean are inputs, never a tail. -/
theorem bounded_interval_tail (ℱ : Filtration ℕ m₀) (X A : ℕ → Ω → ℝ)
    {C : ℝ} (hC : 0 < C)
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hXb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ C)
    (hmean : ∀ n, μ[X n | ℱ n] =ᵐ[μ] A n) (u n : ℕ) (L : ℝ) :
    μ.real {ω | (Real.exp 1 - 1) * intervalSum A u n ω + C * L ≤ intervalSum X u n ω}
      ≤ Real.exp (-L) := by
  let Y : ℕ → Ω → ℝ := fun k ω => X (u + k) ω / C
  have hYm (k : ℕ) : StronglyMeasurable[shiftedFiltration ℱ u (k + 1)] (Y k) := by
    have hs : StronglyMeasurable[ℱ (u + k + 1)] (fun ω => C⁻¹ * X (u + k) ω) :=
      stronglyMeasurable_const.mul (hXm (u + k))
    change StronglyMeasurable[ℱ (u + (k + 1))] (Y k)
    simpa only [Y, div_eq_mul_inv, mul_comm, Nat.add_assoc] using
      (show StronglyMeasurable[ℱ (u + k + 1)] (fun ω => C⁻¹ * X (u + k) ω) from hs)
  have hYb (k : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ Y k ω ∧ Y k ω ≤ 1 := ae_of_all _ fun ω =>
    ⟨div_nonneg (hXb (u + k) ω).1 hC.le, (div_le_one hC).2 (hXb (u + k) ω).2⟩
  have hYmean (k : ℕ) : μ[Y k | shiftedFiltration ℱ u k] =ᵐ[μ]
      fun ω => A (u + k) ω / C := by
    have he := (condExp_smul (μ := μ) C⁻¹ (X (u + k)) (ℱ (u + k))).trans
      ((hmean (u + k)).const_smul C⁻¹)
    have hf : Y k = C⁻¹ • X (u + k) := by
      ext ω
      simp only [Y, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [hf]
    change (μ[C⁻¹ • X (u + k) | ℱ (u + k)]) =ᵐ[μ] _
    filter_upwards [he] with ω hω
    simpa only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using hω
  have ht := StoppedBudget.bounded_budget_tail μ (shiftedFiltration ℱ u) Y hYm hYb n L
  have hEq : {ω | (Real.exp 1 - 1) * (∑ k ∈ range n,
      (μ[Y k | shiftedFiltration ℱ u k]) ω) + L ≤ ∑ k ∈ range n, Y k ω} =ᵐ[μ]
      {ω | (Real.exp 1 - 1) * intervalSum A u n ω + C * L ≤ intervalSum X u n ω} := by
    filter_upwards [ae_all_iff.mpr hYmean] with ω hw
    apply propext
    change ((Real.exp 1 - 1) * (∑ k ∈ range n,
      (μ[Y k | shiftedFiltration ℱ u k]) ω) + L ≤ ∑ k ∈ range n, Y k ω) ↔ _
    simp_rw [hw]
    simp only [intervalSum, Y, ← Finset.sum_div]
    have heq : (Real.exp 1 - 1) * ((∑ k ∈ range n, A (u + k) ω) / C) + L =
        ((Real.exp 1 - 1) * (∑ k ∈ range n, A (u + k) ω) + C * L) / C := by
      field_simp
    rw [heq, div_le_div_iff_of_pos_right hC]
    rfl
  rwa [measureReal_congr hEq] at ht

theorem exp_compensator_le_four : 2 * (Real.exp 1 - 1) ≤ 4 := by
  have he := Real.exp_one_lt_d9
  linarith

section Actual
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ}

theorem observablePayment_interval_tail
    (h : CNDProbability.M1Model ℱ μ θ R M D)
    (r : ℕ → ι → ι → Ω → ℝ) {C : ℝ} (hC : 0 < C)
    (hrm : ∀ n i j, Measurable[ℱ n] (r n i j))
    (hrb : ∀ n i j ω, 0 ≤ r n i j ω ∧ r n i j ω ≤ C / 2)
    (u n : ℕ) (Q : Ω → ℝ)
    (hQ : ∀ ω, intervalSum (predictableGamma h r) u n ω ≤ Q ω) (L : ℝ) :
    μ.real {ω | 4 * Q ω + C * L ≤ intervalSum (observablePayment h r) u n ω} ≤ Real.exp (-L) := by
  have ht := bounded_interval_tail ℱ (observablePayment h r)
    (fun t ω => 2 * predictableGamma h r t ω) hC
    (fun t => (observablePayment_measurable h r hrm t).stronglyMeasurable)
    (observablePayment_bounds h r C hrb)
    (observablePayment_condExp h r C hC.le hrm hrb) u n L
  apply (measureReal_mono (show {ω | 4 * Q ω + C * L ≤ intervalSum (observablePayment h r) u n ω} ⊆
      {ω | (Real.exp 1 - 1) * intervalSum (fun t ω => 2 * predictableGamma h r t ω) u n ω + C * L ≤
        intervalSum (observablePayment h r) u n ω} from ?_)).trans ht
  intro ω hω
  have hΓ : 0 ≤ intervalSum (predictableGamma h r) u n ω :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun i _ =>
      mul_nonneg (h.p_nonneg _ ω i) (Finset.sum_nonneg fun j _ =>
        mul_nonneg (h.p_nonneg _ ω j) (hrb _ i j ω).1)
  have hcoeff := mul_le_mul_of_nonneg_right exp_compensator_le_four hΓ
  have hbudget := hQ ω
  change 4 * Q ω + C * L ≤ intervalSum (observablePayment h r) u n ω at hω
  change (Real.exp 1 - 1) * intervalSum (fun t ω => 2 * predictableGamma h r t ω) u n ω + C * L ≤ _
  have hdouble : intervalSum (fun t ω => 2 * predictableGamma h r t ω) u n ω =
      2 * intervalSum (predictableGamma h r) u n ω := by simp only [intervalSum, Finset.mul_sum]
  rw [hdouble]
  nlinarith

/-- The C*=0 branch needs no normalized process or division by zero. -/
theorem observablePayment_zero
    (h : CNDProbability.M1Model ℱ μ θ R M D) (r : ℕ → ι → ι → Ω → ℝ)
    (hrb : ∀ n i j ω, 0 ≤ r n i j ω ∧ r n i j ω ≤ 0 / 2) (u n : ℕ) (ω : Ω) :
    intervalSum (observablePayment h r) u n ω = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  have hb := observablePayment_bounds h r 0 hrb (u + t) ω
  exact le_antisymm hb.2 hb.1

end Actual

end Part2.CNDPayment
