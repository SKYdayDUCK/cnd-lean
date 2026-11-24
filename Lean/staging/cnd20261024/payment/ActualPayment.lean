import staging.cnd20261024.payment.PaymentTail
import PrivateInformationBudget

noncomputable section
open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators
set_option maxHeartbeats 800000

namespace Part2.CNDPayment
variable {Ω ι η : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype η] [DecidableEq η]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}
variable (h : CNDProbability.M1Model ℱ μ θ R M D)

def actualRadius (H L : ℝ) (t : ℕ) (i j : ι) (ω : Ω) : ℝ :=
  CNDPhysical.actualSaturatedRadius (fun n a => h.p n a ω) t H L R i j
def actualQ (Q : Matrix ι η ℝ) (H L : ℝ) (u n : ℕ) (ω : Ω) : ℝ :=
  CNDInformation.branchedQ Q (fun t a => h.p t a ω) u n H L R

theorem paymentAt_eq_actualPayment (H L : ℝ) (t : ℕ) (i : ι) (ω : Ω) :
    paymentAt h (actualRadius h H L) t i ω =
      CNDInformation.actualPayment (fun t a => h.p t a ω) t H L R i := by
  simp only [paymentAt, rowMean, actualRadius, CNDInformation.actualPayment]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem actual_predictableGamma (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (t : ℕ) (ω : Ω) :
    predictableGamma h (actualRadius h H L) t ω =
      CNDInformation.actualGamma (fun t a => h.p t a ω) t H L R := by
  have he := CNDInformation.actualPayment_mean_nonnegR (fun t a => h.p t a ω)
    (fun t => ⟨h.p_nonneg t ω, h.p_sum t ω⟩) t H L R hH hL h.R_nonneg
  simp_rw [← paymentAt_eq_actualPayment h H L t] at he
  have hformula : (∑ i, h.p t i ω * paymentAt h (actualRadius h H L) t i ω) =
      2 * predictableGamma h (actualRadius h H L) t ω := by
    simp only [paymentAt, predictableGamma, gamma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hformula] at he
  linarith

/-- The true information potential bound is instantiated on this same random
p path, rather than assumed as a payment budget. -/
theorem actual_gamma_budget (Q : Matrix ι η ℝ) (hQ : CNDInformation.TangentChart Q)
    (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (u n : ℕ) (ω : Ω) :
    intervalSum (predictableGamma h (actualRadius h H L)) u n ω ≤ actualQ h Q H L u n ω := by
  simp only [intervalSum, actual_predictableGamma h H L hH hL]
  exact CNDInformation.actualGamma_sum_le_branchedQ Q hQ (fun t a => h.p t a ω)
    (fun t => ⟨h.p_nonneg t ω, h.p_sum t ω⟩) u n H L R hH hL h.R_nonneg

theorem actualRadius_bounds (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (t : ℕ) (i j : ι) (ω : Ω) :
    0 ≤ actualRadius h H L t i j ω ∧ actualRadius h H L t i j ω ≤ (4 * R / CNDPhysical.c0) / 2 := by
  by_cases hR0 : R = 0
  · simp [actualRadius, hR0, CNDPhysical.actualSaturatedRadius, CNDPhysical.saturatedRadius]
  have hb := CNDInformation.actual_radius_bounds (fun t a => h.p t a ω)
    (fun t => ⟨h.p_nonneg t ω, h.p_sum t ω⟩) t H L R hH hL
    (lt_of_le_of_ne h.R_nonneg (Ne.symm hR0)) i j
  refine ⟨hb.1, ?_⟩
  have heq : 2 * R / CNDPhysical.c0 = (4 * R / CNDPhysical.c0) / 2 := by ring
  exact hb.2.1.trans_eq heq

/-- Fixed-interval original observable-payment bound with the exact actual Q.
Radius predictability is a technical process-map interface, not a probability
or information-budget oracle. The zero-R branch is explicitly discharged. -/
theorem actualPayment_interval_tail
    (Q : Matrix ι η ℝ) (hQ : CNDInformation.TangentChart Q)
    (H Lc : ℝ) (hH : 0 ≤ H) (hLc : 0 ≤ Lc)
    (hrm : ∀ t i j, Measurable[ℱ t] (actualRadius h H Lc t i j))
    (u n : ℕ) (L : ℝ) :
    μ.real {ω | 4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * L <
      intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} ≤ Real.exp (-L) := by
  by_cases hR0 : R = 0
  · have heq : {ω | 4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * L <
        intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} = ∅ := by
      ext ω
      simp [hR0, actualQ, CNDInformation.branchedQ, intervalSum, observablePayment,
        paymentAt, rowMean, actualRadius, CNDPhysical.actualSaturatedRadius, CNDPhysical.saturatedRadius]
    rw [heq]
    simpa only [measureReal_empty] using Real.exp_nonneg (-L)
  have hC : 0 < 4 * R / CNDPhysical.c0 := div_pos
    (mul_pos (by norm_num) (lt_of_le_of_ne h.R_nonneg (Ne.symm hR0))) CNDPhysical.c0_pos
  have ht := observablePayment_interval_tail h (actualRadius h H Lc) hC hrm
    (actualRadius_bounds h H Lc hH hLc) u n (actualQ h Q H Lc u n)
    (actual_gamma_budget h Q hQ H Lc hH hLc u n) L
  exact (measureReal_mono (show {ω | 4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * L <
      intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} ⊆
    {ω | 4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * L ≤
      intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} from fun ω hw =>
        (show 4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * L <
          intervalSum (observablePayment h (actualRadius h H Lc)) u n ω from hw).le)).trans ht

end Part2.CNDPayment
