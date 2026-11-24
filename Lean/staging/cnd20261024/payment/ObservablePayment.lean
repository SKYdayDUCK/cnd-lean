import staging.cnd20261024.probability.ModelBridge
import Part2.StoppedBudget
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators

namespace Part2.CNDPayment

section Algebra
variable {ι : Type*} [Fintype ι]

def rowMean (p : ι → ℝ) (r : ι → ι → ℝ) (i : ι) : ℝ := ∑ j, p j * r i j
def gamma (p : ι → ℝ) (r : ι → ι → ℝ) : ℝ := ∑ i, p i * rowMean p r i

theorem rowMean_bounds (p : ι → ℝ) (r : ι → ι → ℝ) (C : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hr : ∀ i j, 0 ≤ r i j ∧ r i j ≤ C / 2) (i : ι) :
    0 ≤ 2 * rowMean p r i ∧ 2 * rowMean p r i ≤ C := by
  have h0 : 0 ≤ rowMean p r i := Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (hr i j).1
  have h1 : rowMean p r i ≤ C / 2 := by
    calc
      _ ≤ ∑ j, p j * (C / 2) := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hr i j).2 (hp j)
      _ = C / 2 := by rw [← Finset.sum_mul, hs, one_mul]
  constructor <;> linarith

end Algebra

section ActualPayment
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}

variable (h : CNDProbability.M1Model ℱ μ θ R M D)
  (r : ℕ → ι → ι → Ω → ℝ)

def paymentAt (n : ℕ) (a : ι) (ω : Ω) : ℝ :=
  2 * rowMean (fun j => h.p n j ω) (fun i j => r n i j ω) a
def observablePayment (n : ℕ) (ω : Ω) : ℝ := paymentAt h r n (h.action n ω) ω
def predictableGamma (n : ℕ) (ω : Ω) : ℝ :=
  gamma (fun i => h.p n i ω) (fun i j => r n i j ω)

theorem paymentAt_measurable (hr : ∀ n i j, Measurable[ℱ n] (r n i j)) (n : ℕ) (a : ι) :
    Measurable[ℱ n] (paymentAt h r n a) :=
  measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => (h.p_measurable n j).mul (hr n a j))

theorem observablePayment_measurable (hr : ∀ n i j, Measurable[ℱ n] (r n i j)) (n : ℕ) :
    Measurable[ℱ (n + 1)] (observablePayment h r n) :=
  PairConfidence.selected_measurable ((h.action_measurable n).mono (h.action_le_next n) le_rfl)
    (fun a => (paymentAt_measurable h r hr n a).mono (ℱ.mono (Nat.le_succ n)) le_rfl)

theorem predictableGamma_measurable (hr : ∀ n i j, Measurable[ℱ n] (r n i j)) (n : ℕ) :
    Measurable[ℱ n] (predictableGamma h r n) :=
  Finset.measurable_fun_sum _ fun i _ => (h.p_measurable n i).mul
    (Finset.measurable_fun_sum _ fun j _ => (h.p_measurable n j).mul (hr n i j))

/-- Actual payment bounds follow from entrywise radius bounds, not confidence. -/
theorem observablePayment_bounds (C : ℝ)
    (hr : ∀ n i j ω, 0 ≤ r n i j ω ∧ r n i j ω ≤ C / 2) (n : ℕ) (ω : Ω) :
    0 ≤ observablePayment h r n ω ∧ observablePayment h r n ω ≤ C :=
  rowMean_bounds _ _ C (h.p_nonneg n ω) (h.p_sum n ω) (fun i j => hr n i j ω) _

/-- The compensator is derived from M1's strong actual action kernel. -/
theorem observablePayment_condExp (C : ℝ) (hC : 0 ≤ C)
    (hrm : ∀ n i j, Measurable[ℱ n] (r n i j))
    (hrb : ∀ n i j ω, 0 ≤ r n i j ω ∧ r n i j ω ≤ C / 2) (n : ℕ) :
    μ[observablePayment h r n | ℱ n] =ᵐ[μ] fun ω => 2 * predictableGamma h r n ω := by
  have hfb (a : ι) (ω : Ω) : |paymentAt h r n a ω| ≤ C := by
    have hb := rowMean_bounds _ _ C (h.p_nonneg n ω) (h.p_sum n ω) (fun i j => hrb n i j ω) a
    change |2 * rowMean (fun j => h.p n j ω) (fun i j => r n i j ω) a| ≤ C
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hfi (a : ι) : Integrable (paymentAt h r n a) μ := PairConfidence.bounded_integrable
    ((paymentAt_measurable h r hrm n a).mono (ℱ.le n) le_rfl) (hfb a)
  have he := h.encoded_selected_expectation n (paymentAt h r n)
    (fun a => (paymentAt_measurable h r hrm n a).stronglyMeasurable.mono
      ((h.past_le_pre n).trans (h.pre_le_encoded n))) hfi
  have he' : μ[observablePayment h r n | h.encoded n] =ᵐ[μ]
      fun ω => 2 * predictableGamma h r n ω := by
    filter_upwards [he] with ω hω
    change (μ[fun ω => paymentAt h r n (h.action n ω) ω | h.encoded n]) ω = _
    rw [hω]
    simp only [predictableGamma, gamma, paymentAt, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hgb (ω : Ω) : |2 * predictableGamma h r n ω| ≤ C := by
    calc
      _ = |∑ i, h.p n i ω * paymentAt h r n i ω| := by
        congr 1
        simp only [predictableGamma, gamma, paymentAt, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, |h.p n i ω * paymentAt h r n i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, h.p n i ω * C := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (h.p_nonneg n ω i)]
        exact mul_le_mul_of_nonneg_left (hfb i ω) (h.p_nonneg n ω i)
      _ = C := by rw [← Finset.sum_mul, h.p_sum n ω, one_mul]
  exact PairConfidence.conditional_down ((h.past_le_pre n).trans (h.pre_le_encoded n))
    ((h.encoded_le_next n).trans (ℱ.le (n + 1))) he'
    (measurable_const.mul (predictableGamma_measurable h r hrm n)).stronglyMeasurable
    (PairConfidence.bounded_integrable
      ((measurable_const.mul (predictableGamma_measurable h r hrm n)).mono (ℱ.le n) le_rfl) hgb)

end ActualPayment
end Part2.CNDPayment
