import staging.cnd20261024.payment.FiniteHoeffding
import staging.cnd20261024.payment.ObservablePayment

noncomputable section
open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators
set_option maxHeartbeats 800000

namespace Part2.CNDPayment
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}
variable (h : CNDProbability.M1Model ℱ μ θ R M D)

/-- Actual actions have positive mass almost surely; no exploration floor. -/
theorem action_supported (n : ℕ) : ∀ᵐ ω ∂μ, 0 < h.p n (h.action n ω) ω := by
  let f : ι → Ω → ℝ := fun a ω => if 0 < h.p n a ω then 0 else 1
  have hfm (a : ι) : Measurable[h.encoded n] (f a) :=
    measurable_const.ite
      (measurableSet_lt measurable_const ((h.p_measurable n a).mono
        ((h.past_le_pre n).trans (h.pre_le_encoded n)) le_rfl)) measurable_const
  have hfb (a : ι) (ω : Ω) : |f a ω| ≤ 1 := by simp only [f]; split_ifs <;> norm_num
  have hfi (a : ι) : Integrable (f a) μ := PairConfidence.bounded_integrable
    ((hfm a).mono ((h.encoded_le_next n).trans (ℱ.le (n + 1))) le_rfl) (hfb a)
  have he := h.encoded_selected_expectation n f (fun a => (hfm a).stronglyMeasurable) hfi
  have hz : μ[fun ω => f (h.action n ω) ω | h.encoded n] =ᵐ[μ] fun _ => 0 := by
    filter_upwards [he] with ω heω
    rw [heω]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : 0 < h.p n a ω
    · simp [f, ha]
    · have hp0 : h.p n a ω = 0 := le_antisymm (le_of_not_gt ha) (h.p_nonneg n ω a)
      simp [f, hp0]
  have hZi := PairConfidence.selected_integrable
    ((h.action_measurable n).mono (h.action_le n) le_rfl) hfi
  have hi : ∫ ω, f (h.action n ω) ω ∂μ = 0 := by
    rw [← integral_condExp ((h.encoded_le_next n).trans (ℱ.le (n + 1)))]
    exact integral_eq_zero_of_ae hz
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => show 0 ≤ f (h.action n ω) ω by
    simp only [f]; split_ifs <;> norm_num) hZi).mp hi
  filter_upwards [hae] with ω hω
  by_contra hn
  simp [f, hn] at hω

variable (l : ℕ → ι → Ω → ℝ)

def publicCenteredAt (n : ℕ) (a : ι) (ω : Ω) : ℝ :=
  safeCentered (fun i => h.p n i ω) (fun i => l n i ω) a
def publicResidual (n : ℕ) (ω : Ω) : ℝ := publicCenteredAt h l n (h.action n ω) ω

theorem publicResidual_eq_actual (n : ℕ) : publicResidual h l n =ᵐ[μ]
    fun ω => l n (h.action n ω) ω - ∑ a, h.p n a ω * l n a ω := by
  filter_upwards [action_supported h n] with ω hω
  simp only [publicResidual, publicCenteredAt, safeCentered, if_pos hω]

theorem publicCenteredAt_measurable
    (hlm : ∀ n a, Measurable[h.encoded n] (l n a)) (n : ℕ) (a : ι) :
    Measurable[h.encoded n] (publicCenteredAt h l n a) := by
  have hpm (a : ι) : Measurable[h.encoded n] (h.p n a) := (h.p_measurable n a).mono
    ((h.past_le_pre n).trans (h.pre_le_encoded n)) le_rfl
  exact ((hlm n a).sub (Finset.measurable_fun_sum _ fun i _ => (hpm i).mul (hlm n i))).ite
    (measurableSet_lt measurable_const (hpm a)) measurable_const

theorem publicResidual_measurable
    (hlm : ∀ n a, Measurable[h.encoded n] (l n a)) (n : ℕ) :
    Measurable[ℱ (n + 1)] (publicResidual h l n) :=
  PairConfidence.selected_measurable ((h.action_measurable n).mono (h.action_le_next n) le_rfl)
    (fun a => (publicCenteredAt_measurable h l hlm n a).mono (h.encoded_le_next n) le_rfl)

theorem publicResidual_bound {W : ℝ} (hW : 0 ≤ W)
    (hspan : ∀ n ω i j, 0 < h.p n i ω → 0 < h.p n j ω → |l n i ω - l n j ω| ≤ 2 * W)
    (n : ℕ) (ω : Ω) : |publicResidual h l n ω| ≤ 2 * W :=
  safeCentered_bound _ _ (h.p_nonneg n ω) (h.p_sum n ω) hW (hspan n ω) _

/-- Exact W-variance proxy from the actual full-potential categorical law.
The original only-positive-support span is sufficient. -/
theorem publicResidual_conditional_mgf [Nonempty ι] {W : ℝ} (hW : 0 ≤ W)
    (hlm : ∀ n a, Measurable[h.encoded n] (l n a))
    (hspan : ∀ n ω i j, 0 < h.p n i ω → 0 < h.p n j ω → |l n i ω - l n j ω| ≤ 2 * W)
    (n : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * publicResidual h l n ω)) μ ∧
      μ[fun ω => Real.exp (t * publicResidual h l n ω) | ℱ n] ≤ᵐ[μ]
        fun _ => Real.exp (W ^ 2 * t ^ 2 / 2) := by
  let f : ι → Ω → ℝ := fun a ω => Real.exp (t * publicCenteredAt h l n a ω)
  have hfm (a : ι) : Measurable[h.encoded n] (f a) :=
    (measurable_const.mul (publicCenteredAt_measurable h l hlm n a)).exp
  have hfb (a : ι) (ω : Ω) : |f a ω| ≤ Real.exp (|t| * (2 * W)) := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |t * publicCenteredAt h l n a ω| := le_abs_self _
      _ ≤ |t| * (2 * W) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (safeCentered_bound _ _ (h.p_nonneg n ω) (h.p_sum n ω) hW (hspan n ω) a) (abs_nonneg t)
  have hfi (a : ι) : Integrable (f a) μ := PairConfidence.bounded_integrable
    ((hfm a).mono ((h.encoded_le_next n).trans (ℱ.le (n + 1))) le_rfl) (hfb a)
  have hEi : Integrable (fun ω => Real.exp (t * publicResidual h l n ω)) μ :=
    PairConfidence.selected_integrable ((h.action_measurable n).mono (h.action_le n) le_rfl) hfi
  refine ⟨hEi, ?_⟩
  have he := h.encoded_selected_expectation n f (fun a => (hfm a).stronglyMeasurable) hfi
  have henc : μ[fun ω => Real.exp (t * publicResidual h l n ω) | h.encoded n] ≤ᵐ[μ]
      fun _ => Real.exp (W ^ 2 * t ^ 2 / 2) := by
    filter_upwards [he] with ω hω
    change (μ[fun ω => f (h.action n ω) ω | h.encoded n]) ω ≤ _
    rw [hω]
    exact safeCentered_hoeffding _ _ (h.p_nonneg n ω) (h.p_sum n ω) hW (hspan n ω) t
  have ht := condExp_condExp_of_le (μ := μ)
    (f := fun ω => Real.exp (t * publicResidual h l n ω))
    ((h.past_le_pre n).trans (h.pre_le_encoded n)) ((h.encoded_le_next n).trans (ℱ.le (n + 1)))
  have hmono := condExp_mono (m := ℱ n) (integrable_condExp : Integrable
    (μ[fun ω => Real.exp (t * publicResidual h l n ω) | h.encoded n]) μ)
    (integrable_const (Real.exp (W ^ 2 * t ^ 2 / 2))) henc
  filter_upwards [ht, hmono] with ω htω hmω
  rw [← htω]
  simpa only [condExp_const (ℱ.le n)] using hmω

end Part2.CNDPayment
