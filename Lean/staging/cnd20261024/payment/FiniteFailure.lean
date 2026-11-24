import staging.cnd20261024.payment.IntervalBasic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators

namespace Part2.CNDPayment
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem finite_failure_union {κ : Type*} [Fintype κ] (bad : κ → Set Ω) (L : ℝ)
    (htail : ∀ i, μ.real (bad i) ≤ Real.exp (-L)) :
    μ.real {ω | ∃ i, ω ∈ bad i} ≤ (Fintype.card κ : ℝ) * Real.exp (-L) := by
  have heq : {ω | ∃ i, ω ∈ bad i} = ⋃ i, bad i := by ext ω; simp
  rw [heq]
  apply (measureReal_iUnion_fintype_le bad).trans
  calc
    _ ≤ ∑ _i : κ, Real.exp (-L) := Finset.sum_le_sum fun i _ => htail i
    _ = _ := by simp [nsmul_eq_mul]

theorem failure_log_identity {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    a * Real.exp (-Real.log (a / δ)) = δ := by
  rw [Real.exp_neg, Real.exp_log (div_pos ha hδ)]
  field_simp

theorem failure_log_pos {a δ : ℝ} (ha : 1 ≤ a) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.log (a / δ) := Real.log_pos ((one_lt_div hδ0).2 (by linarith))

end Part2.CNDPayment
