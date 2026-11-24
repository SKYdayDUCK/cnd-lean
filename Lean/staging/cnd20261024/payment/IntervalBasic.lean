import staging.cnd20261024.payment.ObservablePayment
import Lean.Elab.Tactic.Omega

noncomputable section
open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators

namespace Part2.CNDPayment
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

def shiftedFiltration (ℱ : Filtration ℕ m₀) (u : ℕ) : Filtration ℕ m₀ where
  seq n := ℱ (u + n)
  mono' := fun _ _ hij => ℱ.mono (Nat.add_le_add_left hij u)
  le' n := ℱ.le (u + n)

def intervalSum (X : ℕ → Ω → ℝ) (u n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ range n, X (u + k) ω

theorem intervalSum_measurable (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (hXm : ∀ n, Measurable[ℱ (n + 1)] (X n)) (u n : ℕ) :
    Measurable[ℱ (u + n)] (intervalSum X u n) :=
  Finset.measurable_fun_sum _ fun k hk => (hXm (u + k)).mono
    (ℱ.mono (by have := Finset.mem_range.mp hk; omega)) le_rfl

theorem intervalSum_bound (X : ℕ → Ω → ℝ) {B : ℝ}
    (hXb : ∀ n ω, |X n ω| ≤ B) (u n : ℕ) (ω : Ω) :
    |intervalSum X u n ω| ≤ (n : ℝ) * B := by
  calc
    _ ≤ ∑ k ∈ range n, |X (u + k) ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range n, B := Finset.sum_le_sum fun k _ => hXb (u + k) ω
    _ = _ := by simp [nsmul_eq_mul]

end Part2.CNDPayment
