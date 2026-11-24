import staging.cnd20261024.process.StatisticalMaps

/-! Predictability of the exact pre-existing radius for every predictable
probability process. No confidence event and no S statistic are needed. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators Matrix
namespace Part2.CNDProcess
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [m₀ : MeasurableSpace Ω] (ℱ : Filtration ℕ m₀)

local instance : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

theorem information_history_measurable (p : ℕ → ι → Ω → ℝ)
    (hp : ∀ t i, Measurable[ℱ t] (p t i)) (n : ℕ) :
    Measurable[ℱ n] (fun ω ↦ CNDPhysical.information (fun t i ↦ p t i ω) n) := by
  apply @measurable_pi_lambda Ω ι (fun _ ↦ ι → ℝ) (ℱ n) _
  intro i
  apply @measurable_pi_lambda Ω ι (fun _ ↦ ℝ) (ℱ n) _
  intro j
  simp only [CNDPhysical.information, Matrix.add_apply, Matrix.sum_apply]
  apply measurable_const.add
  apply Finset.measurable_fun_sum
  intro t ht
  have hpi := (hp t i).mono (ℱ.mono (Nat.le_of_lt (mem_range.mp ht))) le_rfl
  have hpj := (hp t j).mono (ℱ.mono (Nat.le_of_lt (mem_range.mp ht))) le_rfl
  unfold CNDPhysical.covariance
  exact (by split_ifs <;> fun_prop)

theorem actualSaturatedRadius_history_measurable (p : ℕ → ι → Ω → ℝ)
    (hp : ∀ t i, Measurable[ℱ t] (p t i)) (n : ℕ) (H L R : ℝ) (i j : ι) :
    Measurable[ℱ n] (fun ω ↦
      CNDPhysical.actualSaturatedRadius (fun t a ↦ p t a ω) n H L R i j) := by
  have hi := StatisticalMaps.measurable_matrix_inverse.comp
    (information_history_measurable ℱ p hp n)
  have hb (a b : ι) : Measurable[ℱ n]
      (fun ω ↦ (CNDPhysical.information (fun t i ↦ p t i ω) n)⁻¹ a b) :=
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hi)
  have hd : Measurable[ℱ n] (fun ω ↦ CNDPhysical.resistance (fun t a ↦ p t a ω) n i j) :=
    ((hb i i).add (hb j j)).sub ((hb i j).const_mul 2)
  have hr := (((hd.const_mul L).sqrt).const_mul (2 * H)).add
    (hd.const_mul (4 * H * L + R * Fintype.card ι))
  exact (measurable_const.sub (((hr.div_const R).neg).exp)).const_mul _

end Part2.CNDProcess
end
