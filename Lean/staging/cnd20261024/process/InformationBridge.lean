import staging.cnd20261024.process.StatisticsTrace
import staging.cnd20261024.process.StatisticalMaps

/-! The explicit V state is Pi+sum C(p), not an assumed information matrix.
This module proves its regularization is the actual library information
matrix, then identifies the computed inverse, resistance and saturated radius.
-/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators Matrix

namespace Part2.CNDProcess

variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}

theorem runS_sum_zero (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (n : ℕ) (ω : Ω) : (∑ i, runS o d f n i ω) = 0 := by
  induction n with
  | zero => simp [runS, run, initialState]
  | succ n ih =>
    simp_rw [runS_succ]
    by_cases hz : d.R = 0
    · simp only [hz, ↓reduceIte]
      exact ih
    · simp only [hz, ↓reduceIte, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_sub_distrib, ih]
      have hp := (runProbability_simplex o d f n ω).2
      simp [hp]

theorem regularized_runV_eq_information (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) :
    StatisticalMaps.regularized (fun i j ↦ runV o d f n i j ω) =
      CNDPhysical.information (fun t a ↦ runProbability o d f t a ω) n := by
  funext i j
  rw [StatisticalMaps.regularized, actual_information_identity o d f hR]
  simp only [CNDPhysical.information, Matrix.add_apply, Matrix.sum_apply, Matrix.one_apply]
  ring

theorem computed_inverse_eq_information (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) :
    StatisticalMaps.totalInverse (fun i j ↦ runV o d f n i j ω) =
      CNDPhysical.inverseInformation (fun t a ↦ runProbability o d f t a ω) n := by
  unfold StatisticalMaps.totalInverse CNDPhysical.inverseInformation
  rw [regularized_runV_eq_information o d f hR]

theorem computed_resistance_eq_actual (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) :
    StatisticalMaps.resistance (fun i j ↦ runV o d f n i j ω) =
      CNDPhysical.resistance (fun t a ↦ runProbability o d f t a ω) n := by
  unfold StatisticalMaps.resistance CNDPhysical.resistance
  rw [computed_inverse_eq_information o d f hR]
  rfl

theorem computed_radius_eq_actual (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) (H L R : ℝ) :
    StatisticalMaps.rawRadius H L R (run o d f n ω).1 =
      CNDPhysical.actualSaturatedRadius (fun t a ↦ runProbability o d f t a ω) n H L R := by
  funext i j
  unfold StatisticalMaps.rawRadius StatisticalMaps.rawPairRadius
    CNDPhysical.actualSaturatedRadius CNDPhysical.pairRadius
  change CNDPhysical.saturatedRadius R
    (2 * H * Real.sqrt (L * StatisticalMaps.resistance (fun i j ↦ runV o d f n i j ω) i j) +
      (4 * H * L + R * Fintype.card ι) * StatisticalMaps.resistance (fun i j ↦ runV o d f n i j ω) i j) = _
  rw [computed_resistance_eq_actual o d f hR]

theorem actualRadius_measurable (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (n : ℕ) (H L R : ℝ) :
    Measurable[ℱ n] (fun ω ↦ StatisticalMaps.rawRadius H L R (run o d f n ω).1) :=
  (StatisticalMaps.measurable_rawRadius H L R).comp
    (measurable_fst.comp (run_measurable o d f n))

theorem estimate_is_actual_inverse_statistic (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) (i : ι) :
    StatisticalMaps.estimate (run o d f n ω).1 i =
      ∑ j, CNDPhysical.inverseInformation (fun t a ↦ runProbability o d f t a ω) n i j *
        runS o d f n j ω := by
  unfold StatisticalMaps.estimate StatisticalMaps.tangentInverse
  change (∑ j, (StatisticalMaps.totalInverse (fun i j ↦ runV o d f n i j ω) i j -
    (Fintype.card ι : ℝ)⁻¹) * runS o d f n j ω) = _
  rw [computed_inverse_eq_information o d f hR]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [runS_sum_zero]
  ring

theorem estimate_unique_tangent_solution (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) :
    let p := fun t a ↦ runProbability o d f t a ω
    let S := fun i ↦ runS o d f n i ω
    let x := StatisticalMaps.estimate (run o d f n ω).1
    (∑ i, x i) = 0 ∧ CNDPhysical.tangentInformation p n x = S ∧
      (∀ y : ι → ℝ, (∑ i, y i) = 0 → CNDPhysical.tangentInformation p n y = S → y = x) := by
  have he : StatisticalMaps.estimate (run o d f n ω).1 =
      CNDPhysical.inverseInformation (fun t a ↦ runProbability o d f t a ω) n *ᵥ
        (fun i ↦ runS o d f n i ω) := by
    funext i
    exact estimate_is_actual_inverse_statistic o d f hR n ω i
  dsimp only
  rw [he]
  exact CNDPhysical.inverse_tangent_direction _ (fun t ↦ runProbability_simplex o d f t ω)
    n _ (runS_sum_zero o d f n ω)

end Part2.CNDProcess

end
