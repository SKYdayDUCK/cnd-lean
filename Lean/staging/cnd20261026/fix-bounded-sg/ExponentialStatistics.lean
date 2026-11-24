import staging.cnd20261026.«fix-bounded-sg».ExponentialStochastic

/-! Statistics of the actual exponential recursion. The V/S identities,
inverse and radius depend on the computed p and observed feedback, not on
the algebra used to update expert weights. Shared with the SG extension. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators Matrix
set_option maxHeartbeats 1600000

namespace Part2.ExponentialStochastic
open CNDProcess
variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [Nonempty E]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀}
  (o : DecisionMaps ι) (d : ExpertData ι E) (prior : E → ℝ) (f : Feedback (ι := ι) ℱ)

def runV (n : ℕ) (i j : ι) (ω : Ω) : ℝ := (run o d prior f n ω).1.1 i j
def runS (n : ℕ) (i : ι) (ω : Ω) : ℝ := (run o d prior f n ω).1.2 i

theorem runV_succ (n : ℕ) (i j : ι) (ω : Ω) :
    runV o d prior f (n+1) i j ω = if d.R = 0 then runV o d prior f n i j ω else
      runV o d prior f n i j ω +
        CNDPhysical.covariance (fun a => runProbability o d prior f n a ω) i j := rfl

theorem runS_succ (n : ℕ) (i : ι) (ω : Ω) :
    runS o d prior f (n+1) i ω = if d.R = 0 then runS o d prior f n i ω else
      runS o d prior f n i ω +
        ((if f.action n ω = i then 1 else 0) - runProbability o d prior f n i ω) * f.residual n ω := rfl

theorem actual_information_identity (hR : d.R ≠ 0) (n : ℕ) (i j : ι) (ω : Ω) :
    runV o d prior f n i j ω = (if i=j then 1 else 0) - (Fintype.card ι : ℝ)⁻¹ +
      ∑ t ∈ range n, CNDPhysical.covariance (fun a => runProbability o d prior f t a ω) i j := by
  induction n with
  | zero => simp [runV, run, rawRun, initial, initialState]
  | succ n ih => rw [runV_succ, if_neg hR, ih, sum_range_succ]; ring

theorem actual_statistic_identity (hR : d.R ≠ 0) (n : ℕ) (i : ι) (ω : Ω) :
    runS o d prior f n i ω = ∑ t ∈ range n,
      ((if f.action t ω = i then 1 else 0) - runProbability o d prior f t i ω) * f.residual t ω := by
  induction n with
  | zero => simp [runS, run, rawRun, initial, initialState]
  | succ n ih => rw [runS_succ, if_neg hR, ih, sum_range_succ]

theorem runS_sum_zero (n : ℕ) (ω : Ω) : (∑ i, runS o d prior f n i ω) = 0 := by
  induction n with
  | zero => simp [runS, run, rawRun, initial, initialState]
  | succ n ih =>
    simp_rw [runS_succ]
    by_cases hz : d.R = 0
    · simp only [if_pos hz]; exact ih
    · simp only [if_neg hz, sum_add_distrib, ← sum_mul, sum_sub_distrib, ih]
      have hp := (runProbability_simplex o d prior f n ω).2
      simp [hp]

theorem regularized_runV_eq_information (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) :
    StatisticalMaps.regularized (fun i j => runV o d prior f n i j ω) =
      CNDPhysical.information (fun t a => runProbability o d prior f t a ω) n := by
  funext i j
  rw [StatisticalMaps.regularized, actual_information_identity o d prior f hR]
  simp only [CNDPhysical.information, Matrix.add_apply, Matrix.sum_apply, Matrix.one_apply]
  ring

theorem computed_inverse_eq_information (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) :
    StatisticalMaps.totalInverse (fun i j => runV o d prior f n i j ω) =
      CNDPhysical.inverseInformation (fun t a => runProbability o d prior f t a ω) n := by
  unfold StatisticalMaps.totalInverse CNDPhysical.inverseInformation
  rw [regularized_runV_eq_information o d prior f hR]

theorem computed_resistance_eq_actual (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) :
    StatisticalMaps.resistance (fun i j => runV o d prior f n i j ω) =
      CNDPhysical.resistance (fun t a => runProbability o d prior f t a ω) n := by
  unfold StatisticalMaps.resistance CNDPhysical.resistance
  rw [computed_inverse_eq_information o d prior f hR]
  rfl

theorem computed_radius_eq_actual (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) (H L R : ℝ) :
    StatisticalMaps.rawRadius H L R (run o d prior f n ω).1 =
      CNDPhysical.actualSaturatedRadius (fun t a => runProbability o d prior f t a ω) n H L R := by
  funext i j
  unfold StatisticalMaps.rawRadius StatisticalMaps.rawPairRadius
    CNDPhysical.actualSaturatedRadius CNDPhysical.pairRadius
  change CNDPhysical.saturatedRadius R
    (2 * H * Real.sqrt (L * StatisticalMaps.resistance (fun i j => runV o d prior f n i j ω) i j) +
      (4 * H * L + R * Fintype.card ι) * StatisticalMaps.resistance
        (fun i j => runV o d prior f n i j ω) i j) = _
  rw [computed_resistance_eq_actual o d prior f hR]

theorem computed_rawPairRadius_eq_actual (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) (H L R : ℝ) :
    StatisticalMaps.rawPairRadius H L R (run o d prior f n ω).1 =
      CNDPhysical.pairRadius (fun t a => runProbability o d prior f t a ω) n H L R := by
  funext i j
  unfold StatisticalMaps.rawPairRadius CNDPhysical.pairRadius
  change 2 * H * Real.sqrt (L * StatisticalMaps.resistance
      (fun i j => runV o d prior f n i j ω) i j) +
      (4 * H * L + R * Fintype.card ι) * StatisticalMaps.resistance
        (fun i j => runV o d prior f n i j ω) i j = _
  rw [computed_resistance_eq_actual o d prior f hR]

theorem estimate_is_actual_inverse_statistic (hR : d.R ≠ 0) (n : ℕ) (ω : Ω) (i : ι) :
    StatisticalMaps.estimate (run o d prior f n ω).1 i =
      ∑ j, CNDPhysical.inverseInformation (fun t a => runProbability o d prior f t a ω) n i j *
        runS o d prior f n j ω := by
  unfold StatisticalMaps.estimate StatisticalMaps.tangentInverse
  change (∑ j, (StatisticalMaps.totalInverse (fun i j => runV o d prior f n i j ω) i j -
    (Fintype.card ι : ℝ)⁻¹) * runS o d prior f n j ω) = _
  rw [computed_inverse_eq_information o d prior f hR]
  simp only [sub_mul, sum_sub_distrib, ← mul_sum]
  rw [runS_sum_zero]
  ring

section FiniteBounded
variable {θ : ι → ℝ} {R M D : ℝ} {T : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (h : CNDHorizon.BoundedInputs ℱ θ R M D T)
  (hm : FiniteLaws o d prior h (μ := μ))

theorem actualScoreSum_eq_runS (hR : d.R ≠ 0) (n : ℕ) (hn : n≤T) (ω : Ω) :
    CNDNet.actualScoreSum (model o d prior h hm) n ω =
      fun i => runS o d prior h.extend.feedback n i ω := by
  funext i
  rw [actual_statistic_identity o d prior h.extend.feedback hR]
  unfold CNDNet.actualScoreSum
  apply sum_congr rfl
  intro t ht
  have htT : t<T := lt_of_lt_of_le (mem_range.mp ht) hn
  simp only [model_action o d prior h hm htT, model_p o d prior h hm htT,
    model_drift o d prior h hm htT, model_error o d prior h hm htT]
  change CNDPhysical.score (runProbability o d prior h.extend.feedback t) θ
    (h.drift t) (h.error t) (h.action t) i ω =
    ((if h.extend.action t ω=i then 1 else 0)-runProbability o d prior h.extend.feedback t i ω) *
      h.extend.residual t ω
  rw [h.extend_action htT,h.extend_residual htT]
  change ((if h.action t ω = i then 1 else 0) - runProbability o d prior h.extend.feedback t i ω) *
    (θ (h.action t ω) + h.drift t ω - h.error t (h.action t ω) ω) =
    ((if h.action t ω = i then 1 else 0) - runProbability o d prior h.extend.feedback t i ω) * h.residual t ω
  dsimp only [CNDHorizon.BoundedInputs.residual,CNDHorizon.BoundedInputs.physical,
    CNDHorizon.BoundedInputs.broadcast]
  ring

theorem computed_estimate_eq_actualEstimator (hR : d.R ≠ 0) (n : ℕ) (hn : n≤T) (ω : Ω) :
    StatisticalMaps.estimate (run o d prior h.extend.feedback n ω).1 =
      CNDNet.actualEstimator (model o d prior h hm) n ω := by
  rw [CNDNet.actualEstimator,actualScoreSum_eq_runS o d prior h hm hR n hn ω]
  have hi := CNDHorizon.information_prefix
    (fun t a => (model o d prior h hm).p t a ω)
    (fun t a => runProbability o d prior h.extend.feedback t a ω) n
    (fun t ht => congrArg (fun p => fun a => p a ω)
      (model_p o d prior h hm (lt_of_lt_of_le ht hn)))
  simp only [CNDPhysical.inverseInformation,hi]
  funext i
  exact estimate_is_actual_inverse_statistic o d prior h.extend.feedback hR n ω i
end FiniteBounded

end Part2.ExponentialStochastic
