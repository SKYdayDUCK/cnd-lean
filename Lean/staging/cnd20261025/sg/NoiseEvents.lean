import staging.cnd20261025.sg.NoiseTail

noncomputable section
open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators NNReal
set_option maxHeartbeats 1600000
namespace Part2.CNDSGMain
open CNDPayment
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D σ σe : ℝ}
variable (h : CNDProbability.SGModel ℱ μ θ R M D σ σe)

theorem noise_interval_tail (ν : ℝ≥0) (hν : (ν:ℝ)^2=σ^2+σe^2)
    (k : ι) (u n : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | (2*(ν:ℝ))*Real.sqrt (2*(n:ℝ)*L) < intervalSum (noiseDifference h k) u n ω} ≤ Real.exp (-L) :=
  interval_hoeffding (noiseDifference_measurable h k) (noiseDifference_exp_integrable h k)
    (fun n t => noiseDifference_conditional_mgf h ν hν k n t) (by positivity) u n hL
theorem noise_all_intervals (ν : ℝ≥0) (hν : (ν : ℝ)^2=σ^2+σe^2) (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ k : ι, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      (2 * (ν : ℝ)) * Real.sqrt (2 * (n : ℝ) * L) < intervalSum (noiseDifference h k) u n ω}
      ≤ (Fintype.card ι : ℝ) * (T : ℝ) ^ 2 * Real.exp (-L) := by
  let bad : ι × (Fin T × Fin T) → Set Ω := fun kuv => {ω |
    (2 * (ν : ℝ)) * Real.sqrt (2 * ((kuv.2.2.val + 1 : ℕ) : ℝ) * L) <
      intervalSum (noiseDifference h kuv.1) kuv.2.1.val (kuv.2.2.val + 1) ω}
  have ht := finite_failure_union bad L (fun kuv => noise_interval_tail h ν hν kuv.1 kuv.2.1.val (kuv.2.2.val + 1) hL)
  have hsub : {ω | ∃ k : ι, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      (2 * (ν : ℝ)) * Real.sqrt (2 * (n : ℝ) * L) < intervalSum (noiseDifference h k) u n ω} ⊆
      {ω | ∃ kuv, ω ∈ bad kuv} := by
    rintro ω ⟨k,u,n,hu,hn,hbad⟩
    refine ⟨(k,(⟨u, by omega⟩, ⟨n - 1, by omega⟩)), ?_⟩
    have hne : n - 1 + 1 = n := by omega
    simpa only [bad, hne] using hbad
  exact (measureReal_mono hsub).trans (by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two, mul_assoc] using ht)

theorem noise_all_intervals_delta (ν : ℝ≥0) (hν : (ν : ℝ)^2=σ^2+σe^2) (T : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | ∃ k : ι, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      (2 * (ν : ℝ)) * Real.sqrt (2 * (n : ℝ) * Real.log ((Fintype.card ι : ℝ) * (T : ℝ) ^ 2 / δ)) <
        intervalSum (noiseDifference h k) u n ω} ≤ δ := by
  by_cases hT : T = 0
  · have heq : {ω | ∃ k : ι, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
        (2 * (ν : ℝ)) * Real.sqrt (2 * (n : ℝ) * Real.log ((Fintype.card ι : ℝ) * (T : ℝ) ^ 2 / δ)) <
          intervalSum (noiseDifference h k) u n ω} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨k,u,n,hu,hn,_⟩; omega
    rw [heq]; simpa only [measureReal_empty] using hδ0.le
  have hTr : 1 ≤ (T : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
  have hKnat : 1 ≤ Fintype.card ι := Nat.one_le_of_lt Fintype.card_pos
  have hKr : 1 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hKnat
  have hT2 : 1 ≤ (T : ℝ) ^ 2 := by nlinarith
  have hcard : 1 ≤ (Fintype.card ι : ℝ) * (T : ℝ) ^ 2 := by
    simpa only [one_mul] using mul_le_mul hKr hT2 (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (Fintype.card ι : ℝ))
  have ht := noise_all_intervals h ν hν T (failure_log_pos hcard hδ0 hδ1)
  rw [failure_log_identity (by linarith : 0 < (Fintype.card ι : ℝ) * (T : ℝ) ^ 2) hδ0] at ht
  exact ht

end Part2.CNDSGMain

