import staging.cnd20261024.payment.IntervalAzuma
import staging.cnd20261024.payment.PublicSampling
import staging.cnd20261024.payment.EncodingDifference
import staging.cnd20261024.payment.FiniteFailure

noncomputable section
open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators
set_option maxHeartbeats 800000

namespace Part2.CNDPayment
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}
variable (h : CNDProbability.M1Model ℱ μ θ R M D) (l : ℕ → ι → Ω → ℝ)

def actualPublicResidual (n : ℕ) (ω : Ω) : ℝ :=
  l n (h.action n ω) ω - ∑ a, h.p n a ω * l n a ω

theorem public_interval_tail {W : ℝ} (hW : 0 ≤ W)
    (hlm : ∀ n a, Measurable[h.encoded n] (l n a))
    (hspan : ∀ n ω i j, 0 < h.p n i ω → 0 < h.p n j ω → |l n i ω - l n j ω| ≤ 2 * W)
    (u n : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | W * Real.sqrt (2 * (n : ℝ) * L) < intervalSum (actualPublicResidual h l) u n ω}
      ≤ Real.exp (-L) := by
  have ht := interval_hoeffding
    (publicResidual_measurable h l hlm) (publicResidual_bound h l hW hspan)
    (fun n t => (publicResidual_conditional_mgf h l hW hlm hspan n t).2) hW u n hL
  have heq : intervalSum (publicResidual h l) u n =ᵐ[μ] intervalSum (actualPublicResidual h l) u n := by
    filter_upwards [ae_all_iff.mpr (publicResidual_eq_actual h l)] with ω hω
    apply Finset.sum_congr rfl
    intro t _
    exact hω (u + t)
  have hs : {ω | W * Real.sqrt (2 * (n : ℝ) * L) < intervalSum (actualPublicResidual h l) u n ω} =ᵐ[μ]
      {ω | W * Real.sqrt (2 * (n : ℝ) * L) < intervalSum (publicResidual h l) u n ω} := by
    filter_upwards [heq] with ω hω
    change (_ < _) = (_ < _)
    rw [hω]
  rwa [← measureReal_congr hs] at ht

theorem encoding_interval_tail (k : ι) (u n : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | (2 * D) * Real.sqrt (2 * (n : ℝ) * L) < intervalSum (encodingDifference h k) u n ω}
      ≤ Real.exp (-L) :=
  interval_hoeffding (encodingDifference_measurable h k) (encodingDifference_bound h k)
    (fun n t => (encodingDifference_conditional_mgf h k n t).2)
    (by linarith [h.D_nonneg]) u n hL

/-- There are at most T² actual nonempty intervals; no path comparator union. -/
theorem public_all_intervals {W : ℝ} (hW : 0 ≤ W)
    (hlm : ∀ n a, Measurable[h.encoded n] (l n a))
    (hspan : ∀ n ω i j, 0 < h.p n i ω → 0 < h.p n j ω → |l n i ω - l n j ω| ≤ 2 * W)
    (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      W * Real.sqrt (2 * (n : ℝ) * L) < intervalSum (actualPublicResidual h l) u n ω}
      ≤ (T : ℝ) ^ 2 * Real.exp (-L) := by
  let bad : Fin T × Fin T → Set Ω := fun uv => {ω |
    W * Real.sqrt (2 * ((uv.2.val + 1 : ℕ) : ℝ) * L) <
      intervalSum (actualPublicResidual h l) uv.1.val (uv.2.val + 1) ω}
  have ht := finite_failure_union bad L (fun uv => public_interval_tail h l hW hlm hspan uv.1.val (uv.2.val + 1) hL)
  have hsub : {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      W * Real.sqrt (2 * (n : ℝ) * L) < intervalSum (actualPublicResidual h l) u n ω} ⊆
      {ω | ∃ uv, ω ∈ bad uv} := by
    rintro ω ⟨u,n,hu,hn,hbad⟩
    refine ⟨(⟨u, by omega⟩, ⟨n - 1, by omega⟩), ?_⟩
    have hne : n - 1 + 1 = n := by omega
    simpa only [bad, hne] using hbad
  exact (measureReal_mono hsub).trans (by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using ht)

theorem encoding_all_intervals (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ k : ι, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      (2 * D) * Real.sqrt (2 * (n : ℝ) * L) < intervalSum (encodingDifference h k) u n ω}
      ≤ (Fintype.card ι : ℝ) * (T : ℝ) ^ 2 * Real.exp (-L) := by
  let bad : ι × (Fin T × Fin T) → Set Ω := fun kuv => {ω |
    (2 * D) * Real.sqrt (2 * ((kuv.2.2.val + 1 : ℕ) : ℝ) * L) <
      intervalSum (encodingDifference h kuv.1) kuv.2.1.val (kuv.2.2.val + 1) ω}
  have ht := finite_failure_union bad L (fun kuv => encoding_interval_tail h kuv.1 kuv.2.1.val (kuv.2.2.val + 1) hL)
  have hsub : {ω | ∃ k : ι, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      (2 * D) * Real.sqrt (2 * (n : ℝ) * L) < intervalSum (encodingDifference h k) u n ω} ⊆
      {ω | ∃ kuv, ω ∈ bad kuv} := by
    rintro ω ⟨k,u,n,hu,hn,hbad⟩
    refine ⟨(k,(⟨u, by omega⟩, ⟨n - 1, by omega⟩)), ?_⟩
    have hne : n - 1 + 1 = n := by omega
    simpa only [bad, hne] using hbad
  exact (measureReal_mono hsub).trans (by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two, mul_assoc] using ht)

theorem public_all_intervals_delta {W : ℝ} (hW : 0 ≤ W)
    (hlm : ∀ n a, Measurable[h.encoded n] (l n a))
    (hspan : ∀ n ω i j, 0 < h.p n i ω → 0 < h.p n j ω → |l n i ω - l n j ω| ≤ 2 * W)
    (T : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      W * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ) ^ 2 / δ)) <
        intervalSum (actualPublicResidual h l) u n ω} ≤ δ := by
  by_cases hT : T = 0
  · have heq : {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
        W * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ) ^ 2 / δ)) <
          intervalSum (actualPublicResidual h l) u n ω} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨u,n,hu,hn,_⟩; omega
    rw [heq]; simpa only [measureReal_empty] using hδ0.le
  have hTr : 1 ≤ (T : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
  have hcard : 1 ≤ (T : ℝ) ^ 2 := by nlinarith
  have ht := public_all_intervals h l hW hlm hspan T (failure_log_pos hcard hδ0 hδ1)
  rw [failure_log_identity (by linarith : 0 < (T : ℝ) ^ 2) hδ0] at ht
  exact ht

theorem encoding_all_intervals_delta (T : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | ∃ k : ι, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      (2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((Fintype.card ι : ℝ) * (T : ℝ) ^ 2 / δ)) <
        intervalSum (encodingDifference h k) u n ω} ≤ δ := by
  by_cases hT : T = 0
  · have heq : {ω | ∃ k : ι, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
        (2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((Fintype.card ι : ℝ) * (T : ℝ) ^ 2 / δ)) <
          intervalSum (encodingDifference h k) u n ω} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨k,u,n,hu,hn,_⟩; omega
    rw [heq]; simpa only [measureReal_empty] using hδ0.le
  have hTr : 1 ≤ (T : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
  have hKnat : 1 ≤ Fintype.card ι := Nat.one_le_of_lt Fintype.card_pos
  have hKr : 1 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hKnat
  have hT2 : 1 ≤ (T : ℝ) ^ 2 := by nlinarith
  have hcard : 1 ≤ (Fintype.card ι : ℝ) * (T : ℝ) ^ 2 := by
    simpa only [one_mul] using mul_le_mul hKr hT2 (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (Fintype.card ι : ℝ))
  have ht := encoding_all_intervals h T (failure_log_pos hcard hδ0 hδ1)
  rw [failure_log_identity (by linarith : 0 < (Fintype.card ι : ℝ) * (T : ℝ) ^ 2) hδ0] at ht
  exact ht

end Part2.CNDPayment
