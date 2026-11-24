import staging.cnd20261024.payment.ActualPayment
import staging.cnd20261024.payment.FiniteFailure

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

theorem actualPayment_all_intervals
    (Q : Matrix ι η ℝ) (hQ : CNDInformation.TangentChart Q)
    (H Lc : ℝ) (hH : 0 ≤ H) (hLc : 0 ≤ Lc)
    (hrm : ∀ t i j, Measurable[ℱ t] (actualRadius h H Lc t i j)) (T : ℕ) (L : ℝ) :
    μ.real {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * L <
        intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} ≤
      (T : ℝ) ^ 2 * Real.exp (-L) := by
  let bad : Fin T × Fin T → Set Ω := fun uv => {ω |
    4 * actualQ h Q H Lc uv.1.val (uv.2.val + 1) ω + (4 * R / CNDPhysical.c0) * L <
      intervalSum (observablePayment h (actualRadius h H Lc)) uv.1.val (uv.2.val + 1) ω}
  have ht := finite_failure_union bad L (fun uv => actualPayment_interval_tail h Q hQ H Lc hH hLc hrm uv.1.val (uv.2.val + 1) L)
  have hsub : {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * L <
        intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} ⊆
      {ω | ∃ uv, ω ∈ bad uv} := by
    rintro ω ⟨u,n,hu,hn,hbad⟩
    refine ⟨(⟨u, by omega⟩,⟨n-1, by omega⟩), ?_⟩
    have hne : n - 1 + 1 = n := by omega
    simpa only [bad, hne] using hbad
  exact (measureReal_mono hsub).trans (by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using ht)

theorem actualPayment_global_delta
    (Q : Matrix ι η ℝ) (hQ : CNDInformation.TangentChart Q)
    (H Lc : ℝ) (hH : 0 ≤ H) (hLc : 0 ≤ Lc)
    (hrm : ∀ t i j, Measurable[ℱ t] (actualRadius h H Lc t i j))
    (T : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | 4 * actualQ h Q H Lc 0 T ω + (4 * R / CNDPhysical.c0) * Real.log (1 / δ) <
      intervalSum (observablePayment h (actualRadius h H Lc)) 0 T ω} ≤ δ := by
  have ht := actualPayment_interval_tail h Q hQ H Lc hH hLc hrm 0 T (Real.log (1 / δ))
  have he : Real.exp (-Real.log (1 / δ)) = δ := by
    simpa only [one_mul] using failure_log_identity (by norm_num : (0 : ℝ) < 1) hδ
  rwa [he] at ht

theorem actualPayment_all_intervals_delta
    (Q : Matrix ι η ℝ) (hQ : CNDInformation.TangentChart Q)
    (H Lc : ℝ) (hH : 0 ≤ H) (hLc : 0 ≤ Lc)
    (hrm : ∀ t i j, Measurable[ℱ t] (actualRadius h H Lc t i j))
    (T : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * Real.log ((T : ℝ) ^ 2 / δ) <
        intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} ≤ δ := by
  by_cases hT : T = 0
  · have heq : {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
        4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * Real.log ((T : ℝ) ^ 2 / δ) <
          intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨u,n,hu,hn,_⟩; omega
    rw [heq]; simpa only [measureReal_empty] using hδ.le
  have hTr : 0 < (T : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hT)
  have ht := actualPayment_all_intervals h Q hQ H Lc hH hLc hrm T (Real.log ((T : ℝ) ^ 2 / δ))
  rwa [failure_log_identity (pow_pos hTr 2) hδ] at ht

end Part2.CNDPayment
