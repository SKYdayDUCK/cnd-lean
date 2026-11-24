import staging.cnd20261024.payment.PaymentEvents

noncomputable section
open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators

namespace Part2.CNDPayment
variable {Ω ι η : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype η] [DecidableEq η]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}
variable (h : CNDProbability.M1Model ℱ μ θ R M D)

theorem nonnegative_interval_le_global (X : ℕ → Ω → ℝ)
    (hX : ∀ t ω, 0 ≤ X t ω) {u n T : ℕ} (hu : u + n ≤ T) (ω : Ω) :
    intervalSum X u n ω ≤ intervalSum X 0 T ω := by
  have hpre : 0 ≤ ∑ t ∈ range u, X t ω := sum_nonneg fun t _ => hX t ω
  have hsplit := sum_range_add (fun t => X t ω) u n
  have hsub : (∑ t ∈ range (u + n), X t ω) ≤ ∑ t ∈ range T, X t ω :=
    sum_le_sum_of_subset_of_nonneg (range_mono hu) (fun t _ _ => hX t ω)
  simp only [intervalSum, Nat.zero_add]
  change (∑ t ∈ range n, X (u + t) ω) ≤ _
  rw [hsplit] at hsub
  linarith

/-- The original three-way envelope retains the deterministic cap and the
nonnegative global budget, on the original probability space. -/
def paymentEnvelope (Q : Matrix ι η ℝ) (H Lc : ℝ) (T u n : ℕ)
    (δg δl : ℝ) (ω : Ω) : ℝ :=
  min ((4 * R / CNDPhysical.c0) * (n : ℝ))
    (min (4 * actualQ h Q H Lc 0 T ω + (4 * R / CNDPhysical.c0) * Real.log (1 / δg))
      (4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * Real.log ((T : ℝ) ^ 2 / δl)))

theorem actualPayment_envelope_delta
    (Q : Matrix ι η ℝ) (hQ : CNDInformation.TangentChart Q)
    (H Lc : ℝ) (hH : 0 ≤ H) (hLc : 0 ≤ Lc)
    (hrm : ∀ t i j, Measurable[ℱ t] (actualRadius h H Lc t i j))
    (T : ℕ) {δg δl : ℝ} (hδg : 0 < δg) (hδl : 0 < δl) :
    μ.real {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      paymentEnvelope h Q H Lc T u n δg δl ω <
        intervalSum (observablePayment h (actualRadius h H Lc)) u n ω} ≤ δg + δl := by
  let X := observablePayment h (actualRadius h H Lc)
  let G := {ω | 4 * actualQ h Q H Lc 0 T ω + (4 * R / CNDPhysical.c0) * Real.log (1 / δg) < intervalSum X 0 T ω}
  let L := {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
    4 * actualQ h Q H Lc u n ω + (4 * R / CNDPhysical.c0) * Real.log ((T : ℝ) ^ 2 / δl) < intervalSum X u n ω}
  have hb := observablePayment_bounds h (actualRadius h H Lc) (4 * R / CNDPhysical.c0)
    (actualRadius_bounds h H Lc hH hLc)
  have hsub : {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      paymentEnvelope h Q H Lc T u n δg δl ω < intervalSum X u n ω} ⊆ G ∪ L := by
    rintro ω ⟨u,n,hu,hn,hbad⟩
    by_cases hg : ω ∈ G
    · exact Or.inl hg
    right
    refine ⟨u,n,hu,hn,?_⟩
    have hcap : intervalSum X u n ω ≤ (4 * R / CNDPhysical.c0) * (n : ℝ) := by
      calc
        _ ≤ ∑ _t ∈ range n, (4 * R / CNDPhysical.c0) := sum_le_sum fun t _ => (hb (u+t) ω).2
        _ = _ := by simp [nsmul_eq_mul, mul_comm]
    have hglobal := nonnegative_interval_le_global X (fun t ω => (hb t ω).1) hu ω
    have hgb : intervalSum X u n ω ≤ 4 * actualQ h Q H Lc 0 T ω + (4 * R / CNDPhysical.c0) * Real.log (1 / δg) :=
      hglobal.trans (le_of_not_gt hg)
    unfold paymentEnvelope at hbad
    rcases (min_lt_iff.mp hbad) with hc | hm
    · exact False.elim (not_lt_of_ge hcap hc)
    rcases min_lt_iff.mp hm with hgg | hll
    · exact False.elim (not_lt_of_ge hgb hgg)
    · exact hll
  apply (measureReal_mono hsub).trans
  exact (measureReal_union_le G L).trans (add_le_add
    (actualPayment_global_delta h Q hQ H Lc hH hLc hrm T hδg)
    (actualPayment_all_intervals_delta h Q hQ H Lc hH hLc hrm T hδl))

end Part2.CNDPayment
