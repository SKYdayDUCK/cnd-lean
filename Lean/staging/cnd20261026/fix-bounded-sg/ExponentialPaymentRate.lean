import staging.cnd20261026.«fix-bounded-sg».BoundedRate

/-! # Explicit bound for the canonical payment envelope

The argument uses the execution probabilities on this model. The
matrix information bound is independent of the expert weight update.
-/

namespace Part2.ExponentialPaymentRate

noncomputable section

open MeasureTheory Finset CNDInformation CNDHorizon.BoundedRate

variable {K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω}

private theorem canonical_payment_branches (h : CNDProbability.M1Model ℱ μ θ R M D)
    (H L Λ δg δl : ℝ) (hΛ : 1 ≤ Λ) (hF : paperF K T ≤ Λ)
    (ω : Ω) :
    let P := CNDPayment.paymentEnvelope h (canonicalChart (Fin K)) H L T 0 T δg δl ω
    P ≤ (4 * R / CNDPhysical.c0) * (T : ℝ) ∧
      ∃ d : ℝ, 0 ≤ d ∧ d ≤ (K : ℝ) * Λ ∧
        P ≤ 4 * ((4 * Real.sqrt 3 / CNDPhysical.c0) * H * Real.sqrt ((T : ℝ) * L * d) +
          (6 / CNDPhysical.c0) * (4 * H * L + R * (K : ℝ)) * d) +
          (4 * R / CNDPhysical.c0) * globalLog δg := by
  let Q := canonicalChart (Fin K)
  let P := CNDPayment.paymentEnvelope h Q H L T 0 T δg δl ω
  have hcap : P ≤ (4 * R / CNDPhysical.c0) * (T : ℝ) := min_le_left _ _
  refine ⟨hcap, ?_⟩
  by_cases hR : R = 0
  · refine ⟨0, le_rfl, by positivity, ?_⟩
    simpa [hR] using hcap
  let p : ℕ → Fin K → ℝ := fun t i => h.p t i ω
  have hp (t : ℕ) : p t ∈ CND.simplex := ⟨h.p_nonneg t ω, h.p_sum t ω⟩
  let d := coordinateLogdet Q p (0 + T) - coordinateLogdet Q p 0
  have hd : 0 ≤ d := by
    have hinfo := tangent_actual_resistance_information_budget Q
      canonicalChart_is_tangentChart p hp 0 T
    have hpos : 0 ≤ ∑ t ∈ range T, pairSum (fun i j =>
        p (0 + t) i * p (0 + t) j * CNDPhysical.resistance p (0 + t) i j) := by
      apply sum_nonneg
      intro t _
      apply sum_nonneg
      intro i _
      apply sum_nonneg
      intro j _
      split_ifs
      · exact mul_nonneg (mul_nonneg ((hp _).1 _) ((hp _).1 _))
          (CNDPhysical.actual_resistance_nonneg p hp _ _ _)
      · exact le_rfl
    change _ ≤ (3 / 2 : ℝ) * d at hinfo
    linarith
  have hdΛ : d ≤ (K : ℝ) * Λ := by
    have hF0 : 0 ≤ paperF K T :=
      Real.log_nonneg (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg T) (Nat.cast_nonneg K)))
    calc
      _ ≤ ((K : ℝ) - 1) * paperF K T := by
        simpa only [d, Q, Fintype.card_fin, paperF] using canonical_logdet_interval_upper p hp 0 T
      _ ≤ (K : ℝ) * paperF K T := mul_le_mul_of_nonneg_right (by linarith) hF0
      _ ≤ (K : ℝ) * Λ := mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg K)
  have hcurve : P ≤ 4 * CNDPayment.actualQ h Q H L 0 T ω +
      (4 * R / CNDPhysical.c0) * globalLog δg :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hq : CNDPayment.actualQ h Q H L 0 T ω =
      (4 * Real.sqrt 3 / CNDPhysical.c0) * H * Real.sqrt ((T : ℝ) * L * d) +
      (6 / CNDPhysical.c0) * (4 * H * L + R * (K : ℝ)) * d := by
    simp only [CNDPayment.actualQ, CNDInformation.branchedQ, if_neg hR,
      CNDInformation.actualQ, Fintype.card_fin, p, d]
  rw [hq] at hcurve
  exact ⟨d, hd, hdΛ, hcurve⟩

/-- The cap and global information branch give a private-rate bound for
the actual execution probabilities of the bounded feedback model. -/
theorem canonical_payment_envelope_le (h : CNDProbability.M1Model ℱ μ θ R M D)
    (H L Λ δg δl : ℝ) (hK : 2 ≤ K) (hT : 1 ≤ T) (hRH : R ≤ H)
    (hΛ : 1 ≤ Λ) (hL : 0 ≤ L) (hLΛ : L ≤ (K : ℝ) * Λ)
    (hF : paperF K T ≤ Λ) (hg : 0 ≤ globalLog δg) (hgΛ : globalLog δg ≤ Λ)
    (ω : Ω) :
    CNDPayment.paymentEnvelope h (canonicalChart (Fin K)) H L T 0 T δg δl ω ≤
      (156 / CNDPhysical.c0) * H * (K : ℝ) * Real.sqrt (T : ℝ) * Λ ^ 2 := by
  obtain ⟨hcap, d, hd, hdΛ, hcurve⟩ :=
    canonical_payment_branches h H L Λ δg δl hΛ hF ω
  exact CNDRateAbsorption.actual_budget_uniform_rate _ H R CNDPhysical.c0
    (K : ℝ) (T : ℝ) Λ L d (globalLog δg) h.R_nonneg hRH CNDPhysical.c0_pos
    (by exact_mod_cast (show 1 ≤ K by omega)) (by exact_mod_cast hT)
    hΛ hL hd hLΛ hdΛ hg hgΛ hcap hcurve

/-- The SG confidence coefficient is scaled by four. The information
increment keeps its original dimension bound. -/
theorem sg_payment_envelope_le (h : CNDProbability.M1Model ℱ μ θ R M D)
    (H L Λ δg δl : ℝ) (hK : 2 ≤ K) (hT : 1 ≤ T) (hRH : R ≤ H)
    (hΛ : 1 ≤ Λ) (hL : 0 ≤ L) (hLΛ : L ≤ 4 * (K : ℝ) * Λ)
    (hF : paperF K T ≤ Λ) (hg : 0 ≤ globalLog δg) (hgΛ : globalLog δg ≤ Λ)
    (ω : Ω) :
    CNDPayment.paymentEnvelope h (canonicalChart (Fin K)) H L T 0 T δg δl ω ≤
      (468 / CNDPhysical.c0) * H * (K : ℝ) * Real.sqrt (T : ℝ) * Λ ^ 2 := by
  obtain ⟨hcap, d, hd, hdΛ, hcurve⟩ :=
    canonical_payment_branches h H L Λ δg δl hΛ hF ω
  exact CNDRateAbsorption.actual_budget_sg_rate _ H R CNDPhysical.c0
    (K : ℝ) (T : ℝ) Λ L d (globalLog δg) h.R_nonneg hRH CNDPhysical.c0_pos
    (by exact_mod_cast (show 1 ≤ K by omega)) (by exact_mod_cast hT)
    hΛ hL hd hLΛ hdΛ hg hgΛ hcap hcurve

end

end Part2.ExponentialPaymentRate
