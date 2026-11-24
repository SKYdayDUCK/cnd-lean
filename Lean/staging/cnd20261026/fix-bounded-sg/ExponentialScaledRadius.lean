import staging.cnd20261024.payment.Closure
import OriginalRadiusBridge

/-! Scaling the argument of the saturated radius preserves its canonical
payment upper bound on the same probability path. No confidence-success
assumption, expert update rule or new execution distribution is used. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators ProbabilityTheory

namespace Part2.ExponentialScaledRadius

theorem saturatedRadius_mono {R x y : ℝ} (hR : 0 ≤ R) (hxy : x ≤ y) :
    CNDPhysical.saturatedRadius R x ≤ CNDPhysical.saturatedRadius R y := by
  by_cases hz : R = 0
  · simp [hz, CNDPhysical.saturatedRadius]
  · have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
    have he : Real.exp (-(y / R)) ≤ Real.exp (-(x / R)) :=
      Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right hxy hR))
    unfold CNDPhysical.saturatedRadius
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left he 1)
      (div_nonneg (by linarith) CNDPhysical.c0_pos.le)

theorem saturatedRadius_nonneg {R x : ℝ} (hR : 0 ≤ R) (hx : 0 ≤ x) :
    0 ≤ CNDPhysical.saturatedRadius R x := by
  simpa [CNDPhysical.saturatedRadius] using
    (saturatedRadius_mono hR hx :
      CNDPhysical.saturatedRadius R 0 ≤ CNDPhysical.saturatedRadius R x)

/-- The scale is inside the exponential, exactly as in the numerical rule. -/
theorem saturatedRadius_scaled_bounds {R x s : ℝ}
    (hR : 0 ≤ R) (hx : 0 ≤ x) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ CNDPhysical.saturatedRadius R (s * x) ∧
    CNDPhysical.saturatedRadius R (s * x) ≤ CNDPhysical.saturatedRadius R x := by
  exact ⟨saturatedRadius_nonneg hR (mul_nonneg hs hx),
    saturatedRadius_mono hR (by nlinarith)⟩

variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}
  (h : CNDProbability.M1Model ℱ μ θ R M D)

def scaledRadius (H L s : ℝ) (t : ℕ) (i j : ι) (ω : Ω) : ℝ :=
  CNDPhysical.saturatedRadius R
    (s * CNDPhysical.pairRadius (fun n a => h.p n a ω) t H L R i j)

theorem scaledRadius_bounds (H L s : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (t : ℕ) (i j : ι) (ω : Ω) :
    0 ≤ scaledRadius h H L s t i j ω ∧
    scaledRadius h H L s t i j ω ≤ CNDPayment.actualRadius h H L t i j ω := by
  exact saturatedRadius_scaled_bounds h.R_nonneg
    (CNDPhysical.pairRadius_nonneg (fun n a => h.p n a ω)
      (fun n => ⟨h.p_nonneg n ω, h.p_sum n ω⟩) t H L R hH hL h.R_nonneg i j)
    hs hs1

/-- The actual scaled radius remains conditionally negative for every
nonnegative scale; the scale need not be at most one for this geometry. -/
theorem scaledRadius_isCND (H L s : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hs : 0 ≤ s) (t : ℕ) (ω : Ω) :
    CND.IsCND (fun i j => scaledRadius h H L s t i j ω) := by
  have hR : 0 ≤ R := h.R_nonneg
  have hp (n : ℕ) : (fun i => h.p n i ω) ∈ CND.simplex :=
    ⟨h.p_nonneg n ω, h.p_sum n ω⟩
  have hrho : CND.IsCND (CNDPhysical.pairRadius (fun n i => h.p n i ω) t H L R) := by
    have hb : 0 ≤ 4 * H * L + R * (Fintype.card ι : ℝ) := by positivity
    have hc := CNDSaturation.sqrt_linear_isCND
      (CNDPhysical.resistance (fun n i => h.p n i ω) t)
      (CNDPhysical.actual_resistance_isCND _ hp t)
      (2 * H * Real.sqrt L) (4 * H * L + R * Fintype.card ι)
      (by positivity) hb
    convert hc using 1
    funext i j
    simp only [CNDPhysical.pairRadius, Real.sqrt_mul hL]
    ring
  have hc := CNDSaturation.exponential_saturation_isCND _ hrho
    (2 * R / CNDPhysical.c0) (s / R)
    (div_nonneg (by linarith [h.R_nonneg]) CNDPhysical.c0_pos.le)
    (div_nonneg hs h.R_nonneg)
  convert hc using 1
  funext i j
  simp only [scaledRadius, CNDPhysical.saturatedRadius]
  congr 2
  ring

theorem observablePayment_mono
    (r r' : ℕ → ι → ι → Ω → ℝ)
    (hr : ∀ t i j ω, r t i j ω ≤ r' t i j ω) (t : ℕ) (ω : Ω) :
    CNDPayment.observablePayment h r t ω ≤ CNDPayment.observablePayment h r' t ω := by
  unfold CNDPayment.observablePayment CNDPayment.paymentAt CNDPayment.rowMean
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hr t (h.action t ω) j ω) (h.p_nonneg t ω j)

/-- Transfer the original private payment envelope to an entrywise smaller
actual radius, without changing the original probability space or p. -/
theorem dominatedPayment_envelope_delta
    (r : ℕ → ι → ι → Ω → ℝ) (H Lc : ℝ)
    (hH : 0 ≤ H) (hLc : 0 ≤ Lc)
    (hr : ∀ t i j ω, r t i j ω ≤ CNDPayment.actualRadius h H Lc t i j ω)
    (T : ℕ) {δg δl : ℝ} (hδg : 0 < δg) (hδl : 0 < δl) :
    μ.real {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      CNDPayment.paymentEnvelope h (CNDInformation.canonicalChart ι) H Lc T u n δg δl ω <
        CNDPayment.intervalSum (CNDPayment.observablePayment h r) u n ω} ≤ δg + δl := by
  apply le_trans (measureReal_mono ?_)
    (CNDPayment.canonicalPayment_envelope_delta h H Lc hH hLc T hδg hδl)
  intro ω hω
  obtain ⟨u,n,hu,hn,hbad⟩ := hω
  refine ⟨u,n,hu,hn,lt_of_lt_of_le hbad ?_⟩
  unfold CNDPayment.intervalSum
  apply sum_le_sum
  intro t _
  exact observablePayment_mono h r (CNDPayment.actualRadius h H Lc) hr (u+t) ω

theorem scaledPayment_envelope_delta (H Lc s : ℝ)
    (hH : 0 ≤ H) (hLc : 0 ≤ Lc) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (T : ℕ) {δg δl : ℝ} (hδg : 0 < δg) (hδl : 0 < δl) :
    μ.real {ω | ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
      CNDPayment.paymentEnvelope h (CNDInformation.canonicalChart ι) H Lc T u n δg δl ω <
        CNDPayment.intervalSum
          (CNDPayment.observablePayment h (scaledRadius h H Lc s)) u n ω} ≤ δg + δl := by
  exact dominatedPayment_envelope_delta h _ H Lc hH hLc
    (fun t i j ω => (scaledRadius_bounds h H Lc s hH hLc hs hs1 t i j ω).2)
    T hδg hδl

#print axioms saturatedRadius_mono
#print axioms saturatedRadius_scaled_bounds
#print axioms scaledRadius_bounds
#print axioms scaledRadius_isCND
#print axioms observablePayment_mono
#print axioms dominatedPayment_envelope_delta
#print axioms scaledPayment_envelope_delta
end Part2.ExponentialScaledRadius
