import staging.cnd20261024.payment.Closure
import staging.cnd20261024.process.ActualModel
import staging.cnd20261026.«fix-bounded-sg».BoundedModel

/-! The original public loss is computed from the actual canonical run.
Only primitive public-cost span is assumed; no loss, center, MGF, or tail
oracle is introduced. No absolute public baseline is bounded or integrated. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
set_option maxHeartbeats 1000000

namespace Part2.CNDHorizon.BoundedPublic
open CNDProcess
variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}

theorem public_width_nonneg (h : PotentialInputs ℱ θ R M D) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ B + 2 * D := by linarith [h.D_nonneg]

def actualPublicLoss (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B)
    (t : ℕ) (i : Fin K) (ω : Ω) : ℝ :=
  let o := concreteMaps (K := K) (R + M + D) L R (B + 2 * D) h.R_nonneg (public_width_nonneg h hB)
  let a := treeData d K (B + 2 * D) R
  processLoss o a t (run o a h.feedback t ω) (h.broadcast t ω) i

/-- Primitive public-cost span and the actual bounded potential errors imply
the original broadcast span W=B+2D, even with a nonintegrable common shift. -/
theorem actual_broadcast_span (h : PotentialInputs ℱ θ R M D) (B : ℝ)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    {t : ℕ} (ht : t < T) (ω : Ω) (i j : Fin K) :
    h.broadcast t ω j - h.broadcast t ω i ≤ B + 2 * D := by
  have hi := abs_le.mp (h.error_bound t i ω)
  have hj := abs_le.mp (h.error_bound t j ω)
  have hcost := hc t ht ω i j
  unfold PotentialInputs.broadcast
  linarith

theorem actualPublicLoss_encoded_measurable
    (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B) (t : ℕ) (i : Fin K) :
    Measurable[h.encoded t] (actualPublicLoss (d := d) h B L hB t i) := by
  let o := concreteMaps (K := K) (R + M + D) L R (B + 2 * D) h.R_nonneg (public_width_nonneg h hB)
  let a := treeData d K (B + 2 * D) R
  have hp : Measurable[h.encoded t] (fun ω => proxy o a t (run o a h.feedback t ω) i) :=
    (proxy_measurable (m := ℱ t) (run_measurable o a h.feedback t) o a t i).mono
      (show ℱ t ≤ h.encoded t from (h.past_le_pre t).trans le_sup_left) le_rfl
  have hb := (measurable_pi_apply i).comp (h.potential_broadcast_measurable t)
  exact hp.add hb

/-- The actual suggestion is a simplex point, including the W=0 branch.
Positive width uses the already proved actual Prod invariant, not a q field. -/
theorem actual_suggestion_simplex_closed
    (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hK : 2 ≤ K) (hT : T ≤ 2 ^ d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    {t : ℕ} (ht : t < T) (ω : Ω) :
    suggestion (treeData d K (B + 2 * D) R) t
      (run (concreteMaps (K := K) (R + M + D) L R (B + 2 * D) h.R_nonneg (public_width_nonneg h hB))
        (treeData d K (B + 2 * D) R) h.feedback t ω) ∈ CND.simplex := by
  have hW := public_width_nonneg h hB
  by_cases hz : B + 2 * D = 0
  · constructor
    · intro i
      simpa [suggestion, treeData, hz] using
        (inv_nonneg.mpr (Nat.cast_nonneg K) : 0 ≤ (K : ℝ)⁻¹)
    · have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
      simpa [suggestion, treeData, hz] using mul_inv_cancel₀ hKr
  · exact actual_suggestion_simplex hK hT (R + M + D) L R (B + 2 * D)
      (by linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg]) hL h.R_nonneg
      (lt_of_le_of_ne hW (Ne.symm hz)) h.feedback ω
      (fun t ht i j => actual_broadcast_span h B hc ht ω i j) ht

/-- The original actual loss has span 2W on the actual positive support.
The canonical minimizer, CND radius and actual q invariant are all derived. -/
theorem actual_public_geometry
    (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hK : 2 ≤ K) (hT : T ≤ 2 ^ d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    {t : ℕ} (ht : t < T) (ω : Ω) :
    let o := concreteMaps (K := K) (R + M + D) L R (B + 2 * D) h.R_nonneg (public_width_nonneg h hB)
    let a := treeData d K (B + 2 * D) R
    suggestion a t (run o a h.feedback t ω) ∈ CND.simplex ∧
    ∀ i j, 0 < runProbability o a h.feedback t i ω →
      0 < runProbability o a h.feedback t j ω →
      |actualPublicLoss (d := d) h B L hB t i ω - actualPublicLoss (d := d) h B L hB t j ω| ≤
        2 * (B + 2 * D) := by
  let o := concreteMaps (K := K) (R + M + D) L R (B + 2 * D) h.R_nonneg (public_width_nonneg h hB)
  let a := treeData d K (B + 2 * D) R
  let s := run o a h.feedback t ω
  have hr := concrete_radius_isCND (R + M + D) L R (B + 2 * D)
    (by linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg]) hL h.R_nonneg
    (public_width_nonneg h hB) a rfl h.feedback t ω
  have hp := runProbability_simplex o a h.feedback t ω
  have hmin := extendedProx_minimizes (B + 2 * D) (public_width_nonneg h hB)
    (confidence o a s, (radius o a s, suggestion a t s)) hr
  refine ⟨actual_suggestion_simplex_closed h B L hB hL hK hT hc ht ω, ?_⟩
  intro i j hi hj
  exact CNDMatrixProx.minimizer_public_support_span (confidence o a s) (radius o a s)
    (suggestion a t s) (probability o a t s) (h.broadcast t ω) (B + 2 * D)
    hr (public_width_nonneg h hB) hp hmin
    (fun i j => actual_broadcast_span h B hc ht ω i j) i j hi hj

/-- Extension by zero after the specified horizon avoids imposing any public
span or Prod invariant beyond the original theorem's time horizon. -/
def horizonPublicLoss (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B)
    (T t : ℕ) (i : Fin K) (ω : Ω) : ℝ :=
  if t < T then actualPublicLoss (d := d) h B L hB t i ω else 0

theorem horizonPublicLoss_measurable
    (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B) (T t : ℕ) (i : Fin K) :
    Measurable[h.encoded t] (horizonPublicLoss (d := d) h B L hB T t i) := by
  unfold horizonPublicLoss
  split_ifs
  · exact actualPublicLoss_encoded_measurable h B L hB t i
  · exact measurable_const

theorem horizonPublicLoss_span
    (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hK : 2 ≤ K) (hT : T ≤ 2 ^ d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    (t : ℕ) (ω : Ω) (i j : Fin K)
    (hi : 0 < runProbability
      (concreteMaps (K := K) (R + M + D) L R (B + 2 * D) h.R_nonneg (public_width_nonneg h hB))
      (treeData d K (B + 2 * D) R) h.feedback t i ω)
    (hj : 0 < runProbability
      (concreteMaps (K := K) (R + M + D) L R (B + 2 * D) h.R_nonneg (public_width_nonneg h hB))
      (treeData d K (B + 2 * D) R) h.feedback t j ω) :
    |horizonPublicLoss (d := d) h B L hB T t i ω - horizonPublicLoss (d := d) h B L hB T t j ω| ≤
      2 * (B + 2 * D) := by
  unfold horizonPublicLoss
  split_ifs with ht
  · exact (actual_public_geometry h B L hB hL hK hT hc ht ω).2 i j hi hj
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (public_width_nonneg h hB)

section Probability
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- All actual public residual sums up to the original horizon agree with
the zero extension, pointwise and before taking any probability or event. -/
theorem horizon_public_interval_eq
    (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B)
    (hm : CNDHorizon.Bounded.Laws
      (concreteMaps (K := K) (R + M + D) L R (B + 2 * D) h.R_nonneg (public_width_nonneg h hB))
      (treeData d K (B + 2 * D) R) h μ T)
    {u n : ℕ} (hu : u + n ≤ T) (ω : Ω) :
    let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
    CNDPayment.intervalSum (CNDPayment.actualPublicResidual m
      (horizonPublicLoss (d := d) h B L hB T)) u n ω =
    CNDPayment.intervalSum (CNDPayment.actualPublicResidual m
      (actualPublicLoss (d := d) h B L hB)) u n ω := by
  dsimp only
  apply sum_congr rfl
  intro t ht
  have htn : u + t < T := by have := mem_range.mp ht; omega
  simp only [CNDPayment.actualPublicResidual, horizonPublicLoss, if_pos htn]

/-- Complete original-run payment/M2/M3 probability ledger. The public-loss
measurability and support span have been discharged from primitive inputs. -/
theorem actual_public_payment_encoding_joint_delta
    (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hK : 2 ≤ K) (hT : T ≤ 2 ^ d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    (hm : CNDHorizon.Bounded.Laws
      (concreteMaps (K := K) (R + M + D) L R (B + 2 * D) h.R_nonneg (public_width_nonneg h hB))
      (treeData d K (B + 2 * D) R) h μ T)
    {δg δl δa δe : ℝ} (hδg : 0 < δg) (hδl : 0 < δl)
    (hδa0 : 0 < δa) (hδa1 : δa < 1) (hδe0 : 0 < δe) (hδe1 : δe < 1) :
    let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
    μ.real {ω |
      (∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
        CNDPayment.paymentEnvelope m (CNDInformation.canonicalChart (Fin K)) (R + M + D) L T u n δg δl ω <
          CNDPayment.intervalSum (CNDPayment.observablePayment m (CNDPayment.actualRadius m (R + M + D) L)) u n ω) ∨
      (∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
        (B + 2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ) ^ 2 / δa)) <
          CNDPayment.intervalSum (CNDPayment.actualPublicResidual m (actualPublicLoss (d := d) h B L hB)) u n ω) ∨
      (∃ k : Fin K, ∃ u n : ℕ, u + n ≤ T ∧ 0 < n ∧
        (2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((K : ℝ) * (T : ℝ) ^ 2 / δe)) <
          CNDPayment.intervalSum (CNDPayment.encodingDifference m k) u n ω)} ≤ δg + δl + δa + δe := by
  let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
  have ht := CNDPayment.payment_public_encoding_joint_delta m
    (horizonPublicLoss (d := d) h B L hB T) (public_width_nonneg h hB)
    (by
      intro t i
      by_cases ht : t<T
      · simpa only [m,CNDHorizon.Bounded.actualM1Model, CNDHorizon.Bounded.model,
          Primitive.stopped, CNDHorizon.Bounded.primitive, if_pos ht] using
          horizonPublicLoss_measurable h B L hB T t i
      · have he : horizonPublicLoss (d:=d) h B L hB T t i=fun _ => 0 := by
          funext ω; simp only [horizonPublicLoss,if_neg ht]
        rw [he]; exact measurable_const)
    (by
      intro t ω i j hi hj
      by_cases ht : t<T
      · simp only [m,CNDHorizon.Bounded.actualM1Model, CNDHorizon.Bounded.model,
          Primitive.stopped, CNDHorizon.Bounded.primitive, stopP, if_pos ht] at hi hj
        exact horizonPublicLoss_span h B L hB hL hK hT hc t ω i j hi hj
      · simp only [horizonPublicLoss, if_neg ht, sub_self, abs_zero]
        exact mul_nonneg (by norm_num) (public_width_nonneg h hB))
    (R + M + D) L (by linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg]) hL T
    hδg hδl hδa0 hδa1 hδe0 hδe1
  apply (measureReal_mono (show _ ⊆ _ from ?_)).trans ht
  intro ω hw
  rcases hw with hp | ha | he
  · exact Or.inl hp
  · right; left
    rcases ha with ⟨u,n,hu,hn,hbad⟩
    refine ⟨u,n,hu,hn,?_⟩
    rwa [horizon_public_interval_eq h B L hB hm hu ω]
  · right; right
    simpa only [Fintype.card_fin] using he

end Probability
end Part2.CNDHorizon.BoundedPublic
