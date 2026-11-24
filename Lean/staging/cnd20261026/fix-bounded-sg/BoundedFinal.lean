import staging.cnd20261026.«fix-bounded-sg».BoundedPhysical
import staging.cnd20261026.«fix-bounded-sg».BoundedEvents
import SwitchingRuns
import RateAbsorption

/-! The original bounded CND theorem: the actual physical losses, a common
original-space probability event, the exact observable ledger, and every
post-hoc comparator path. No confidence, geometry, update, partition or budget
field is added to PotentialInputs or CNDHorizon.Bounded.Laws. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators
set_option maxHeartbeats 1600000

namespace Part2.CNDHorizon.BoundedMain
open CNDProcess CNDHorizon.BoundedPublic CNDHorizon.BoundedEvents

variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def intervalRegret (h : PotentialInputs ℱ θ R M D) (u n : ℕ)
    (k : Fin K) (ω : Ω) : ℝ :=
  ∑ t ∈ Ico u (u + n), (h.physical t (h.action t ω) ω - h.physical t k ω)

def pathRegret (h : PotentialInputs ℱ θ R M D) (T : ℕ)
    (path : ℕ → Fin K) (ω : Ω) : ℝ :=
  ∑ t ∈ range T, (h.physical t (h.action t ω) ω - h.physical t (path t) ω)

def switchCount (T : ℕ) (path : ℕ → Fin K) : ℕ :=
  ((range (T - 1)).filter (fun t => path (t + 1) ≠ path t)).card

def publicCoefficient (d K T : ℕ) (B D δa δe : ℝ) : ℝ :=
  32 * (B + 2 * D) * Real.sqrt (CNDProd.logExperts d K) +
  (B + 2 * D) * Real.sqrt (2 * Real.log ((T : ℝ)^2 / δa)) +
  (2 * D) * Real.sqrt (2 * Real.log ((K : ℝ) * (T : ℝ)^2 / δe))

section ActualLedger
variable (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B)
  (hm : CNDHorizon.Bounded.Laws
    (concreteMaps (K := K) (R + M + D) L R (B + 2 * D)
      h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B + 2 * D) R) h μ T)

def actualLedger (t : ℕ) (ω : Ω) : ℝ :=
  let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
  CNDPayment.observablePayment m (CNDPayment.actualRadius m (R + M + D) L) t ω

def actualBudgetQ (u n : ℕ) (ω : Ω) : ℝ :=
  let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
  CNDPayment.actualQ m (CNDInformation.canonicalChart (Fin K)) (R + M + D) L u n ω

def globalBudget (T : ℕ) (δg : ℝ) (ω : Ω) : ℝ :=
  min ((4 * R / CNDPhysical.c0) * (T : ℝ))
    (4 * actualBudgetQ h B L hB hm 0 T ω + (4 * R / CNDPhysical.c0) * Real.log (1 / δg))

def exactPaymentEnvelope (T u n : ℕ) (δg δl : ℝ) (ω : Ω) : ℝ :=
  min ((4 * R / CNDPhysical.c0) * (n : ℝ))
    (min (4 * actualBudgetQ h B L hB hm u n ω +
      (4 * R / CNDPhysical.c0) * Real.log ((T : ℝ)^2 / δl))
      (globalBudget h B L hB hm T δg ω))

theorem ledger_nonneg (hL : 0 ≤ L) (t : ℕ) (ω : Ω) :
    0 ≤ actualLedger h B L hB hm t ω := by
  let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
  exact (CNDPayment.observablePayment_bounds m (CNDPayment.actualRadius m (R + M + D) L)
    (4 * R / CNDPhysical.c0)
    (CNDPayment.actualRadius_bounds m (R + M + D) L
      (by linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg]) hL) t ω).1

/-- The repeated global cap is retained exactly as in original equation (8). -/
theorem paymentEnvelope_eq_exact {u n T : ℕ} (hu : u + n ≤ T)
    (δg δl : ℝ) (ω : Ω) :
    let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
    CNDPayment.paymentEnvelope m (CNDInformation.canonicalChart (Fin K))
      (R + M + D) L T u n δg δl ω =
      exactPaymentEnvelope h B L hB hm T u n δg δl ω := by
  have hC : 0 ≤ 4 * R / CNDPhysical.c0 :=
    div_nonneg (mul_nonneg (by norm_num) h.R_nonneg) CNDPhysical.c0_pos.le
  have hcap : (4 * R / CNDPhysical.c0) * (n : ℝ) ≤
      (4 * R / CNDPhysical.c0) * (T : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hC
    exact_mod_cast (show n ≤ T by omega)
  dsimp only [CNDPayment.paymentEnvelope, exactPaymentEnvelope, globalBudget, actualBudgetQ]
  symm
  calc
    _ = min (min ((4 * R / CNDPhysical.c0) * (n : ℝ))
        ((4 * R / CNDPhysical.c0) * (T : ℝ)))
      (min (4 * CNDPayment.actualQ
        (CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm)
        (CNDInformation.canonicalChart (Fin K)) (R + M + D) L 0 T ω +
        (4 * R / CNDPhysical.c0) * Real.log (1 / δg))
        (4 * CNDPayment.actualQ
        (CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm)
        (CNDInformation.canonicalChart (Fin K)) (R + M + D) L u n ω +
        (4 * R / CNDPhysical.c0) * Real.log ((T : ℝ)^2 / δl))) := by ac_rfl
    _ = _ := by rw [min_eq_left hcap]

/-- Every deterministic partition counts the very same actual ledger once. -/
theorem ledger_partition_exact (T : ℕ) (P : Intervals.Partition (range T)) (ω : Ω) :
    (∑ j ∈ P.labels, ∑ t ∈ P.block j, actualLedger h B L hB hm t ω) =
      CNDPayment.intervalSum (actualLedger h B L hB hm) 0 T ω := by
  simpa only [CNDPayment.intervalSum, Nat.zero_add] using
    P.sum_blocks (fun t => actualLedger h B L hB hm t ω)

theorem zero_R_ledger (hR : R = 0) (t : ℕ) (ω : Ω) :
    actualLedger h B L hB hm t ω = 0 := by
  simp [actualLedger, CNDPayment.observablePayment, CNDPayment.paymentAt,
    CNDPayment.rowMean, CNDPayment.actualRadius, hR,
    CNDPhysical.actualSaturatedRadius, CNDPhysical.saturatedRadius]

theorem zero_R_Q (hR : R = 0) (u n : ℕ) (ω : Ω) :
    actualBudgetQ h B L hB hm u n ω = 0 := by
  simp [actualBudgetQ, CNDPayment.actualQ, CNDInformation.branchedQ, hR]

theorem zero_R_globalBudget (hR : R = 0) (T : ℕ) (δg : ℝ) (ω : Ω) :
    globalBudget h B L hB hm T δg ω = 0 := by
  simp [globalBudget, zero_R_Q h B L hB hm hR, hR]

end ActualLedger

theorem publicCoefficient_nonneg (h : PotentialInputs ℱ θ R M D)
    (B : ℝ) (hB : 0 ≤ B) (d K T : ℕ) (δa δe : ℝ) :
    0 ≤ publicCoefficient d K T B D δa δe := by
  unfold publicCoefficient
  have hW := public_width_nonneg h hB
  have hD := h.D_nonneg
  positivity

theorem public_terms_eq_coefficient (n : ℕ) (d K T : ℕ) (B D δa δe : ℝ) :
    32 * (B + 2 * D) * Real.sqrt ((n : ℝ) * CNDProd.logExperts d K) +
      (B + 2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa)) +
      (2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((K : ℝ) * (T : ℝ)^2 / δe)) =
    publicCoefficient d K T B D δa δe * Real.sqrt (n : ℝ) := by
  have hs (x : ℝ) : Real.sqrt ((n : ℝ) * x) = Real.sqrt x * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), mul_comm]
  rw [show 2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa) =
    (n : ℝ) * (2 * Real.log ((T : ℝ)^2 / δa)) by ring,
    show 2 * (n : ℝ) * Real.log ((K : ℝ) * (T : ℝ)^2 / δe) =
    (n : ℝ) * (2 * Real.log ((K : ℝ) * (T : ℝ)^2 / δe)) by ring]
  rw [hs, hs, hs]
  unfold publicCoefficient
  ring

section EventConsequences
variable (h : PotentialInputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B)
  (δc δg δl δa δe : ℝ)
  (hm : CNDHorizon.Bounded.Laws
    (concreteMaps (K := K) (R + M + D) (CNDNet.paperLc (Fin K) T δc) R (B + 2 * D)
      h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B + 2 * D) R) h μ T)

theorem event_interval_physical (hL : 0 ≤ CNDNet.paperLc (Fin K) T δc)
    (hK : 2 ≤ K) (hT : T ≤ 2^d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    (ω : Ω) (hω : MainEvent (d := d) (T := T) h B hB δc δg δl δa δe hm ω)
    (u n : ℕ) (hu : u + n ≤ T) (hn : 0 < n) (k : Fin K) :
    intervalRegret h u n k ω ≤
      32 * (B + 2 * D) * Real.sqrt ((n : ℝ) * CNDProd.logExperts d K) +
      (B + 2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa)) +
      (2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((K : ℝ) * (T : ℝ)^2 / δe)) +
      CNDPayment.intervalSum
        (actualLedger h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω := by
  have hp := CNDHorizon.BoundedPhysical.actual_physical_interval_le h B
    (CNDNet.paperLc (Fin K) T δc) hB hm hL hK hT hc u n hu k ω
    (fun t ht i j => hω.1 t (Nat.le_of_lt ht) i j)
  have ha := hω.2.2.1 u n hu hn
  have he := hω.2.2.2 k u n hu hn
  change intervalRegret h u n k ω ≤ _ at hp
  change _ ≤ _ + _ + _ + CNDPayment.intervalSum
    (actualLedger h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω
  unfold actualLedger
  linarith

theorem event_interval_coefficient (hL : 0 ≤ CNDNet.paperLc (Fin K) T δc)
    (hK : 2 ≤ K) (hT : T ≤ 2^d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    (ω : Ω) (hω : MainEvent (d := d) (T := T) h B hB δc δg δl δa δe hm ω)
    (u n : ℕ) (hu : u + n ≤ T) (hn : 0 < n) (k : Fin K) :
    intervalRegret h u n k ω ≤ publicCoefficient d K T B D δa δe * Real.sqrt (n : ℝ) +
      ∑ t ∈ Ico u (u+n), actualLedger h B (CNDNet.paperLc (Fin K) T δc) hB hm t ω := by
  have hi := event_interval_physical h B hB δc δg δl δa δe hm hL hK hT hc ω hω u n hu hn k
  rw [public_terms_eq_coefficient] at hi
  rw [CNDHorizon.BoundedPhysical.sum_Ico_eq_intervalSum]
  exact hi

theorem event_payment_exact
    (ω : Ω) (hω : MainEvent (d := d) (T := T) h B hB δc δg δl δa δe hm ω)
    (u n : ℕ) (hu : u + n ≤ T) (hn : 0 < n) :
    CNDPayment.intervalSum (actualLedger h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω ≤
      exactPaymentEnvelope h B (CNDNet.paperLc (Fin K) T δc) hB hm T u n δg δl ω := by
  have hp := hω.2.1 u n hu hn
  rw [paymentEnvelope_eq_exact h B (CNDNet.paperLc (Fin K) T δc) hB hm hu δg δl ω] at hp
  exact hp

theorem event_global_budget (hT0 : 1 ≤ T)
    (ω : Ω) (hω : MainEvent (d := d) (T := T) h B hB δc δg δl δa δe hm ω) :
    CNDPayment.intervalSum (actualLedger h B (CNDNet.paperLc (Fin K) T δc) hB hm) 0 T ω ≤
      globalBudget h B (CNDNet.paperLc (Fin K) T δc) hB hm T δg ω := by
  have hp := event_payment_exact h B hB δc δg δl δa δe hm ω hω 0 T (by omega) (by omega)
  exact hp.trans ((min_le_right _ _).trans (min_le_right _ _))

theorem event_posthoc_path (hL : 0 ≤ CNDNet.paperLc (Fin K) T δc)
    (hK : 2 ≤ K) (hT0 : 1 ≤ T) (hT : T ≤ 2^d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    (ω : Ω) (hω : MainEvent (d := d) (T := T) h B hB δc δg δl δa δe hm ω)
    (path : ℕ → Fin K) :
    pathRegret h T path ω ≤
      publicCoefficient d K T B D δa δe *
        Real.sqrt ((T : ℝ) * ((switchCount T path + 1 : ℕ) : ℝ)) +
      globalBudget h B (CNDNet.paperLc (Fin K) T δc) hB hm T δg ω := by
  cases T with
  | zero => omega
  | succ N =>
    have hlocal : ∀ a b : ℕ, Icc a b ⊆ range (N+1) → ∀ k : Fin K,
        (∑ t ∈ Icc a b, (h.physical t (h.action t ω) ω - h.physical t k ω)) ≤
        publicCoefficient d K (N+1) B D δa δe * Real.sqrt ((Icc a b).card : ℝ) +
          ∑ t ∈ Icc a b, actualLedger h B (CNDNet.paperLc (Fin K) (N+1) δc) hB hm t ω := by
      intro a b hsub k
      by_cases hab : a ≤ b
      · have hb := mem_range.mp (hsub (mem_Icc.mpr ⟨hab, le_rfl⟩))
        let n := b + 1 - a
        have hn : 0 < n := by dsimp [n]; omega
        have he : a+n = b+1 := by dsimp [n]; omega
        have hi : Icc a b = Ico a (a+n) := by
          ext t
          simp only [mem_Icc, mem_Ico]
          omega
        have hcard : (Icc a b).card = n := by rw [Nat.card_Icc]
        have hl := event_interval_coefficient h B hB δc δg δl δa δe hm
          hL hK hT hc ω hω a n (by omega) hn k
        unfold intervalRegret at hl
        rw [← hi] at hl
        simpa only [hcard] using hl
      · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hab), sum_empty, card_empty,
          Nat.cast_zero, Real.sqrt_zero, mul_zero, add_zero, le_refl]
    have hbudget := event_global_budget h B hB δc δg δl δa δe hm hT0 ω hω
    have hp := SwitchingRuns.all_intervals_to_actual_path N path
      (fun t k => h.physical t k ω) (fun t => h.physical t (h.action t ω) ω)
      (fun t => actualLedger h B (CNDNet.paperLc (Fin K) (N+1) δc) hB hm t ω)
      (publicCoefficient d K (N+1) B D δa δe)
      (globalBudget h B (CNDNet.paperLc (Fin K) (N+1) δc) hB hm (N+1) δg ω)
      (publicCoefficient_nonneg h B hB d K (N+1) δa δe) hlocal
      (by simpa only [CNDPayment.intervalSum, Nat.zero_add] using hbudget)
    simpa only [pathRegret, switchCount, Nat.add_sub_cancel] using hp

/-- The three original conclusions, on one sample point. The final model has
only its original primitive input fields and its original two M1 laws. -/
def BoundedConclusions (ω : Ω) : Prop :=
  (∀ u n : ℕ, u+n ≤ T → 0 < n → ∀ k : Fin K,
    intervalRegret h u n k ω ≤
      32 * (B + 2 * D) * Real.sqrt ((n : ℝ) * CNDProd.logExperts d K) +
      (B + 2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((T : ℝ)^2 / δa)) +
      (2 * D) * Real.sqrt (2 * (n : ℝ) * Real.log ((K : ℝ) * (T : ℝ)^2 / δe)) +
      CNDPayment.intervalSum (actualLedger h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω) ∧
  (∀ u n : ℕ, u+n ≤ T → 0 < n →
    CNDPayment.intervalSum (actualLedger h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω ≤
      exactPaymentEnvelope h B (CNDNet.paperLc (Fin K) T δc) hB hm T u n δg δl ω) ∧
  (∀ path : ℕ → Fin K, pathRegret h T path ω ≤
    publicCoefficient d K T B D δa δe *
      Real.sqrt ((T : ℝ) * ((switchCount T path + 1 : ℕ) : ℝ)) +
    globalBudget h B (CNDNet.paperLc (Fin K) T δc) hB hm T δg ω) ∧
  (∀ P : Intervals.Partition (range T),
    (∑ j ∈ P.labels, ∑ t ∈ P.block j,
      actualLedger h B (CNDNet.paperLc (Fin K) T δc) hB hm t ω) =
    CNDPayment.intervalSum (actualLedger h B (CNDNet.paperLc (Fin K) T δc) hB hm) 0 T ω)

/-- End-to-end original equations (7), (8), and (9). The single good event is
constructed from the original run; arbitrary post-hoc paths cost no budget. -/
theorem original_bounded_main (hK : 2 ≤ K) (hT0 : 1 ≤ T) (hT : T ≤ 2^d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    {δ : ℝ} (hδc : 0 < δc) (hδg : 0 < δg) (hδl : 0 < δl)
    (hδa : 0 < δa) (hδe : 0 < δe) (hδ : δ < 1)
    (hδsum : δc + δg + δl + δa + δe ≤ δ) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δ ∧
      ∀ ω ∈ G, BoundedConclusions h B hB δc δg δl δa δe hm ω := by
  have hL : 0 ≤ CNDNet.paperLc (Fin K) T δc :=
    le_trans (by norm_num) (CNDNet.paper_Lc_budget (ι := Fin K) T hδc (by linarith)).1
  obtain ⟨G,hG,hprob,hgood⟩ := CNDHorizon.BoundedEvents.original_run_main_event h B hB
    hK hT0 hT hc hδc (by linarith) hδg hδl hδa (by linarith) hδe (by linarith) hm
  refine ⟨G,hG,hprob.trans hδsum,?_⟩
  intro ω hω
  have hg := hgood ω hω
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact event_interval_physical h B hB δc δg δl δa δe hm hL hK hT hc ω hg
  · exact event_payment_exact h B hB δc δg δl δa δe hm ω hg
  · exact event_posthoc_path h B hB δc δg δl δa δe hm hL hK hT0 hT hc ω hg
  · intro P
    exact ledger_partition_exact h B (CNDNet.paperLc (Fin K) T δc) hB hm T P ω

end EventConsequences

/-- Original paper depth; no extra horizon or tree-depth hypothesis. -/
theorem paper_depth_bounded_main
    (h : PotentialInputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B)
    (δc δg δl δa δe : ℝ)
    (hm : CNDHorizon.Bounded.Laws
      (concreteMaps (K := K) (R + M + D) (CNDNet.paperLc (Fin K) T δc) R (B + 2 * D)
        h.R_nonneg (public_width_nonneg h hB))
      (treeData (Nat.clog 2 T) K (B + 2 * D) R) h μ T)
    (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω - h.publicCost t i ω ≤ B)
    {δ : ℝ} (hδc : 0 < δc) (hδg : 0 < δg) (hδl : 0 < δl)
    (hδa : 0 < δa) (hδe : 0 < δe) (hδ : δ < 1)
    (hδsum : δc + δg + δl + δa + δe ≤ δ) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δ ∧
      ∀ ω ∈ G, BoundedConclusions h B hB δc δg δl δa δe hm ω := by
  exact original_bounded_main h B hB δc δg δl δa δe hm hK hT0
    (CNDProd.padded_horizon T) hc hδc hδg hδl hδa hδe hδ hδsum

/-- The public coefficient vanishes in the actual zero-width branch. -/
theorem zero_width_publicCoefficient (h : PotentialInputs ℱ θ R M D)
    (B : ℝ) (hB : 0 ≤ B) (hW : B + 2 * D = 0)
    (d K T : ℕ) (δa δe : ℝ) : publicCoefficient d K T B D δa δe = 0 := by
  have hD : D = 0 := by linarith [h.D_nonneg]
  have hB0 : B = 0 := by linarith
  simp [publicCoefficient, hB0, hD]

theorem zero_horizon_path (h : PotentialInputs ℱ θ R M D) (path : ℕ → Fin K) (ω : Ω) :
    pathRegret h 0 path ω = 0 := by simp [pathRegret]

theorem singleton_path (h : PotentialInputs ℱ θ R M D) (hK : K = 1)
    (T : ℕ) (path : ℕ → Fin K) (ω : Ω) : pathRegret h T path ω = 0 := by
  have hall (i j : Fin K) : i = j := by apply Fin.ext; have hi := i.isLt; have hj := j.isLt; omega
  unfold pathRegret
  apply sum_eq_zero
  intro t ht
  rw [hall (h.action t ω) (path t), sub_self]

end Part2.CNDHorizon.BoundedMain
