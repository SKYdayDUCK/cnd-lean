import staging.cnd20261026.«fix-bounded-sg».BoundedFinal
import InformationDimension

/-! Explicit original-parameter rate. The information increment, Lc bounds,
and two capped payment branches are proved from the original computed run;
they are not assumptions of the final theorem. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators
set_option maxHeartbeats 1600000

namespace Part2.CNDHorizon.BoundedRate
open CNDProcess CNDHorizon.BoundedPublic CNDHorizon.BoundedMain CNDInformation
variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def paperA (T : ℕ) (δc : ℝ) : ℝ := Real.log (8 * ((T : ℝ)+1)^2 / δc)
def paperE (K T : ℕ) : ℝ := Real.log (1 + 8 * (K : ℝ) * ((T : ℝ)+1))
def paperF (K T : ℕ) : ℝ := Real.log (1 + (T : ℝ) / (K : ℝ))
def localLog (T : ℕ) (δl : ℝ) : ℝ := Real.log ((T : ℝ)^2 / δl)
def globalLog (δg : ℝ) : ℝ := Real.log (1 / δg)
def paperL0 (K T : ℕ) (δc δg δl : ℝ) : ℝ :=
  1 + paperA T δc + paperE K T + paperF K T + localLog T δl + globalLog δg

theorem paper_parameters (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    {δc δg δl : ℝ} (hδc : 0 < δc) (hδc1 : δc ≤ 1)
    (hδg : 0 < δg) (hδg1 : δg ≤ 1) (hδl : 0 < δl) (hδl1 : δl ≤ 1) :
    1 ≤ paperL0 K T δc δg δl ∧
    0 ≤ CNDNet.paperLc (Fin K) T δc ∧
    CNDNet.paperLc (Fin K) T δc ≤ (K : ℝ) * paperL0 K T δc δg δl ∧
    0 ≤ localLog T δl ∧ localLog T δl ≤ paperL0 K T δc δg δl ∧
    0 ≤ globalLog δg ∧ globalLog δg ≤ paperL0 K T δc δg δl ∧
    0 ≤ paperF K T ∧ paperF K T ≤ paperL0 K T δc δg δl := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT0
  have hA : 0 ≤ paperA T δc := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hδc).2
    nlinarith [sq_nonneg (T : ℝ)]
  have hE : 0 ≤ paperE K T := by
    apply Real.log_nonneg
    nlinarith
  have hF : 0 ≤ paperF K T :=
    Real.log_nonneg (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg T) (Nat.cast_nonneg K)))
  have hl : 0 ≤ localLog T δl := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hδl).2
    nlinarith
  have hg : 0 ≤ globalLog δg :=
    Real.log_nonneg ((le_div_iff₀ hδg).2 (by simpa using hδg1))
  have hL0 : 1 ≤ paperL0 K T δc δg δl := by unfold paperL0; linarith
  have hLc0 : 0 ≤ CNDNet.paperLc (Fin K) T δc :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans (CNDNet.paper_Lc_budget T hδc hδc1).1
  have hAe : paperA T δc + paperE K T ≤ paperL0 K T δc δg δl := by
    unfold paperL0
    linarith
  have hKm : (((K-1 : ℕ) : ℝ)) ≤ (K : ℝ) := by exact_mod_cast (Nat.sub_le K 1)
  have hAU := le_mul_of_one_le_left hA hKr
  have hEU := mul_le_mul_of_nonneg_right hKm hE
  have hLc : CNDNet.paperLc (Fin K) T δc ≤ (K : ℝ) * paperL0 K T δc δg δl := by
    calc
      _ = paperA T δc + (((K-1 : ℕ) : ℝ)) * paperE K T := by
        simp only [CNDNet.paperLc, Fintype.card_fin, paperA, paperE]
      _ ≤ (K : ℝ) * (paperA T δc + paperE K T) := by nlinarith only [hAU,hEU]
      _ ≤ _ := mul_le_mul_of_nonneg_left hAe (Nat.cast_nonneg K)
  refine ⟨hL0,hLc0,hLc,hl,?_,hg,?_,hF,?_⟩ <;> unfold paperL0 <;> linarith

section OriginalRun
variable (h : PotentialInputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B)
  (hm : CNDHorizon.Bounded.Laws
    (concreteMaps (K := K) (R + M + D) L R (B + 2 * D)
      h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B + 2 * D) R) h μ T)

def actualInformation (u n : ℕ) (ω : Ω) : ℝ :=
  let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
  let p := fun t i => m.p t i ω
  coordinateLogdet (canonicalChart (Fin K)) p (u+n) -
    coordinateLogdet (canonicalChart (Fin K)) p u

/-- The exact original dimension K-1 and original interval endpoints. -/
theorem actual_information_bounds (u n : ℕ) (ω : Ω) :
    0 ≤ actualInformation h B L hB hm u n ω ∧
    actualInformation h B L hB hm u n ω ≤
      ((K : ℝ)-1) * Real.log (1+(n : ℝ)/(K : ℝ)) := by
  let m := CNDHorizon.Bounded.actualM1Model (d := d) h (public_width_nonneg h hB) μ hm
  let p := fun t i => m.p t i ω
  have hp : ∀ t, p t ∈ CND.simplex := fun t => ⟨m.p_nonneg t ω,m.p_sum t ω⟩
  have hd := tangent_actual_resistance_information_budget (canonicalChart (Fin K))
    canonicalChart_is_tangentChart p hp u n
  have hs : 0 ≤ ∑ s ∈ range n, pairSum (fun i j =>
      p (u+s) i * p (u+s) j * CNDPhysical.resistance p (u+s) i j) := by
    apply sum_nonneg
    intro s _
    apply sum_nonneg
    intro i _
    apply sum_nonneg
    intro j _
    split_ifs
    · exact mul_nonneg (mul_nonneg ((hp _).1 _) ((hp _).1 _))
        (CNDPhysical.actual_resistance_nonneg p hp _ _ _)
    · exact le_rfl
  constructor
  · change 0 ≤ coordinateLogdet (canonicalChart (Fin K)) p (u+n) -
      coordinateLogdet (canonicalChart (Fin K)) p u
    linarith
  · simpa only [actualInformation, m, p, Fintype.card_fin] using canonical_logdet_interval_upper p hp u n

theorem actual_information_le_KL0 (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    {δc δg δl : ℝ} (hδc : 0 < δc) (hδc1 : δc ≤ 1)
    (hδg : 0 < δg) (hδg1 : δg ≤ 1) (hδl : 0 < δl) (hδl1 : δl ≤ 1)
    (u n : ℕ) (hu : u+n ≤ T) (ω : Ω) :
    actualInformation h B L hB hm u n ω ≤ (K : ℝ) * paperL0 K T δc δg δl := by
  have hpar := paper_parameters hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hKm : 0 ≤ (K : ℝ)-1 := by
    have hk : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    linarith
  have hlog : Real.log (1+(n : ℝ)/(K : ℝ)) ≤ paperF K T := by
    apply Real.log_le_log (by positivity)
    apply add_le_add_left
    apply div_le_div_of_nonneg_right _ hK0
    exact_mod_cast (show n ≤ T by omega)
  calc
    _ ≤ ((K : ℝ)-1) * Real.log (1+(n : ℝ)/(K : ℝ)) :=
      (actual_information_bounds h B L hB hm u n ω).2
    _ ≤ ((K : ℝ)-1) * paperF K T := mul_le_mul_of_nonneg_left hlog hKm
    _ ≤ (K : ℝ) * paperF K T := mul_le_mul_of_nonneg_right (by linarith) hpar.2.2.2.2.2.2.2.1
    _ ≤ _ := mul_le_mul_of_nonneg_left hpar.2.2.2.2.2.2.2.2 hK0

theorem actualQ_positive_R (hR : R ≠ 0) (u n : ℕ) (ω : Ω) :
    actualBudgetQ h B L hB hm u n ω =
      (4 * Real.sqrt 3 / CNDPhysical.c0) * (R+M+D) *
        Real.sqrt ((n : ℝ) * L * actualInformation h B L hB hm u n ω) +
      (6 / CNDPhysical.c0) * (4 * (R+M+D) * L + R * (K : ℝ)) *
        actualInformation h B L hB hm u n ω := by
  simp only [actualBudgetQ, CNDPayment.actualQ, CNDInformation.branchedQ, if_neg hR,
    CNDInformation.actualQ, Fintype.card_fin, actualInformation]

end OriginalRun

section Rates
variable (h : PotentialInputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B)
  (δc δg δl : ℝ)
  (hm : CNDHorizon.Bounded.Laws
    (concreteMaps (K := K) (R + M + D) (CNDNet.paperLc (Fin K) T δc) R (B + 2 * D)
      h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B + 2 * D) R) h μ T)

/-- Internal capped-budget algebra; final corollaries discharge both bounds. -/
theorem actual_cap_curve_rate (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hδc : 0 < δc) (hδc1 : δc ≤ 1) (hδg : 0 < δg) (hδg1 : δg ≤ 1)
    (hδl : 0 < δl) (hδl1 : δl ≤ 1)
    (P Λ : ℝ) (u n : ℕ) (hu : u+n ≤ T) (hn : 0 < n) (ω : Ω)
    (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ paperL0 K T δc δg δl)
    (hcap : P ≤ (4 * R / CNDPhysical.c0) * (n : ℝ))
    (hcurve : P ≤ 4 * actualBudgetQ h B (CNDNet.paperLc (Fin K) T δc) hB hm u n ω +
      (4 * R / CNDPhysical.c0) * Λ) :
    P ≤ (156 / CNDPhysical.c0) * (R+M+D) * (K : ℝ) *
      Real.sqrt (n : ℝ) * (paperL0 K T δc δg δl)^2 := by
  by_cases hR : R = 0
  · have hP : P ≤ 0 := by simpa only [hR, mul_zero, zero_mul, zero_div] using hcap
    exact hP.trans (by
      have hH : 0 ≤ R+M+D := by linarith [h.R_nonneg,h.M_nonneg,h.D_nonneg]
      have hc := CNDPhysical.c0_pos
      positivity)
  have hpar := paper_parameters hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
  rw [actualQ_positive_R h B (CNDNet.paperLc (Fin K) T δc) hB hm hR u n ω] at hcurve
  exact CNDRateAbsorption.actual_budget_uniform_rate P (R+M+D) R CNDPhysical.c0
    (K : ℝ) (n : ℝ) (paperL0 K T δc δg δl) (CNDNet.paperLc (Fin K) T δc)
    (actualInformation h B (CNDNet.paperLc (Fin K) T δc) hB hm u n ω) Λ
    h.R_nonneg (by linarith [h.M_nonneg,h.D_nonneg]) CNDPhysical.c0_pos
    (by exact_mod_cast (show 1 ≤ K by omega)) (by exact_mod_cast (show 1 ≤ n by omega)) hpar.1 hpar.2.1
    (actual_information_bounds h B (CNDNet.paperLc (Fin K) T δc) hB hm u n ω).1 hpar.2.2.1
    (actual_information_le_KL0 h B (CNDNet.paperLc (Fin K) T δc) hB hm hK hT0
      hδc hδc1 hδg hδg1 hδl hδl1 u n hu ω) hΛ0 hΛ hcap hcurve

/-- Deterministic envelope rate on every actual sample point, including R=0. -/
theorem exact_envelope_original_rate (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hδc : 0 < δc) (hδc1 : δc ≤ 1) (hδg : 0 < δg) (hδg1 : δg ≤ 1)
    (hδl : 0 < δl) (hδl1 : δl ≤ 1)
    (u n : ℕ) (hu : u+n ≤ T) (hn : 0 < n) (ω : Ω) :
    exactPaymentEnvelope h B (CNDNet.paperLc (Fin K) T δc) hB hm T u n δg δl ω ≤
      (156 / CNDPhysical.c0) * (R+M+D) * (K : ℝ) *
        Real.sqrt (n : ℝ) * (paperL0 K T δc δg δl)^2 := by
  have hpar := paper_parameters hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
  exact actual_cap_curve_rate h B hB δc δg δl hm hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
    _ (localLog T δl) u n hu hn ω hpar.2.2.2.1 hpar.2.2.2.2.1
    (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))

/-- The global envelope itself has the rate; it need not be attained by P. -/
theorem global_budget_original_rate (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hδc : 0 < δc) (hδc1 : δc ≤ 1) (hδg : 0 < δg) (hδg1 : δg ≤ 1)
    (hδl : 0 < δl) (hδl1 : δl ≤ 1) (ω : Ω) :
    globalBudget h B (CNDNet.paperLc (Fin K) T δc) hB hm T δg ω ≤
      (156 / CNDPhysical.c0) * (R+M+D) * (K : ℝ) *
        Real.sqrt (T : ℝ) * (paperL0 K T δc δg δl)^2 := by
  have hpar := paper_parameters hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
  exact actual_cap_curve_rate h B hB δc δg δl hm hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
    _ (globalLog δg) 0 T (by omega) (by omega) ω hpar.2.2.2.2.2.1 hpar.2.2.2.2.2.2.1
    (min_le_left _ _) (min_le_right _ _)

end Rates

theorem paper_expert_log_bound (hK : 2 ≤ K) (hT0 : 1 ≤ T) :
    CNDProd.logExperts (Nat.clog 2 T) K ≤ Real.log (4 * (K : ℝ) * (T : ℝ)) := by
  apply Real.log_le_log
  · have hN := CNDProd.logExperts_pos (d := Nat.clog 2 T) hK
    exact_mod_cast (show 0 < CNDProd.expertCount (Nat.clog 2 T) K by
      unfold CNDProd.expertCount
      have hp : 0 < 2^(Nat.clog 2 T + 1) - 1 := by
        have : 0 < 2^(Nat.clog 2 T) := by positivity
        rw [pow_succ]
        omega
      exact Nat.mul_pos (by omega) hp)
  · exact_mod_cast (CNDProd.padded_expert_count_lt (show 0 < K by omega) (show 0 < T by omega)).le

def paperPublicCoefficient (K T : ℕ) (B D δa δe : ℝ) : ℝ :=
  32 * (B+2*D) * Real.sqrt (Real.log (4 * (K : ℝ) * (T : ℝ))) +
    (B+2*D) * Real.sqrt (2 * Real.log ((T : ℝ)^2 / δa)) +
    (2*D) * Real.sqrt (2 * Real.log ((K : ℝ) * (T : ℝ)^2 / δe))

theorem publicCoefficient_paper_le (h : PotentialInputs ℱ θ R M D)
    (B : ℝ) (hB : 0 ≤ B) (δa δe : ℝ) (hK : 2 ≤ K) (hT0 : 1 ≤ T) :
    publicCoefficient (Nat.clog 2 T) K T B D δa δe ≤ paperPublicCoefficient K T B D δa δe := by
  unfold publicCoefficient paperPublicCoefficient
  have hW := public_width_nonneg h hB
  gcongr
  exact paper_expert_log_bound hK hT0

/-- Final original-parameter corollary. No confidence, information-dimension,
cap/curve, event, update, path partition or budget premise is exposed. -/
theorem paper_original_main_with_rates
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
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δ ∧ ∀ ω ∈ G,
      BoundedConclusions h B hB δc δg δl δa δe hm ω ∧
      (∀ u n : ℕ, u+n ≤ T → 0 < n →
        CNDPayment.intervalSum (actualLedger h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω ≤
          (156 / CNDPhysical.c0) * (R+M+D) * (K : ℝ) * Real.sqrt (n : ℝ) *
            (paperL0 K T δc δg δl)^2) ∧
      (globalBudget h B (CNDNet.paperLc (Fin K) T δc) hB hm T δg ω ≤
        (156 / CNDPhysical.c0) * (R+M+D) * (K : ℝ) * Real.sqrt (T : ℝ) *
          (paperL0 K T δc δg δl)^2) ∧
      (∀ path : ℕ → Fin K, pathRegret h T path ω ≤
        paperPublicCoefficient K T B D δa δe *
          Real.sqrt ((T : ℝ) * ((switchCount T path + 1 : ℕ) : ℝ)) +
        (156 / CNDPhysical.c0) * (R+M+D) * (K : ℝ) * Real.sqrt (T : ℝ) *
          (paperL0 K T δc δg δl)^2) := by
  have hδc1 : δc ≤ 1 := by linarith
  have hδg1 : δg ≤ 1 := by linarith
  have hδl1 : δl ≤ 1 := by linarith
  obtain ⟨G,hG,hprob,hgood⟩ := paper_depth_bounded_main h B hB δc δg δl δa δe hm
    hK hT0 hc hδc hδg hδl hδa hδe hδ hδsum
  refine ⟨G,hG,hprob,?_⟩
  intro ω hω
  have hg := hgood ω hω
  have hb := global_budget_original_rate h B hB δc δg δl hm hK hT0
    hδc hδc1 hδg hδg1 hδl hδl1 ω
  refine ⟨hg,?_,hb,?_⟩
  · intro u n hu hn
    exact (hg.2.1 u n hu hn).trans (exact_envelope_original_rate h B hB δc δg δl hm
      hK hT0 hδc hδc1 hδg hδg1 hδl hδl1 u n hu hn ω)
  · intro path
    exact (hg.2.2.1 path).trans (add_le_add
      (mul_le_mul_of_nonneg_right (publicCoefficient_paper_le h B hB δa δe hK hT0)
        (Real.sqrt_nonneg _)) hb)

end Part2.CNDHorizon.BoundedRate
