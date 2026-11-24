import staging.cnd20261026.«fix-bounded-sg».SGPaper
import staging.cnd20261025.bounded.RateCorollary

/-! Original-parameter SG payment rates. The frozen exact SG main package is
unchanged. The only reused bounded lemmas here are pure logarithm bounds;
all information increments and payments refer to the actual noisy SG run. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators NNReal
set_option maxHeartbeats 1600000
namespace Part2.CNDHorizon.SGRate
open CNDProcess CNDProcess.SG CNDHorizon.SGMain CNDInformation CNDBoundedRate
variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {σ σe : ℝ}
variable (ν : ℝ≥0)
section OriginalRun
variable (h : Inputs ℱ θ R M D) (B L : ℝ) (hB : 0 ≤ B)
  (hm : CNDHorizon.SG.Laws
    (maps (K := K) ν L R M (B+2*D)
      h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B + 2 * D) R) h μ σ σe T)

def actualInformation (u n : ℕ) (ω : Ω) : ℝ :=
  let m := shadow ν h B L hB hm
  let p := fun t i => m.p t i ω
  coordinateLogdet (canonicalChart (Fin K)) p (u+n) -
    coordinateLogdet (canonicalChart (Fin K)) p u

/-- The exact original dimension K-1 and original interval endpoints. -/
theorem actual_information_bounds (u n : ℕ) (ω : Ω) :
    0 ≤ actualInformation ν h B L hB hm u n ω ∧
    actualInformation ν h B L hB hm u n ω ≤
      ((K : ℝ)-1) * Real.log (1+(n : ℝ)/(K : ℝ)) := by
  let m := shadow ν h B L hB hm
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
    actualInformation ν h B L hB hm u n ω ≤ (K : ℝ) * paperL0 K T δc δg δl := by
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
      (actual_information_bounds ν h B L hB hm u n ω).2
    _ ≤ ((K : ℝ)-1) * paperF K T := mul_le_mul_of_nonneg_left hlog hKm
    _ ≤ (K : ℝ) * paperF K T := mul_le_mul_of_nonneg_right (by linarith) hpar.2.2.2.2.2.2.2.1
    _ ≤ _ := mul_le_mul_of_nonneg_left hpar.2.2.2.2.2.2.2.2 hK0

theorem actualQ_positive_R (hR : R ≠ 0) (u n : ℕ) (ω : Ω) :
    actualBudgetQ ν h B L hB hm u n ω =
      (4 * Real.sqrt 3 / CNDPhysical.c0) * (R+M+(ν:ℝ)) *
        Real.sqrt ((n : ℝ) * (4*L) * actualInformation ν h B L hB hm u n ω) +
      (6 / CNDPhysical.c0) * (4 * (R+M+(ν:ℝ)) * (4*L) + R * (K : ℝ)) *
        actualInformation ν h B L hB hm u n ω := by
  simp only [actualBudgetQ, CNDPayment.actualQ, CNDInformation.branchedQ, if_neg hR,
    CNDInformation.actualQ, Fintype.card_fin, actualInformation]

end OriginalRun

section Rates
variable (h : Inputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B)
  (δc δg δl : ℝ)
  (hm : CNDHorizon.SG.Laws
    (maps (K := K) ν (CNDNet.paperLc (Fin K) T δc) R M (B+2*D)
      h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B + 2 * D) R) h μ σ σe T)

/-- Internal capped-budget algebra; final corollaries discharge both bounds. -/
theorem actual_cap_curve_rate (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hδc : 0 < δc) (hδc1 : δc ≤ 1) (hδg : 0 < δg) (hδg1 : δg ≤ 1)
    (hδl : 0 < δl) (hδl1 : δl ≤ 1)
    (P Λ : ℝ) (u n : ℕ) (hu : u+n ≤ T) (hn : 0 < n) (ω : Ω)
    (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ paperL0 K T δc δg δl)
    (hcap : P ≤ (4 * R / CNDPhysical.c0) * (n : ℝ))
    (hcurve : P ≤ 4 * actualBudgetQ ν h B (CNDNet.paperLc (Fin K) T δc) hB hm u n ω +
      (4 * R / CNDPhysical.c0) * Λ) :
    P ≤ (2496 / CNDPhysical.c0) * (R+M+(ν:ℝ)) * (K : ℝ) *
      Real.sqrt (n : ℝ) * (paperL0 K T δc δg δl)^2 := by
  by_cases hR : R = 0
  · have hP : P ≤ 0 := by simpa only [hR, mul_zero, zero_mul, zero_div] using hcap
    exact hP.trans (by
      have hH : 0 ≤ R+M+(ν:ℝ) := by linarith [h.R_nonneg,h.M_nonneg,ν.coe_nonneg]
      have hc := CNDPhysical.c0_pos
      positivity)
  have hpar := paper_parameters hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
  rw [actualQ_positive_R ν h B (CNDNet.paperLc (Fin K) T δc) hB hm hR u n ω] at hcurve
  have hL4 : 1 ≤ 4*paperL0 K T δc δg δl := by linarith [hpar.1]
  have ha0 : 0 ≤ 4*CNDNet.paperLc (Fin K) T δc := mul_nonneg (by norm_num) hpar.2.1
  have haU : 4*CNDNet.paperLc (Fin K) T δc ≤ (K:ℝ)*(4*paperL0 K T δc δg δl) := by
    nlinarith [hpar.2.2.1]
  have hdU : actualInformation ν h B (CNDNet.paperLc (Fin K) T δc) hB hm u n ω ≤
      (K:ℝ)*(4*paperL0 K T δc δg δl) := by
    have hd := actual_information_le_KL0 ν h B (CNDNet.paperLc (Fin K) T δc) hB hm hK hT0
      hδc hδc1 hδg hδg1 hδl hδl1 u n hu ω
    have hKL : 0 ≤ (K:ℝ)*paperL0 K T δc δg δl := by
      exact mul_nonneg (Nat.cast_nonneg K) (by linarith [hpar.1])
    nlinarith
  have hΛ4 : Λ ≤ 4*paperL0 K T δc δg δl := by linarith [hpar.1]
  have hf := CNDRateAbsorption.actual_budget_uniform_rate P (R+M+(ν:ℝ)) R CNDPhysical.c0
    (K : ℝ) (n : ℝ) (4*paperL0 K T δc δg δl) (4*CNDNet.paperLc (Fin K) T δc)
    (actualInformation ν h B (CNDNet.paperLc (Fin K) T δc) hB hm u n ω) Λ
    h.R_nonneg (by linarith [h.M_nonneg,ν.coe_nonneg]) CNDPhysical.c0_pos
    (by exact_mod_cast (show 1 ≤ K by omega)) (by exact_mod_cast (show 1 ≤ n by omega)) hL4 ha0
    (actual_information_bounds ν h B (CNDNet.paperLc (Fin K) T δc) hB hm u n ω).1 haU hdU hΛ0 hΛ4 hcap hcurve
  convert hf using 1 <;> ring

/-- Deterministic envelope rate on every actual sample point, including R=0. -/
theorem exact_envelope_original_rate (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hδc : 0 < δc) (hδc1 : δc ≤ 1) (hδg : 0 < δg) (hδg1 : δg ≤ 1)
    (hδl : 0 < δl) (hδl1 : δl ≤ 1)
    (u n : ℕ) (hu : u+n ≤ T) (hn : 0 < n) (ω : Ω) :
    exactPaymentEnvelope ν h B (CNDNet.paperLc (Fin K) T δc) hB hm T u n δg δl ω ≤
      (2496 / CNDPhysical.c0) * (R+M+(ν:ℝ)) * (K : ℝ) *
        Real.sqrt (n : ℝ) * (paperL0 K T δc δg δl)^2 := by
  have hpar := paper_parameters hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
  exact actual_cap_curve_rate ν h B hB δc δg δl hm hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
    _ (localLog T δl) u n hu hn ω hpar.2.2.2.1 hpar.2.2.2.2.1
    (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))

/-- The global envelope itself has the rate; it need not be attained by P. -/
theorem global_budget_original_rate (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hδc : 0 < δc) (hδc1 : δc ≤ 1) (hδg : 0 < δg) (hδg1 : δg ≤ 1)
    (hδl : 0 < δl) (hδl1 : δl ≤ 1) (ω : Ω) :
    globalBudget ν h B (CNDNet.paperLc (Fin K) T δc) hB hm T δg ω ≤
      (2496 / CNDPhysical.c0) * (R+M+(ν:ℝ)) * (K : ℝ) *
        Real.sqrt (T : ℝ) * (paperL0 K T δc δg δl)^2 := by
  have hpar := paper_parameters hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
  exact actual_cap_curve_rate ν h B hB δc δg δl hm hK hT0 hδc hδc1 hδg hδg1 hδl hδl1
    _ (globalLog δg) 0 T (by omega) (by omega) ω hpar.2.2.2.2.2.1 hpar.2.2.2.2.2.2.1
    (min_le_left _ _) (min_le_right _ _)

end Rates

def paperPublicCoefficient (K T : ℕ) (B D δa δn : ℝ) : ℝ :=
  32*(B+2*D)*Real.sqrt (Real.log (4*(K:ℝ)*(T:ℝ))) +
  (B+2*D)*Real.sqrt (2*Real.log ((T:ℝ)^2/δa)) +
  (2*(ν:ℝ))*Real.sqrt (2*Real.log ((K:ℝ)*(T:ℝ)^2/δn))

theorem publicCoefficient_paper_le (h : Inputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B)
    (δa δn : ℝ) (hK : 2 ≤ K) (hT0 : 1 ≤ T) :
    publicCoefficient ν (Nat.clog 2 T) K T B D δa δn ≤ paperPublicCoefficient ν K T B D δa δn := by
  unfold publicCoefficient paperPublicCoefficient
  have hW := public_width_nonneg h hB
  gcongr
  exact CNDBoundedRate.paper_expert_log_bound hK hT0

/-- The original SG run, all interval/private rates and all post-hoc paths
share the exact main event. No information, cap, curve or tail premise remains. -/
theorem paper_original_sg_main_with_rates (hν : (ν:ℝ)^2=σ^2+σe^2)
    (h : Inputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B) (δc δg δl δa δn : ℝ)
    (hm : CNDHorizon.SG.Laws (maps (K := K) ν (CNDNet.paperLc (Fin K) T δc) R M (B+2*D)
      h.R_nonneg (public_width_nonneg h hB)) (treeData (Nat.clog 2 T) K (B+2*D) R) h μ σ σe T)
    (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω-h.publicCost t i ω ≤ B)
    {δ : ℝ} (hδc : 0 < δc) (hδg : 0 < δg) (hδl : 0 < δl)
    (hδa : 0 < δa) (hδn : 0 < δn) (hδ : δ < 1)
    (hδsum : δc+δg+δl+δa+δn ≤ δ) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δ ∧ ∀ ω ∈ G,
      SGCompleteConclusions ν h B hB δc δg δl δa δn hm ω ∧
      (∀ u n : ℕ, u+n ≤ T → 0 < n →
        CNDPayment.intervalSum (actualLedger ν h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω ≤
          (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (n:ℝ)*(paperL0 K T δc δg δl)^2) ∧
      (globalBudget ν h B (CNDNet.paperLc (Fin K) T δc) hB hm T δg ω ≤
        (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (T:ℝ)*(paperL0 K T δc δg δl)^2) ∧
      (∀ u n : ℕ, u+n ≤ T → 0 < n → ∀ path : ℕ → Fin K,
        intervalPathRegret h u n path ω ≤ paperPublicCoefficient ν K T B D δa δn *
          Real.sqrt ((n:ℝ)*((intervalSwitchCount u n path+1:ℕ):ℝ)) +
          (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (n:ℝ)*(paperL0 K T δc δg δl)^2) ∧
      (∀ path : ℕ → Fin K, pathRegret h T path ω ≤ paperPublicCoefficient ν K T B D δa δn *
        Real.sqrt ((T:ℝ)*((switchCount T path+1:ℕ):ℝ)) +
        (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (T:ℝ)*(paperL0 K T δc δg δl)^2) := by
  have hδc1 : δc ≤ 1 := by linarith
  have hδg1 : δg ≤ 1 := by linarith
  have hδl1 : δl ≤ 1 := by linarith
  obtain ⟨G,hG,hprob,hgood⟩ := paper_depth_sg_complete_main ν hν h B hB δc δg δl δa δn hm
    hK hT0 hc hδc hδg hδl hδa hδn hδ hδsum
  refine ⟨G,hG,hprob,?_⟩
  intro ω hω
  have hg := hgood ω hω
  have hpub := publicCoefficient_paper_le ν h B hB δa δn hK hT0
  have hb := global_budget_original_rate ν h B hB δc δg δl hm hK hT0
    hδc hδc1 hδg hδg1 hδl hδl1 ω
  have hlocal : ∀ u n : ℕ, u+n ≤ T → 0 < n →
      CNDPayment.intervalSum (actualLedger ν h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω ≤
        (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (n:ℝ)*(paperL0 K T δc δg δl)^2 := by
    intro u n hu hn
    exact (hg.1.2.1 u n hu hn).trans (exact_envelope_original_rate ν h B hB δc δg δl hm
      hK hT0 hδc hδc1 hδg hδg1 hδl hδl1 u n hu hn ω)
  refine ⟨hg,hlocal,hb,?_,?_⟩
  · intro u n hu hn path
    exact (hg.2.1 u n hu hn path).trans (add_le_add
      (mul_le_mul_of_nonneg_right hpub (Real.sqrt_nonneg _)) (hlocal u n hu hn))
  · intro path
    exact (hg.1.2.2.1 path).trans (add_le_add
      (mul_le_mul_of_nonneg_right hpub (Real.sqrt_nonneg _)) hb)

def defaultLog (K T : ℕ) (δ : ℝ) : ℝ := paperL0 K T (δ/5) (δ/5) (δ/5)

/-- Default five-way budget, pure logarithmic L0, original Hs*K*sqrt(n)
private rate and one private payment per interval/path. -/
theorem default_budget_sg_main_with_rates (hν : (ν:ℝ)^2=σ^2+σe^2)
    (h : Inputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm : CNDHorizon.SG.Laws (maps (K := K) ν (CNDNet.paperLc (Fin K) T (δ/5)) R M (B+2*D)
      h.R_nonneg (public_width_nonneg h hB)) (treeData (Nat.clog 2 T) K (B+2*D) R) h μ σ σe T)
    (hK : 2 ≤ K) (hT0 : 1 ≤ T)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω-h.publicCost t i ω ≤ B) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δ ∧ ∀ ω ∈ G,
      SGCompleteConclusions ν h B hB (δ/5) (δ/5) (δ/5) (δ/5) (δ/5) hm ω ∧
      (∀ u n : ℕ, u+n ≤ T → 0 < n →
        CNDPayment.intervalSum (actualLedger ν h B (CNDNet.paperLc (Fin K) T (δ/5)) hB hm) u n ω ≤
          (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (n:ℝ)*(defaultLog K T δ)^2) ∧
      (globalBudget ν h B (CNDNet.paperLc (Fin K) T (δ/5)) hB hm T (δ/5) ω ≤
        (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (T:ℝ)*(defaultLog K T δ)^2) ∧
      (∀ u n : ℕ, u+n ≤ T → 0 < n → ∀ path : ℕ → Fin K,
        intervalPathRegret h u n path ω ≤ paperPublicCoefficient ν K T B D (δ/5) (δ/5) *
          Real.sqrt ((n:ℝ)*((intervalSwitchCount u n path+1:ℕ):ℝ)) +
          (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (n:ℝ)*(defaultLog K T δ)^2) ∧
      (∀ path : ℕ → Fin K, pathRegret h T path ω ≤ paperPublicCoefficient ν K T B D (δ/5) (δ/5) *
        Real.sqrt ((T:ℝ)*((switchCount T path+1:ℕ):ℝ)) +
        (2496/CNDPhysical.c0)*(R+M+(ν:ℝ))*(K:ℝ)*Real.sqrt (T:ℝ)*(defaultLog K T δ)^2) := by
  simpa only [defaultLog] using paper_original_sg_main_with_rates ν hν h B hB
    (δ/5) (δ/5) (δ/5) (δ/5) (δ/5) hm hK hT0 hc
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hδ1 (by linarith)

end Part2.CNDHorizon.SGRate
