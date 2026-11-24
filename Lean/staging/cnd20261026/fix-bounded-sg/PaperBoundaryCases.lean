import staging.cnd20261026.«fix-bounded-sg».Boundaries

/-! Finite-input boundary wrappers. The singleton case has no realized regret
or private payment. The existing concentration envelope is retained verbatim;
it need not vanish when K = 1. No noise term is removed. -/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators NNReal
namespace Part2.CNDHorizon.PaperBoundaryCases

variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}

theorem bounded_zero_range_Q (h : BoundedInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (hR : R=0) (u n : ℕ) (ω : Ω) :
    FiniteBounded.actualBudgetQ (d:=d) h B L hB u n ω=0 := by
  simp [FiniteBounded.actualBudgetQ,CNDInformation.branchedQ,hR]

theorem sg_zero_range_Q (ν : ℝ≥0) (h : SGInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (hR : R=0) (u n : ℕ) (ω : Ω) :
    FiniteSG.actualBudgetQ (d:=d) ν h B L hB u n ω=0 := by
  simp [FiniteSG.actualBudgetQ,CNDInformation.branchedQ,hR]

theorem bounded_zero_range_globalBudget (h : BoundedInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (hR : R=0) (δg : ℝ) (ω : Ω) :
    FiniteBounded.globalBudget (d:=d) h B L hB δg ω=0 := by
  simp [FiniteBounded.globalBudget,bounded_zero_range_Q h B L hB hR,hR]

theorem sg_zero_range_globalBudget (ν : ℝ≥0) (h : SGInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (hR : R=0) (δg : ℝ) (ω : Ω) :
    FiniteSG.globalBudget (d:=d) ν h B L hB δg ω=0 := by
  simp [FiniteSG.globalBudget,sg_zero_range_Q ν h B L hB hR,hR]

theorem bounded_zero_range_exactPaymentEnvelope (h : BoundedInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (hR : R=0) (u n : ℕ) (δg δl : ℝ) (ω : Ω) :
    FiniteBounded.exactPaymentEnvelope (d:=d) h B L hB u n δg δl ω=0 := by
  simp [FiniteBounded.exactPaymentEnvelope,bounded_zero_range_Q h B L hB hR,
    bounded_zero_range_globalBudget h B L hB hR,hR]

theorem sg_zero_range_exactPaymentEnvelope (ν : ℝ≥0) (h : SGInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (hR : R=0) (u n : ℕ) (δg δl : ℝ) (ω : Ω) :
    FiniteSG.exactPaymentEnvelope (d:=d) ν h B L hB u n δg δl ω=0 := by
  simp [FiniteSG.exactPaymentEnvelope,sg_zero_range_Q ν h B L hB hR,
    sg_zero_range_globalBudget ν h B L hB hR,hR]

section Singleton
variable {θ : Fin 1 → ℝ}

theorem singleton_radius (p : ℕ → Fin 1 → ℝ) (t : ℕ) (H L R : ℝ) (i j : Fin 1) :
    CNDPhysical.actualSaturatedRadius p t H L R i j=0 := by
  rw [Subsingleton.elim j i]
  have hr : CNDPhysical.resistance p t i i=0 := by
    unfold CNDPhysical.resistance CND.gramDistance
    ring
  simp [CNDPhysical.actualSaturatedRadius,CNDPhysical.saturatedRadius,
    CNDPhysical.pairRadius,hr]

theorem singleton_Q (p : ℕ → Fin 1 → ℝ) (u n : ℕ) (H L R : ℝ) :
    CNDInformation.branchedQ (CNDInformation.canonicalChart (Fin 1)) p u n H L R=0 := by
  have hc : CNDInformation.canonicalChart (Fin 1)=0 := by
    ext i a
    have hh := CNDInformation.canonicalChart_column_sum (ι:=Fin 1) a
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    simpa using hh
  simp [CNDInformation.branchedQ,CNDInformation.actualQ,hc,
    CNDInformation.coordinateLogdet,CNDInformation.coordinateDesign,
    CNDInformation.matrixDesign,CNDInformation.coordinateCovariance]

theorem bounded_singleton_interval (h : BoundedInputs ℱ θ R M D T)
    (u n : ℕ) (k : Fin 1) (ω : Ω) : FiniteBounded.intervalRegret h u n k ω=0 := by
  unfold FiniteBounded.intervalRegret
  apply sum_eq_zero
  intro t ht
  rw [Subsingleton.elim (h.action t ω) k,sub_self]

theorem sg_singleton_interval (h : SGInputs ℱ θ R M D T)
    (u n : ℕ) (k : Fin 1) (ω : Ω) : FiniteSG.intervalRegret h u n k ω=0 := by
  unfold FiniteSG.intervalRegret
  apply sum_eq_zero
  intro t ht
  rw [Subsingleton.elim (h.action t ω) k,sub_self]

theorem bounded_singleton_ledger (h : BoundedInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (t : ℕ) (ω : Ω) :
    FiniteBounded.actualLedger (d:=d) h B L hB t ω=0 := by
  simp [FiniteBounded.actualLedger,ledger,CNDPhysicalRegret.payment,
    CNDPhysicalRegret.rowRadius,singleton_radius]

theorem sg_singleton_ledger (ν : ℝ≥0) (h : SGInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (t : ℕ) (ω : Ω) :
    FiniteSG.actualLedger (d:=d) ν h B L hB t ω=0 := by
  simp [FiniteSG.actualLedger,ledger,CNDPhysicalRegret.payment,
    CNDPhysicalRegret.rowRadius,singleton_radius]

theorem bounded_singleton_Q (h : BoundedInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (u n : ℕ) (ω : Ω) :
    FiniteBounded.actualBudgetQ (d:=d) h B L hB u n ω=0 :=
  singleton_Q _ u n _ _ _

theorem sg_singleton_Q (ν : ℝ≥0) (h : SGInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (u n : ℕ) (ω : Ω) :
    FiniteSG.actualBudgetQ (d:=d) ν h B L hB u n ω=0 :=
  singleton_Q _ u n _ _ _

private theorem log_bounds (T : ℕ) {δg δl : ℝ}
    (hg0 : 0<δg) (hg1 : δg≤1) (hl0 : 0<δl) (hl1 : δl≤1) :
    0≤Real.log (1/δg) ∧ 0≤Real.log ((T:ℝ)^2/δl) := by
  constructor
  · apply Real.log_nonneg
    exact (le_div_iff₀ hg0).mpr (by linarith)
  · by_cases ht0 : T=0
    · simp [ht0]
    · have ht : (1:ℝ)≤T := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ht0)
      apply Real.log_nonneg
      exact (le_div_iff₀ hl0).mpr (by nlinarith)

theorem bounded_singleton_conclusions (h : BoundedInputs ℱ θ R M D T)
    (B : ℝ) (hB : 0≤B) (δc δg δl δa δe : ℝ)
    (hg0 : 0<δg) (hg1 : δg≤1) (hl0 : 0<δl) (hl1 : δl≤1) (ω : Ω) :
    FiniteBounded.Conclusions (d:=d) h B hB δc δg δl δa δe ω := by
  have hR := h.R_nonneg
  have hD := h.D_nonneg
  have hc := CNDPhysical.c0_pos.le
  have hw := FiniteBounded.width_nonneg h hB
  obtain ⟨hlogg,hlogl⟩ := log_bounds T hg0 hg1 hl0 hl1
  have hb : 0≤FiniteBounded.globalBudget (d:=d) h B (CNDNet.paperLc (Fin 1) T δc) hB δg ω := by
    simp only [FiniteBounded.globalBudget,bounded_singleton_Q,mul_zero,zero_add]
    exact le_min (by positivity) (by positivity)
  have he (u n : ℕ) : 0≤FiniteBounded.exactPaymentEnvelope (d:=d) h B
      (CNDNet.paperLc (Fin 1) T δc) hB u n δg δl ω := by
    simp only [FiniteBounded.exactPaymentEnvelope,bounded_singleton_Q,mul_zero,zero_add]
    exact le_min (by positivity) (le_min (by positivity) hb)
  refine ⟨?_,?_,?_,?_⟩
  · intro u n hu hn k
    simp only [bounded_singleton_interval,CNDPayment.intervalSum,bounded_singleton_ledger,
      sum_const_zero,add_zero]
    positivity
  · intro u n hu hn
    simpa only [CNDPayment.intervalSum,bounded_singleton_ledger,sum_const_zero] using he u n
  · intro path
    rw [bounded_singleton_path]
    exact add_nonneg (mul_nonneg
      (BoundedMain.publicCoefficient_nonneg h.extend B hB d 1 T δa δe) (Real.sqrt_nonneg _)) hb
  · intro P
    simp [CNDPayment.intervalSum,bounded_singleton_ledger]

theorem sg_singleton_conclusions (ν : ℝ≥0) (h : SGInputs ℱ θ R M D T)
    (B : ℝ) (hB : 0≤B) (δc δg δl δa δn : ℝ)
    (hg0 : 0<δg) (hg1 : δg≤1) (hl0 : 0<δl) (hl1 : δl≤1) (ω : Ω) :
    FiniteSG.CompleteConclusions (d:=d) ν h B hB δc δg δl δa δn ω := by
  have hR := h.R_nonneg
  have hc := CNDPhysical.c0_pos.le
  have hw := FiniteSG.width_nonneg h hB
  obtain ⟨hlogg,hlogl⟩ := log_bounds T hg0 hg1 hl0 hl1
  have hp := SGMain.publicCoefficient_nonneg ν h.extend B hB d 1 T δa δn
  have hb : 0≤FiniteSG.globalBudget (d:=d) ν h B (CNDNet.paperLc (Fin 1) T δc) hB δg ω := by
    simp only [FiniteSG.globalBudget,sg_singleton_Q,mul_zero,zero_add]
    exact le_min (by positivity) (by positivity)
  have he (u n : ℕ) : 0≤FiniteSG.exactPaymentEnvelope (d:=d) ν h B
      (CNDNet.paperLc (Fin 1) T δc) hB u n δg δl ω := by
    simp only [FiniteSG.exactPaymentEnvelope,sg_singleton_Q,mul_zero,zero_add]
    exact le_min (by positivity) (le_min (by positivity) hb)
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩
  · intro u n hu hn k
    simp only [sg_singleton_interval,CNDPayment.intervalSum,sg_singleton_ledger,
      sum_const_zero,add_zero]
    positivity
  · intro u n hu hn
    simpa only [CNDPayment.intervalSum,sg_singleton_ledger,sum_const_zero] using he u n
  · intro path
    rw [sg_singleton_path]
    exact add_nonneg (mul_nonneg hp (Real.sqrt_nonneg _)) hb
  · intro P
    simp [CNDPayment.intervalSum,sg_singleton_ledger]
  · intro u n hu hn path
    have hz : FiniteSG.intervalPathRegret h u n path ω=0 := by
      unfold FiniteSG.intervalPathRegret
      apply sum_eq_zero
      intro t ht
      rw [Subsingleton.elim (h.action (u+t) ω) (path (u+t)),sub_self]
    simp only [hz,CNDPayment.intervalSum,sg_singleton_ledger,sum_const_zero,add_zero]
    exact mul_nonneg hp (Real.sqrt_nonneg _)
  · intro u n P
    simp [CNDPayment.intervalSum,sg_singleton_ledger]

theorem singleton_common_probability_one_event (ν : ℝ≥0)
    (hb : BoundedInputs ℱ θ R M D T) (hs : SGInputs ℱ θ R M D T)
    (B : ℝ) (hB : 0≤B) (δc δg δl δa δe δn : ℝ)
    (hg0 : 0<δg) (hg1 : δg≤1) (hl0 : 0<δl) (hl1 : δl≤1)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ G : Set Ω, MeasurableSet G ∧ μ G=1 ∧ μ.real Gᶜ=0 ∧ ∀ ω∈G,
      FiniteBounded.Conclusions (d:=d) hb B hB δc δg δl δa δe ω ∧
      FiniteSG.CompleteConclusions (d:=d) ν hs B hB δc δg δl δa δn ω := by
  refine ⟨Set.univ,MeasurableSet.univ,by simp,by simp,?_⟩
  intro ω hω
  exact ⟨bounded_singleton_conclusions hb B hB δc δg δl δa δe hg0 hg1 hl0 hl1 ω,
    sg_singleton_conclusions ν hs B hB δc δg δl δa δn hg0 hg1 hl0 hl1 ω⟩

end Singleton

/-- The per-user events may be dependent. Their model and Laws hypotheses
remain in the theorems supplying those events on the common measure space. -/
theorem finite_users_common_event {N : ℕ} (hN : 0<N) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Fin N → Set Ω) (hG : ∀ i,MeasurableSet (G i))
    (δ : ℝ) (hprob : ∀ i,μ.real (G i)ᶜ≤δ/(N:ℝ)) :
    MeasurableSet (⋂ i,G i) ∧ μ.real (⋂ i,G i)ᶜ≤δ := by
  refine ⟨MeasurableSet.iInter hG,?_⟩
  rw [Set.compl_iInter]
  calc
    μ.real (⋃ i,(G i)ᶜ) ≤ ∑ i,μ.real (G i)ᶜ := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin N,δ/(N:ℝ) := sum_le_sum (fun i _ => hprob i)
    _ = δ := by
      have hn : (N:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hN)
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

theorem finite_users_common_conclusions {N : ℕ} (hN : 0<N) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Fin N → Set Ω) (hG : ∀ i,MeasurableSet (G i))
    (δ : ℝ) (hprob : ∀ i,μ.real (G i)ᶜ≤δ/(N:ℝ))
    (P : Fin N → Ω → Prop) (hgood : ∀ i,∀ ω∈G i,P i ω) :
    ∃ H : Set Ω,MeasurableSet H ∧ μ.real Hᶜ≤δ ∧ ∀ ω∈H,∀ i,P i ω := by
  obtain ⟨hm,hp⟩ := finite_users_common_event hN μ G hG δ hprob
  refine ⟨⋂ i,G i,hm,hp,?_⟩
  intro ω hω i
  exact hgood i ω (Set.mem_iInter.mp hω i)

/-- Compose the certificates returned by the per-user main theorems, whose
original model and Laws hypotheses must still be supplied by the caller.
This probability bridge does not construct a physical simulator's joint law. -/
theorem finite_users_from_certificates {N : ℕ} (hN : 0<N) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (δ : ℝ) (P : Fin N → Ω → Prop)
    (huser : ∀ i,∃ G : Set Ω,MeasurableSet G ∧ μ.real Gᶜ≤δ/(N:ℝ) ∧
      ∀ ω∈G,P i ω) :
    ∃ H : Set Ω,MeasurableSet H ∧ μ.real Hᶜ≤δ ∧ ∀ ω∈H,∀ i,P i ω := by
  classical
  choose G hG hprob hgood using huser
  exact finite_users_common_conclusions hN μ G hG δ hprob P hgood

open FiniteBounded BoundedRate CNDProcess in
theorem default_budget_bounded_main_with_rates
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : BoundedInputs ℱ θ R M D T) (B : ℝ) (hB : 0≤B)
    {δ : ℝ} (hδ0 : 0<δ) (hδ1 : δ<1)
    (hm : BoundedLaws (maps h B (CNDNet.paperLc (Fin K) T (δ/5)) hB)
      (treeData (Nat.clog 2 T) K (B+2*D) R) h μ)
    (hK : 2≤K) (hT0 : 1≤T)
    (hc : ∀ t<T,∀ ω i j,h.publicCost t j ω-h.publicCost t i ω≤B) :
    ∃ G : Set Ω,MeasurableSet G ∧ μ.real Gᶜ≤δ ∧ ∀ ω∈G,
      Conclusions (d:=Nat.clog 2 T) h B hB (δ/5) (δ/5) (δ/5) (δ/5) (δ/5) ω ∧
      (∀ u n : ℕ,u+n≤T → 0<n →
        CNDPayment.intervalSum (actualLedger (d:=Nat.clog 2 T) h B
          (CNDNet.paperLc (Fin K) T (δ/5)) hB) u n ω≤
          (156/CNDPhysical.c0)*(R+M+D)*(K:ℝ)*Real.sqrt (n:ℝ)*
            (paperL0 K T (δ/5) (δ/5) (δ/5))^2) ∧
      (globalBudget (d:=Nat.clog 2 T) h B (CNDNet.paperLc (Fin K) T (δ/5)) hB (δ/5) ω≤
        (156/CNDPhysical.c0)*(R+M+D)*(K:ℝ)*Real.sqrt (T:ℝ)*
          (paperL0 K T (δ/5) (δ/5) (δ/5))^2) ∧
      (∀ path : ℕ → Fin K,pathRegret h path ω≤paperPublicCoefficient K T B D (δ/5) (δ/5)*
        Real.sqrt ((T:ℝ)*((BoundedMain.switchCount T path+1:ℕ):ℝ))+
        (156/CNDPhysical.c0)*(R+M+D)*(K:ℝ)*Real.sqrt (T:ℝ)*
          (paperL0 K T (δ/5) (δ/5) (δ/5))^2) := by
  exact paper_original_main_with_rates h B hB (δ/5) (δ/5) (δ/5) (δ/5) (δ/5)
    hm hK hT0 hc (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) hδ1 (by linarith)

end Part2.CNDHorizon.PaperBoundaryCases
