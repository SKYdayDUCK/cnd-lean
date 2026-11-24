import staging.cnd20261026.«fix-bounded-sg».SGFinal

noncomputable section
open MeasureTheory Finset
open scoped BigOperators NNReal
set_option maxHeartbeats 1600000
namespace Part2.CNDHorizon.SGMain
open CNDProcess CNDProcess.SG
variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {σ σe : ℝ}

def intervalPathRegret (h : Inputs ℱ θ R M D) (u n : ℕ) (path : ℕ → Fin K) (ω : Ω) : ℝ :=
  ∑ t ∈ range n, (h.physical (u+t) (h.action (u+t) ω) ω - h.physical (u+t) (path (u+t)) ω)

def intervalSwitchCount (u n : ℕ) (path : ℕ → Fin K) : ℕ :=
  switchCount n (fun t => path (u+t))

variable (ν : ℝ≥0) (h : Inputs ℱ θ R M D) (B : ℝ) (hB : 0 ≤ B)
  (δc δg δl δa δn : ℝ)
  (hm : CNDHorizon.SG.Laws (maps (K := K) ν (CNDNet.paperLc (Fin K) T δc) R M (B+2*D)
    h.R_nonneg (public_width_nonneg h hB)) (treeData d K (B+2*D) R) h μ σ σe T)

/-- Every interval admits every path chosen after the realized sample point.
Only the KT² fixed-arm noise union was used; no path union is needed. -/
theorem event_interval_posthoc_path (hL : 0 ≤ CNDNet.paperLc (Fin K) T δc)
    (hK : 2 ≤ K) (hT : T ≤ 2^d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω-h.publicCost t i ω ≤ B)
    (ω : Ω) (hω : MainEvent (d := d) (T := T) ν h B hB δc δg δl δa δn hm ω)
    (u n : ℕ) (hu : u+n ≤ T) (hn : 0 < n) (path : ℕ → Fin K) :
    intervalPathRegret h u n path ω ≤ publicCoefficient ν d K T B D δa δn *
      Real.sqrt ((n:ℝ)*((intervalSwitchCount u n path+1:ℕ):ℝ)) +
      CNDPayment.intervalSum (actualLedger ν h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω := by
  cases n with
  | zero => omega
  | succ N =>
    let w : ℕ → ℝ := fun t => actualLedger ν h B (CNDNet.paperLc (Fin K) T δc) hB hm (u+t) ω
    have hlocal : ∀ a b : ℕ, Icc a b ⊆ range (N+1) → ∀ k : Fin K,
        (∑ t ∈ Icc a b, (h.physical (u+t) (h.action (u+t) ω) ω-h.physical (u+t) k ω)) ≤
        publicCoefficient ν d K T B D δa δn*Real.sqrt ((Icc a b).card:ℝ) + ∑ t ∈ Icc a b, w t := by
      intro a b hsub k
      by_cases hab : a ≤ b
      · have hb := mem_range.mp (hsub (mem_Icc.mpr ⟨hab,le_rfl⟩))
        let len := b+1-a
        have hlen : 0 < len := by dsimp [len]; omega
        have he : a+len=b+1 := by dsimp [len]; omega
        have hi : Icc a b = Ico a (a+len) := by
          ext t
          simp only [mem_Icc,mem_Ico]
          omega
        have hcard : (Icc a b).card=len := by rw [Nat.card_Icc]
        have hl := event_interval_coefficient ν h B hB δc δg δl δa δn hm
          hL hK hT hc ω hω (u+a) len (by omega) hlen k
        unfold intervalRegret at hl
        rw [sum_Ico_eq_sum_range,sum_Ico_eq_sum_range] at hl
        simp only [Nat.add_sub_cancel_left] at hl
        rw [hcard,hi,sum_Ico_eq_sum_range,sum_Ico_eq_sum_range]
        simpa only [Nat.add_sub_cancel_left,Nat.add_assoc,w] using hl
      · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hab),sum_empty,card_empty,
          Nat.cast_zero,Real.sqrt_zero,mul_zero,add_zero,le_refl]
    have hp := SwitchingRuns.all_intervals_to_actual_path N (fun t => path (u+t))
      (fun t k => h.physical (u+t) k ω) (fun t => h.physical (u+t) (h.action (u+t) ω) ω)
      w (publicCoefficient ν d K T B D δa δn) (∑ t ∈ range (N+1), w t)
      (publicCoefficient_nonneg ν h B hB d K T δa δn) hlocal le_rfl
    simpa only [intervalPathRegret,intervalSwitchCount,switchCount,Nat.add_sub_cancel,
      CNDPayment.intervalSum,w] using hp

theorem ledger_interval_partition_exact (u n : ℕ) (P : Intervals.Partition (Ico u (u+n))) (ω : Ω) :
    (∑ j ∈ P.labels, ∑ t ∈ P.block j,
      actualLedger ν h B (CNDNet.paperLc (Fin K) T δc) hB hm t ω) =
    CNDPayment.intervalSum (actualLedger ν h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω := by
  rw [← sum_Ico_eq_intervalSum]
  exact P.sum_blocks _

def SGCompleteConclusions (ω : Ω) : Prop :=
  SGConclusions ν h B hB δc δg δl δa δn hm ω ∧
  (∀ u n : ℕ, u+n ≤ T → 0 < n → ∀ path : ℕ → Fin K,
    intervalPathRegret h u n path ω ≤ publicCoefficient ν d K T B D δa δn *
      Real.sqrt ((n:ℝ)*((intervalSwitchCount u n path+1:ℕ):ℝ)) +
      CNDPayment.intervalSum (actualLedger ν h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω) ∧
  (∀ u n : ℕ, ∀ P : Intervals.Partition (Ico u (u+n)),
    (∑ j ∈ P.labels, ∑ t ∈ P.block j,
      actualLedger ν h B (CNDNet.paperLc (Fin K) T δc) hB hm t ω) =
      CNDPayment.intervalSum (actualLedger ν h B (CNDNet.paperLc (Fin K) T δc) hB hm) u n ω)

/-- Complete SG6/SG7: one original event, all intervals, post-hoc paths,
the observable envelope and one exactly additive private ledger. -/
theorem original_sg_complete_main (hν : (ν:ℝ)^2=σ^2+σe^2)
    (hK : 2 ≤ K) (hT0 : 1 ≤ T) (hT : T ≤ 2^d)
    (hc : ∀ t < T, ∀ ω i j, h.publicCost t j ω-h.publicCost t i ω ≤ B)
    {δ : ℝ} (hδc : 0 < δc) (hδg : 0 < δg) (hδl : 0 < δl)
    (hδa : 0 < δa) (hδn : 0 < δn) (hδ : δ < 1)
    (hδsum : δc+δg+δl+δa+δn ≤ δ) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δ ∧
      ∀ ω ∈ G, SGCompleteConclusions ν h B hB δc δg δl δa δn hm ω := by
  have hL : 0 ≤ CNDNet.paperLc (Fin K) T δc :=
    le_trans (by norm_num) (CNDNet.paper_Lc_budget (ι := Fin K) T hδc (by linarith)).1
  obtain ⟨G,hG,hprob,hgood⟩ := original_run_main_event ν hν h B hB hK hT0 hT hc
    hδc (by linarith) hδg hδl hδa (by linarith) hδn (by linarith) hm
  refine ⟨G,hG,hprob.trans hδsum,?_⟩
  intro ω hω
  have hg := hgood ω hω
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩
  · exact event_interval_physical ν h B hB δc δg δl δa δn hm hL hK hT hc ω hg
  · exact event_payment_exact ν h B hB δc δg δl δa δn hm ω hg
  · exact event_posthoc_path ν h B hB δc δg δl δa δn hm hL hK hT0 hT hc ω hg
  · intro P
    exact ledger_partition_exact ν h B (CNDNet.paperLc (Fin K) T δc) hB hm T P ω
  · exact event_interval_posthoc_path ν h B hB δc δg δl δa δn hm hL hK hT hc ω hg
  · intro u n P
    exact ledger_interval_partition_exact ν h B hB δc hm u n P ω

end Part2.CNDHorizon.SGMain
