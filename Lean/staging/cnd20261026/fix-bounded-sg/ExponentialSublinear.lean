import Part2.ExponentialSafeCover
import staging.cnd20261026.«fix-bounded-sg».ExponentialFiniteGap
import staging.cnd20261026.«fix-bounded-sg».ExponentialSGFinite
import staging.cnd20261026.«fix-bounded-sg».ExponentialPaymentRate

/-! A horizon-scaled learning-rate band for the existing ECND update.
Every path is compared on its maximal constant-server runs. Each cover piece
uses an expert at the start of its active interval, with the original prior. -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators ProbabilityTheory NNReal
set_option maxHeartbeats 2400000

namespace Part2.ExponentialSublinear

open ExponentialComposition ExponentialExperts ExponentialRemainder ExponentialSafeRate

variable {E ι Ω : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

/-- The schedule supplies only rate, prior, and interval geometry. -/
structure Schedule (v : Trajectory E ι Ω) (T : ℕ) (W : ℝ) (pieces : ℕ) where
  lower : ∀ e, rateLower T (2 * W) ≤ v.eta e
  upper : ∀ e, v.eta e ≤ rateUpper T (2 * W)
  prior : ∀ e ω, v.weight 0 e ω = 1 / (Fintype.card E : ℝ)
  cover : ∀ u n, u + n ≤ T → 0 < n → ∀ k,
    ∃ C : ExponentialCovers.Cover T v.active v.arm k (Ico u (u + n)),
      C.partition.labels.card ≤ pieces ∧
      ∀ j ∈ C.partition.labels, ∀ t < C.start j, C.expert j ∉ v.active t

def expertCost (T count : ℕ) (W : ℝ) : ℝ :=
  2 * (2 * W) * Real.sqrt (T : ℝ) * (Real.log (count : ℝ) + kappa 1)

omit [DecidableEq E] in
private theorem expertCost_nonneg (T : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    0 ≤ expertCost T (Fintype.card E) W := by
  have hc : (1 : ℝ) ≤ Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  have hlog := Real.log_nonneg hc
  have hk := kappa_one_nonneg
  unfold expertCost
  positivity

variable [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ} {T pieces : ℕ} {W : ℝ}
  {h : CNDProbability.M1Model ℱ μ θ R M D}
  {a : ℕ → ι → Ω → ℝ} {r : ℕ → ι → ι → Ω → ℝ}
  {v : Trajectory E ι Ω}

omit [Nonempty E] [MeasurableSingletonClass ι] [Nonempty ι] [IsProbabilityMeasure μ] in
private theorem excess_abs (hv : Laws h a r v T W) (t : ℕ) (e : E) (ω : Ω) :
    |excess h a r v t e ω| ≤ 2 * W := by
  unfold excess
  rw [CNDPhysicalRegret.transported_mixture _ _ _ _ (hv.conservation t ω)]
  apply CNDProd.averages_abs_sub_le (fun i => h.p t i ω)
      (fun j => v.transport t (v.arm e) j ω) (fun i => ExponentialPhysical.loss h a r t i ω) (2 * W)
      (h.p_nonneg t ω) (hv.row_nonneg t ω (v.arm e)) (h.p_sum t ω)
      (hv.row_sum t ω (v.arm e))
  intro i j hi hj
  exact hv.support_span t ω i j (lt_of_le_of_ne (h.p_nonneg t ω i) hi.symm)
    (hv.row_support t ω (v.arm e) j (lt_of_le_of_ne (hv.row_nonneg t ω (v.arm e) j) hj.symm))

omit [MeasurableSingletonClass ι] [IsProbabilityMeasure μ] in
private theorem exponent_zero (hv : Laws h a r v T W) (t : ℕ) (ht : t < T) (ω : Ω) :
    (∑ e, v.weight t e ω * exponent h a r v t e ω) = 0 := by
  let w := fun n e => v.weight n e ω
  let z := fun n e => exponent h a r v n e ω
  let d := fun e k => if v.arm e = k then (1 : ℝ) else 0
  let l := CNDPhysicalRegret.transported (fun i j => v.transport t i j ω)
    (fun i => ExponentialPhysical.loss h a r t i ω)
  have hp := trajectory_pos T w z (fun e => hv.initial_pos e ω) (fun n hn e => hv.update n hn e ω)
  have hd := Prod.denominator_pos (v.active t) v.eta (w t)
    (fun e _ => hv.eta_pos e) (fun e _ => hp t ht.le e)
    ⟨hv.root Classical.ofNonempty, hv.root_awake t ht Classical.ofNonempty⟩
  have hz (e : E) : z t e =
      sleepingExponent (v.active t) v.eta (Prod.excess (v.active t) v.eta (w t) d l) e := by
    by_cases he : e ∈ v.active t
    · simp only [z, exponent, sleepingExponent, Prod.excess, if_pos he]
      simp [excess, recommendation, Prod.mixtureLoss, Prod.adviceLoss, CNDPhysicalRegret.avg,
        w, d, l]
    · simp [z, exponent, sleepingExponent, he]
  change (∑ e, w t e * z t e) = 0
  simp_rw [hz]
  exact sleeping_advice_zero (v.active t) v.eta (w t) d l hd.ne'

theorem envelope_le (hv : Laws h a r v T W) (hT : 0 < T) (hW : 0 < W)
    (hs : Schedule v T W pieces) (u n : ℕ) (hu : u + n ≤ T) (hn : 0 < n)
    (k : ι) (ω : Ω) :
    envelope h a r v T W u n k ω ≤ (pieces : ℝ) * expertCost T (Fintype.card E) W := by
  obtain ⟨C, hcard, hbirth⟩ := hs.cover u n hu hn k
  let w := fun t e => v.weight t e ω
  let x := fun t e => excess h a r v t e ω
  let z := fun t e => exponent h a r v t e ω
  have hupdate : ∀ t < T, ∀ e, w (t+1) e = step (w t) (z t) e :=
    fun t ht e => hv.update t ht e ω
  have hcost := ExponentialSafeCover.cover_cost_le C (2 * W) hT (by positivity)
    v.eta w x hs.lower hs.upper (fun e => hs.prior e ω) hupdate
    (fun t ht => exponent_zero hv t ht ω) (fun t _ e _ => excess_abs hv t e ω) hbirth
  have hbdd : BddBelow (Set.range fun A : ExponentialCovers.Cover T v.active v.arm k
      (Ico u (u + n)) => A.totalCost w z v.eta) := by
    refine ⟨∑ t ∈ Ico u (u + n), ExponentialPhysical.proxyRegret h a r k t ω, ?_⟩
    rintro _ ⟨A, rfl⟩
    apply ExponentialCovers.cover_regret A w z x v.eta
      (fun t => ExponentialPhysical.proxyRegret h a r k t ω) hv.eta_pos
      (fun e => hv.initial_pos e ω) hupdate
    · intro t _ e he
      simp [z, exponent, he, x]
    · intro t _ e _ hk
      simpa only [hk] using actual_gap h a r v hv t ω e
  unfold envelope
  rw [if_neg (Nat.ne_of_gt hn)]
  calc
    _ ≤ sInf (Set.range fun A : ExponentialCovers.Cover T v.active v.arm k
        (Ico u (u + n)) => A.totalCost w z v.eta) := min_le_right _ _
    _ ≤ C.totalCost w z v.eta := csInf_le hbdd ⟨C, rfl⟩
    _ ≤ (C.partition.labels.card : ℝ) * expertCost T (Fintype.card E) W := hcost
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (expertCost_nonneg T hW.le)

theorem path_envelope_le (hv : Laws h a r v T W) (hT : 0 < T) (hW : 0 < W)
    (hs : Schedule v T W pieces) (path : ℕ → ι) (ω : Ω) :
    (∑ j ∈ (SwitchingRuns.partition path T).labels,
      envelope h a r v T W (runStart path T j) (runLength path T j)
        (SwitchingRuns.label path T j) ω) ≤
      ((switchCount T path + 1 : ℕ) : ℝ) *
        (pieces : ℝ) * expertCost T (Fintype.card E) W := by
  calc
    _ ≤ ∑ _j ∈ (SwitchingRuns.partition path T).labels,
        (pieces : ℝ) * expertCost T (Fintype.card E) W := by
      apply sum_le_sum
      intro j hj
      obtain ⟨_, hu, hn⟩ := maximal_run_geometry path T j hj
      exact envelope_le hv hT hW hs _ _ hu hn _ ω
    _ = _ := by rw [sum_const, nsmul_eq_mul, maximal_run_card path T hT]; ring

section Finite

open CNDHorizon BoundedRate ExponentialPaymentRate

variable {K : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {theta : Fin K → ℝ}

/-- The bounded model's high-probability path rate, in the original actions
and physical losses. The comparator and its switches can be chosen in hindsight. -/
theorem bounded_dynamic_regret
    (f : BoundedInputs ℱ theta R M D T) (hW : 0 < W)
    (c : ExponentialFinite.Config (K := K) (E := E) T R W)
    {δc δa δe δg δl : ℝ}
    (hm : ExponentialFinite.Protocol f (CNDNet.paperLc (Fin K) T δc) hW c (μ := μ))
    (hs : Schedule (ExponentialFinite.trajectory f (CNDNet.paperLc (Fin K) T δc) hW c)
      T W pieces)
    (hK : 2 ≤ K) (hT : 1 ≤ T)
    (hc : c.confidence_scale = 1) (hr : c.radius_scale = 1)
    (hb : ∀ t < T, ∀ ω i j, f.broadcast t ω j - f.broadcast t ω i ≤ W)
    (hδc : 0 < δc) (hδc1 : δc ≤ 1)
    (ha : 0 < δa) (ha1 : δa < 1) (he : 0 < δe) (he1 : δe < 1)
    (hg : 0 < δg) (hg1 : δg ≤ 1) (hl : 0 < δl) (hl1 : δl ≤ 1) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc + δa + δe + (δg + δl) ∧
      ∀ ω ∈ G, ∀ path : ℕ → Fin K,
        (∑ t ∈ range T, (f.physical t (f.action t ω) ω - f.physical t (path t) ω)) ≤
          ((switchCount T path + 1 : ℕ) : ℝ) * (pieces : ℝ) *
            expertCost T (Fintype.card E) W +
          ExponentialPhysical.noiseCoefficient (ι := Fin K) (D := D) W T δa δe *
            Real.sqrt ((T : ℝ) * ((switchCount T path + 1 : ℕ) : ℝ)) +
          (156 / CNDPhysical.c0) * (R + M + D) * (K : ℝ) * Real.sqrt (T : ℝ) *
            (paperL0 K T δc δg δl) ^ 2 := by
  let L := CNDNet.paperLc (Fin K) T δc
  obtain ⟨hlog, hL, hLup, _, _, hglobal, hglobalup, _, hinfo⟩ :=
    paper_parameters hK hT hδc hδc1 hg hg1 hl hl1
  obtain ⟨G, hG, hprob, hgood⟩ := ExponentialFiniteGap.unit_scale_budget_main
    f L hW c hm hK hT hc hr hb hδc hδc1 ha ha1 he he1 hg hl rfl
  let hv := ExponentialFinite.compositionLaws f L hW c hm hL hb
  refine ⟨G, hG, hprob, ?_⟩
  intro ω hω path
  have hexpert := path_envelope_le hv hT hW hs path ω
  have hpay := canonical_payment_envelope_le (ExponentialFinite.model f L hW c hm)
    (R + M + D) L (paperL0 K T δc δg δl) δg δl hK hT
    (by linarith [f.M_nonneg, f.D_nonneg]) hlog hL hLup hinfo hglobal hglobalup ω
  have hraw := (hgood ω hω).2.1.2 path
  simp only [ExponentialFiniteGap.budgetLedger, Nat.ne_of_gt hT, if_false,
    Bool.false_eq_true, add_zero] at hraw
  exact hraw.trans (add_le_add_right (add_le_add_right hexpert _) _ |>.trans (add_le_add_left hpay _))

/-- The conditionally sub-Gaussian analogue with the same schedule and
deterministic private-payment bound. -/
theorem sg_dynamic_regret
    (f : SGInputs ℱ theta R M D T) (ν : ℝ≥0) (hW : 0 < W)
    (c : ExponentialFinite.Config (K := K) (E := E) T R W)
    {σ σe δc δa δn δg δl : ℝ}
    (hm : ExponentialSGFinite.Protocol f ν (4 * CNDNet.paperLc (Fin K) T δc)
      hW.le c (μ := μ) (σ := σ) (σe := σe))
    (hs : Schedule (ExponentialSGFinite.trajectory f ν (4 * CNDNet.paperLc (Fin K) T δc)
      hW.le c) T W pieces)
    (hν : (ν : ℝ)^2 = σ^2 + σe^2)
    (hK : 2 ≤ K) (hT : 1 ≤ T)
    (hc : c.confidence_scale = 1) (hr : c.radius_scale = 1)
    (hb : ∀ t < T, ∀ ω i j, f.broadcast t ω j - f.broadcast t ω i ≤ W)
    (hδc : 0 < δc) (hδc1 : δc ≤ 1)
    (ha : 0 < δa) (ha1 : δa < 1) (hn : 0 < δn) (hn1 : δn < 1)
    (hg : 0 < δg) (hg1 : δg ≤ 1) (hl : 0 < δl) (hl1 : δl ≤ 1) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ.real Gᶜ ≤ δc + δa + δn + (δg + δl) ∧
      ∀ ω ∈ G, ∀ path : ℕ → Fin K,
        (∑ t ∈ range T, (f.physical t (f.action t ω) ω - f.physical t (path t) ω)) ≤
          ((switchCount T path + 1 : ℕ) : ℝ) * (pieces : ℝ) *
            expertCost T (Fintype.card E) W +
          ExponentialSGPhysical.noiseCoefficient (ι := Fin K) ν W T δa δn *
            Real.sqrt ((T : ℝ) * ((switchCount T path + 1 : ℕ) : ℝ)) +
          (468 / CNDPhysical.c0) * (R + M + (ν : ℝ)) * (K : ℝ) * Real.sqrt (T : ℝ) *
            (paperL0 K T δc δg δl) ^ 2 := by
  let L := 4 * CNDNet.paperLc (Fin K) T δc
  let Λ := paperL0 K T δc δg δl
  obtain ⟨hΛ, hLc, hLcup, _, _, hglobal, hglobalup, _, hinfo⟩ :=
    paper_parameters hK hT hδc hδc1 hg hg1 hl hl1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLup : L ≤ 4 * (K : ℝ) * Λ := by dsimp [L, Λ]; linarith
  obtain ⟨G, hG, hprob, hgood⟩ := ExponentialSGFinite.original_legal_budget_main
    f ν hW.le c hδc hδc1 hν hT hK hW hc hr hm hb ha ha1 hn hn1 hg hl
  let hv := ExponentialSGFinite.compositionLaws f ν L hW.le c hm hL hW hb
  refine ⟨G, hG, hprob, ?_⟩
  intro ω hω path
  have hexpert := path_envelope_le hv hT hW hs path ω
  have hpay := sg_payment_envelope_le (ExponentialSGFinite.model f ν L hW.le c hm).toM1Model
    (R + M + (ν : ℝ)) L Λ δg δl hK hT
    (by linarith [f.M_nonneg, ν.coe_nonneg]) hΛ hL hLup hinfo hglobal hglobalup ω
  have hactual := (hgood ω hω).2 0 T (by simp) hT
  have hraw := (hgood ω hω).1.2 path
  simp only [ExponentialSGFinite.pathBound, Bool.false_eq_true, if_false, add_zero] at hraw
  exact hraw.trans (add_le_add (add_le_add_right hexpert _) (hactual.trans hpay))

section AllIntervals

open CNDProcess

/-- One expert for each arm and pair of endpoints. Pairs with the end at
or before the start are always asleep. The bank has polynomial size in T. -/
abbrev IntervalExpert (T K : ℕ) := Fin T × Fin (T + 1) × Fin K

theorem interval_expert_count (T K : ℕ) :
    Fintype.card (IntervalExpert T K) = K * T * (T + 1) := by
  simp only [IntervalExpert, Fintype.card_prod, Fintype.card_fin]
  ring

variable [Nonempty (Fin T)]

def allIntervalConfig (R : ℝ) (hT : 0 < T) (hW : 0 < W) :
    ExponentialFinite.Config (K := K) (E := IntervalExpert T K) T R W where
  data :=
    { active := fun t e => decide (e.1.val ≤ t ∧ t < e.2.1.val)
      arm := fun e => e.2.2
      eta := fun _ => rateUpper T (2 * W)
      W := W
      R := R }
  prior := fun _ => 1 / (Fintype.card (IntervalExpert T K) : ℝ)
  width_eq := rfl
  range_eq := rfl
  eta_pos := fun _ => (canonical_rate_admissible T (2 * W) hT (by positivity)).2
  prior_pos := by
    intro e
    have h := Fintype.card_pos (α := IntervalExpert T K)
    positivity
  root := fun k => (⟨0, hT⟩, ⟨T, Nat.lt_succ_self T⟩, k)
  root_arm := fun _ => rfl
  root_awake := by
    intro t ht k
    simp [activeSet, ht]
  confidence_nonneg := by norm_num
  radius_nonneg := by norm_num

omit [MeasurableSingletonClass (Fin K)] in
/-- Every nonempty interval has an expert that starts exactly at its left
endpoint, so every constant-comparator run requires one cover piece.
For a sparser interval bank, use `Schedule` with its cover size. -/
theorem all_interval_schedule (hT : 0 < T) (hW : 0 < W) (H L : ℝ) (hR : 0 ≤ R)
    (feedback : Feedback (ι := Fin K) ℱ) :
    Schedule (ExponentialActual.trajectory H L hR hW.le (allIntervalConfig (K := K) R hT hW)
      feedback) T W 1 := by
  let c := allIntervalConfig (K := K) R hT hW
  let v := ExponentialActual.trajectory H L hR hW.le c feedback
  change Schedule v T W 1
  refine ⟨fun _ => (canonical_rate_admissible T _ hT (by positivity)).1,
    fun _ => le_rfl, fun _ _ => rfl, ?_⟩
  intro u n hu hn k
  let e : IntervalExpert T K := (⟨u, by omega⟩, ⟨u + n, by omega⟩, k)
  have hactive (t : ℕ) (ht : t < T) : e ∈ v.active t ↔ u ≤ t ∧ t < u + n := by
    simp [v, ExponentialActual.trajectory, ht, c, allIntervalConfig, activeSet, e]
  let C : ExponentialCovers.Cover T v.active v.arm k (Ico u (u + n)) :=
    { partition := ExponentialCovers.singlePartition _
      start := fun _ => u
      length := fun _ => n
      expert := fun _ => e
      block_eq := fun _ _ => rfl
      length_pos := fun _ _ => hn
      within := fun _ _ => hu
      awake := by
        intro _ _ t ht
        change t ∈ Ico u (u + n) at ht
        have ht' := mem_Ico.mp ht
        exact (hactive t (by omega)).2 ht'
      same_arm := fun _ _ => rfl }
  refine ⟨C, by simp [C, ExponentialCovers.singlePartition], ?_⟩
  intro _ _ t ht
  change e ∉ v.active t
  rw [hactive t (by change t < u at ht; omega)]
  change t < u at ht
  omega

end AllIntervals

end Finite

end Part2.ExponentialSublinear
