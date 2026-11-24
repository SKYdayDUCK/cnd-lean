import staging.cnd20261024.net.InformationEnergy
import staging.cnd20261024.net.NetExtension
import staging.cnd20261024.probability.SharpUniform

noncomputable section
set_option maxHeartbeats 1200000
open Finset MeasureTheory
namespace Part2.CNDNet
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def paperEpsilon (ι : Type*) [Fintype ι] (T : ℕ) : ℝ :=
  1 / (4 * (Fintype.card ι : ℝ) * (T + 1))

def paperNetCard (ι : Type*) [Fintype ι] (T : ℕ) : ℝ :=
  (1 + 8 * (Fintype.card ι : ℝ) * (T + 1)) ^ (Fintype.card ι - 1)

def paperLc (ι : Type*) [Fintype ι] (T : ℕ) (δ : ℝ) : ℝ :=
  Real.log (8 * ((T : ℝ) + 1)^2 / δ) +
    ((Fintype.card ι - 1 : ℕ) : ℝ) * Real.log (1 + 8 * (Fintype.card ι : ℝ) * (T + 1))

theorem paper_Lc_budget (T : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ paperLc ι T δ ∧
      paperNetCard ι T * (2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-paperLc ι T δ)) ≤ δ := by
  have ht : (0 : ℝ) ≤ T := by positivity
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hbase : 0 < 1 + 8 * (Fintype.card ι : ℝ) * (T + 1) := by positivity
  have hA : 0 < 8 * ((T : ℝ) + 1)^2 / δ := by positivity
  have hA4 : 4 ≤ 8 * ((T : ℝ) + 1)^2 / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith [sq_nonneg (T : ℝ)]
  have hlog2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog4 : 1 ≤ Real.log 4 := by
    have hh := Real.log_pow (2 : ℝ) 2
    norm_num at hh hlog2
    linarith
  have hlogA : 1 ≤ Real.log (8 * ((T : ℝ) + 1)^2 / δ) :=
    hlog4.trans (Real.log_le_log (by norm_num) hA4)
  have hlogbase : 0 ≤ Real.log (1 + 8 * (Fintype.card ι : ℝ) * (T + 1)) :=
    Real.log_nonneg (by nlinarith)
  have hLc : 1 ≤ paperLc ι T δ := by
    unfold paperLc
    exact hlogA.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hlogbase))
  have hN : 0 < paperNetCard ι T := by unfold paperNetCard; positivity
  have hexp : Real.exp (paperLc ι T δ) =
      (8 * ((T : ℝ) + 1)^2 / δ) * paperNetCard ι T := by
    unfold paperLc paperNetCard
    rw [← Real.log_pow, Real.exp_add, Real.exp_log hA, Real.exp_log (pow_pos hbase _)]
  have heq : paperNetCard ι T * (2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-paperLc ι T δ)) =
      δ / (4 * ((T : ℝ) + 1)) := by
    rw [Real.exp_neg, hexp]
    push_cast
    field_simp
    <;> ring
  refine ⟨hLc, ?_⟩
  rw [heq]
  apply (div_le_iff₀ (by positivity : 0 < 4 * ((T : ℝ) + 1))).2
  nlinarith

theorem paper_epsilon_bounds (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ Fintype.card ι) :
    0 < paperEpsilon ι T ∧ paperEpsilon ι T ≤ 1 / 16 ∧
      paperEpsilon ι T * Real.sqrt ((Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2)) ≤ 1 / 8 := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hk : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hK
  have hprod : 4 ≤ (Fintype.card ι : ℝ) * (T + 1) := by nlinarith
  have hden : 0 < 4 * (Fintype.card ι : ℝ) * (T + 1) := by positivity
  have he : paperEpsilon ι T ≤ 1 / 16 := by
    unfold paperEpsilon
    apply (div_le_iff₀ hden).2
    nlinarith
  have hroot := Real.sqrt_nonneg ((Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2))
  have hsquare := Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2))
  have hrootbound : Real.sqrt ((Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2)) ≤
      ((Fintype.card ι : ℝ) * (T + 1)) / 2 := by
    have hm : (Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2) ≤
        (Fintype.card ι : ℝ) * (T + 1) := by nlinarith
    nlinarith [sq_nonneg ((Fintype.card ι : ℝ) * (T + 1) / 2 - 1)]
  refine ⟨by unfold paperEpsilon; positivity, he, ?_⟩
  unfold paperEpsilon
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ hden).2
  nlinarith

def statisticLinear (Z : ι → ℝ) : ZeroSum ι →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x.val i * Z i
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_assoc, Finset.mul_sum]

/-- An actual deterministic net is constructed before proving the extension implication.
The conclusion is CND-MAIN (11), with the actual information matrix and original constants. -/
theorem exists_paper_net_extension (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ Fintype.card ι) :
    ∃ s : Finset (ZeroSum ι), (∀ b ∈ s, oscillation b.val = 1) ∧
      (s.card : ℝ) ≤ paperNetCard ι T ∧
      ∀ (p : ℕ → ι → ℝ), (∀ t, p t ∈ CND.simplex) →
      ∀ n ≤ T, ∀ H L : ℝ, 0 ≤ H → 1 ≤ L → ∀ Z : ι → ℝ,
      (∀ b ∈ s, |∑ i, b.val i * Z i| ≤
        2 * H * Real.sqrt L * informationEnergy p n b.val + 2 * H * L) →
      ∀ u : ι → ℝ, (∑ i, u i) = 0 →
        |∑ i, u i * Z i| ≤
          2 * H * Real.sqrt (L * CND.quadratic (CNDPhysical.information p n) u) +
            4 * H * L * oscillation u := by
  obtain ⟨s, hs, hcard, hnet⟩ := exists_paper_net (ι := ι) T
  refine ⟨s, hs, hcard, ?_⟩
  intro p hp n hn H L hH hL Z hfinite u hu
  letI : NormedAddCommGroup (ZeroSum ι) :=
    NormedAddCommGroup.induced _ _ (differenceMap (ι := ι)).toAddMonoidHom differenceMap_injective
  letI : MetricSpace (ZeroSum ι) := (inferInstance : NormedAddCommGroup (ZeroSum ι)).toMetricSpace
  letI : PseudoMetricSpace (ZeroSum ι) := (inferInstance : MetricSpace (ZeroSum ι)).toPseudoMetricSpace
  letI : UniformSpace (ZeroSum ι) := (inferInstance : PseudoMetricSpace (ZeroSum ι)).toUniformSpace
  letI : SeminormedAddCommGroup (ZeroSum ι) :=
    (inferInstance : NormedAddCommGroup (ZeroSum ι)).toSeminormedAddCommGroup
  letI : TopologicalSpace (ZeroSum ι) :=
    (inferInstance : NormedAddCommGroup (ZeroSum ι)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedSpace ℝ (ZeroSum ι) := NormedSpace.induced ℝ _ _ (differenceMap (ι := ι))
  let F : ZeroSum ι →L[ℝ] ℝ := (statisticLinear Z).toContinuousLinearMap
  let e : Seminorm ℝ (ZeroSum ι) :=
    (informationEnergy p n).comp (LinearMap.ker (sumLinear (ι := ι))).subtype
  let C : ℝ := Real.sqrt ((Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2))
  have he : ∀ a : ZeroSum ι, e a ≤ C * ‖a‖ := by
    intro a
    exact energy_upper p hp n T hn hK a.val a.property
  obtain ⟨hε, hε16, hεC⟩ := paper_epsilon_bounds (ι := ι) T hT hK
  have hnet' : ∀ a : ZeroSum ι, ‖a‖ = 1 → ∃ b ∈ s, ‖a - b‖ ≤ paperEpsilon ι T := hnet
  have hs' : ∀ b ∈ s, ‖b‖ = 1 := hs
  have hf : ∀ b ∈ s, ‖F b‖ ≤ (2 * H * Real.sqrt L) * e b + 2 * H * L := hfinite
  have hL0 : 0 ≤ L := by linarith
  have hA0 : 0 ≤ 2 * H * Real.sqrt L := by positivity
  have hB0 : 0 ≤ 2 * H * L := by positivity
  have hh := extend_all s hε.le (by linarith) hA0 hB0
    (Real.sqrt_nonneg _) hs' hnet' e he F hf (⟨u, hu⟩ : ZeroSum ι)
  have herr := extension_error_bound hε.le hε16
    (by positivity : 0 ≤ 2 * H * Real.sqrt L) (by positivity : 0 ≤ 2 * H * L)
    (Real.sqrt_nonneg _) hεC
  have hsqrtL : Real.sqrt L ≤ L := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ L), Real.sqrt_nonneg L]
  have herr' : 2 * H * Real.sqrt L * C * paperEpsilon ι T +
      paperEpsilon ι T * ((2 * H * Real.sqrt L * C + 2 * H * L) /
        (1 - paperEpsilon ι T)) ≤ 2 * H * L := by
    dsimp [C] at *
    nlinarith
  have henergyroot : Real.sqrt (L * CND.quadratic (CNDPhysical.information p n) u) =
      Real.sqrt L * informationEnergy p n u := by
    rw [← energy_actual_information p hp n u, Real.sqrt_mul (by linarith : 0 ≤ L),
      Real.sqrt_sq (apply_nonneg _ _)]
  rw [henergyroot]
  change |∑ i, u i * Z i| ≤ _ at hh
  change _ ≤ 2 * H * Real.sqrt L * informationEnergy p n u +
    (2 * H * L + 2 * H * Real.sqrt L * C * paperEpsilon ι T +
      paperEpsilon ι T * ((2 * H * Real.sqrt L * C + 2 * H * L) /
      (1 - paperEpsilon ι T))) * oscillation u at hh
  nlinarith [mul_nonneg (sub_nonneg.mpr herr') (oscillation_nonneg u)]

theorem bernstein_threshold_to_energy (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ CND.simplex) (n : ℕ) (b : ι → ℝ)
    (hb : oscillation b = 1) {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) :
    H * Real.sqrt (2 * (1 + ∑ t ∈ Finset.range n,
        CNDProbability.directionVariance (p t) b) * L) + (4 / 3) * H * L ≤
      2 * H * Real.sqrt L * informationEnergy p n b + 2 * H * L := by
  have hbase := square_sum_lower b
  rw [hb] at hbase
  have he := energy_square_variance p hp n b
  have he0 := apply_nonneg (informationEnergy p n) b
  have hq : 0 ≤ ∑ t ∈ Finset.range n, CNDProbability.directionVariance (p t) b :=
    Finset.sum_nonneg fun t _ => CNDProbability.directionVariance_nonneg _ _ (hp t).1
  have hrad : 2 * (1 + ∑ t ∈ Finset.range n,
      CNDProbability.directionVariance (p t) b) * L ≤
      4 * (L * (informationEnergy p n b)^2) := by nlinarith
  have hr := Real.sqrt_le_sqrt hrad
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_mul hL,
    Real.sqrt_sq he0] at hr
  rw [show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hr
  have hscaled := mul_le_mul_of_nonneg_left hr hH
  nlinarith [mul_nonneg hH hL]

section Probability
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}

/-- Actual original-space full-direction event, after constructing and eliminating the net.
No finite family or covering property is supplied as a hypothesis. -/
theorem actual_uniform_direction_event (h : CNDProbability.M1Model ℱ μ θ R M D)
    (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ Fintype.card ι)
    (hH : 0 < R + M + D) {L : ℝ} (hL : 1 ≤ L) :
    ∃ G : Set Ω,
      μ.real Gᶜ ≤ paperNetCard ι T * (2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-L)) ∧
      ∀ ω ∈ G, ∀ n ≤ T, ∀ u : ι → ℝ, (∑ i, u i) = 0 →
        |∑ i, u i * h.coordinateSum n i ω| ≤
          2 * (R + M + D) * Real.sqrt (L * CND.quadratic
            (CNDPhysical.information (fun t i => h.p t i ω) n) u) +
              4 * (R + M + D) * L * oscillation u := by
  classical
  obtain ⟨s, hs, hcard, hextend⟩ := exists_paper_net_extension (ι := ι) T hT hK
  let α := {b // b ∈ s}
  let b : α → ι → ℝ := fun a => a.val.val
  let bad : Set Ω := {ω | ∃ a : α, ∃ n ≤ T,
    (R + M + D) * Real.sqrt (2 * (1 + Bernstein.sumProcess
      (CNDProbability.Directional.information h.statistics (b a)) n ω) * L) +
    (4 / 3) * (R + M + D) * L ≤ |Bernstein.sumProcess
      (CNDProbability.Directional.increment h.statistics (b a)) n ω|}
  have hb : ∀ a i j, |b a i - b a j| ≤ 1 := by
    intro a i j
    exact (pairwise_le_oscillation a.val.val i j).trans_eq (hs a.val a.property)
  have hprob := h.finite_direction_family b hb hH T (show 0 < L by linarith)
  refine ⟨badᶜ, ?_, ?_⟩
  · simp only [compl_compl]
    change μ.real bad ≤ _
    have hca : (Fintype.card α : ℝ) ≤ paperNetCard ι T := by simpa [α] using hcard
    exact hprob.trans (mul_le_mul_of_nonneg_right hca (by positivity))
  · intro ω hω n hn u hu
    have hp : ∀ t, (fun i => h.p t i ω) ∈ CND.simplex :=
      fun t => ⟨fun i => h.p_nonneg t ω i, h.p_sum t ω⟩
    apply hextend (fun t i => h.p t i ω) hp n hn (R + M + D) L hH.le hL
      (fun i => h.coordinateSum n i ω) _ u hu
    intro v hv
    let a : α := ⟨v, hv⟩
    have hnot : ¬ ((R + M + D) * Real.sqrt (2 * (1 +
        Bernstein.sumProcess (CNDProbability.Directional.information h.statistics (b a)) n ω) * L) +
        (4 / 3) * (R + M + D) * L ≤ |Bernstein.sumProcess
        (CNDProbability.Directional.increment h.statistics (b a)) n ω|) := by
      intro hc
      exact hω ⟨a, n, hn, hc⟩
    have hstrict := lt_of_not_ge hnot
    rw [h.direction_sum_eq_coordinates] at hstrict
    have hthreshold := bernstein_threshold_to_energy (fun t i => h.p t i ω) hp n v.val
      (hs v hv) (by linarith : 0 ≤ L) hH.le
    exact hstrict.le.trans hthreshold

theorem actual_uniform_direction_event_paper (h : CNDProbability.M1Model ℱ μ θ R M D)
    (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ Fintype.card ι)
    (hH : 0 < R + M + D) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ G : Set Ω, μ.real Gᶜ ≤ δ ∧
      ∀ ω ∈ G, ∀ n ≤ T, ∀ u : ι → ℝ, (∑ i, u i) = 0 →
        |∑ i, u i * h.coordinateSum n i ω| ≤
          2 * (R + M + D) * Real.sqrt (paperLc ι T δ * CND.quadratic
            (CNDPhysical.information (fun t i => h.p t i ω) n) u) +
              4 * (R + M + D) * paperLc ι T δ * oscillation u := by
  obtain ⟨hL, hbudget⟩ := paper_Lc_budget (ι := ι) T hδ hδ1
  obtain ⟨G, hG, hbound⟩ := actual_uniform_direction_event h T hT hK hH hL
  exact ⟨G, hG.trans hbudget, hbound⟩

end Probability

end Part2.CNDNet
