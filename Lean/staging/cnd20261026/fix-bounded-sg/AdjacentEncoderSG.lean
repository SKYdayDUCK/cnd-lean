import staging.cnd20261026.«fix-bounded-sg».FiniteLaws
import Mathlib.Probability.Moments.SubGaussian

/-!
Adjacent-grid encoding with a random, physically measurable cell position.
Conditional unbiasedness is required after the physical noise and action have
been revealed. It is the fresh encoding protocol's law, not independence of the
error from its random cell position. The enclosing interval has width Δ, rather
than the width 2Δ of the coarse absolute-error bound.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Part2.AdjacentEncoderSG

variable {Ω H : Type*} [mΩ : MeasurableSpace Ω] [mH : MeasurableSpace H]

/-- The two adjacent-grid errors have this interval of width exactly Δ.
The probability assigned to the Boolean endpoint is handled by conditional
unbiasedness in `conditional_mgf`. -/
theorem bernoulli_error_mem_cell (Δ r : ℝ) (hΔ : 0 ≤ Δ) (b : Bool) :
    Δ * ((if b then (1 : ℝ) else 0) - r) ∈ Set.Icc (-Δ * r) (Δ * (1 - r)) := by
  cases b <;> simp only [Bool.false_eq_true, reduceIte] <;> constructor <;> nlinarith

theorem conditional_mgf
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → H) (e : Ω → ℝ)
    (r : H → ℝ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hg : Measurable g)
    (he : Measurable e) (hr : Measurable r) (hrange : ∀ v, r v ∈ Set.Icc 0 1)
    (hcell : ∀ ω, e ω ∈ Set.Icc (-Δ * r (g ω)) (Δ * (1 - r (g ω))))
    (hcenter : μ[e | mH.comap g] =ᵐ[μ] 0) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * e ω)) μ ∧
      μ[fun ω => Real.exp (t * e ω) | mH.comap g] ≤ᵐ[μ]
        fun _ => Real.exp (Δ ^ 2 * t ^ 2 / 8) := by
  have hb (ω : Ω) : e ω ∈ Set.Icc (-Δ) Δ := by
    have hh := hcell ω
    have hrw := hrange (g ω)
    constructor <;> nlinarith [hh.1, hh.2, hrw.1, hrw.2,
      mul_nonneg hΔ hrw.1, mul_nonneg hΔ (sub_nonneg.mpr hrw.2)]
  have hL1 : Integrable e μ := Integrable.of_mem_Icc (-Δ) Δ he.aemeasurable (ae_of_all _ hb)
  have hce := condExp_ae_eq_integral_condDistrib' hg hL1
  have hmean : ∀ᵐ v ∂μ.map g, ∫ y, y ∂condDistrib e g μ v = (0 : ℝ) := by
    apply (ae_map_iff hg.aemeasurable ?_).2
    · filter_upwards [hce, hcenter] with ω heq hz
      exact heq.symm.trans hz
    · exact measurableSet_eq_fun
        ((stronglyMeasurable_id.integral_kernel (κ := condDistrib e g μ)).measurable)
        measurable_const
  have hbound : ∀ᵐ v ∂μ.map g, ∀ᵐ y ∂condDistrib e g μ v,
      y ∈ Set.Icc (-Δ * r v) (Δ * (1 - r v)) := by
    apply Measure.ae_ae_of_ae_compProd
      (p := fun z : H × ℝ => z.2 ∈ Set.Icc (-Δ * r z.1) (Δ * (1 - r z.1)))
    rw [compProd_map_condDistrib he.aemeasurable]
    apply (ae_map_iff (hg.prodMk he).aemeasurable ?_).2 (ae_of_all _ hcell)
    exact (measurableSet_le (measurable_const.mul (hr.comp measurable_fst)) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_const.mul (measurable_const.sub (hr.comp measurable_fst))))
  have hExp : Integrable (fun ω => Real.exp (t * e ω)) μ :=
    integrable_exp_mul_of_mem_Icc he.aemeasurable (ae_of_all _ hb)
  refine ⟨hExp, ?_⟩
  have hmean' := ae_of_ae_map hg.aemeasurable hmean
  have hbound' := ae_of_ae_map hg.aemeasurable hbound
  have hceExp := condExp_ae_eq_integral_condDistrib hg he.aemeasurable
    (measurable_const.mul measurable_id).exp.stronglyMeasurable hExp
  filter_upwards [hmean', hbound', hceExp] with ω hm hbω heq
  have hSG := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    measurable_id.aemeasurable hbω hm
  have hw : Δ * (1 - r (g ω)) - -Δ * r (g ω) = Δ := by ring
  have hn : (((‖Δ‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2 = Δ ^ 2 * t ^ 2 / 8 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
      NNReal.coe_ofNat, abs_of_nonneg hΔ]
    ring
  simp only [id_eq] at heq
  rw [heq]
  have hs := hSG.mgf_le t
  rw [hw] at hs
  simpa only [mgf, hn] using hs

end Part2.AdjacentEncoderSG

namespace Part2.CNDHorizon
open CNDProcess

variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀} {θ : ι → ℝ}
  {R M D : ℝ} {T : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exactly the finite `SGLaws.encoder_conditional_mgf` obligation with
`σe = Δ / 2`. The full physical conditional mean is an explicit protocol
assumption; the weaker `afterAction` centering alone is insufficient. -/
theorem adjacent_encoder_conditional_mgf
    (h : SGInputs ℱ θ R M D T) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (r : ℕ → ι → Ω → ℝ)
    (hr : ∀ n<T, ∀ i, Measurable[h.afterNoiseAction n] (r n i))
    (hrange : ∀ n<T, ∀ i ω, r n i ω ∈ Set.Icc 0 1)
    (hcell : ∀ n<T, ∀ i ω,
      h.error n i ω ∈ Set.Icc (-Δ * r n i ω) (Δ * (1 - r n i ω)))
    (hcenter : ∀ n<T, ∀ i, μ[h.error n i | h.afterNoiseAction n] =ᵐ[μ] 0) :
    ∀ n<T, ∀ i t,
      μ[fun ω => Real.exp (t * h.error n i ω) | h.afterNoiseAction n] ≤ᵐ[μ]
        fun _ => Real.exp ((Δ / 2) ^ 2 * t ^ 2 / 2) := by
  intro n hn i t
  have hpre : h.pre n ≤ m₀ := (h.pre_le_next n hn).trans (ℱ.le _)
  have hA : Measurable (h.action n) := (h.action_measurable n hn).mono (ℱ.le _) le_rfl
  have hN : Measurable (h.noise n) := (h.noise_measurable n hn).mono (ℱ.le _) le_rfl
  have hS : Measurable (h.encodingSeed n) := (h.seed_measurable n hn).mono (ℱ.le _) le_rfl
  have hm : h.afterNoiseAction n ≤ m₀ :=
    sup_le (sup_le hpre hA.comap_le) hN.comap_le
  have he : Measurable (h.error n i) :=
    (h.error_encoded n hn i).mono (sup_le hpre (sup_le hN.comap_le hS.comap_le)) le_rfl
  have hg : @Measurable Ω Ω m₀ (h.afterNoiseAction n) id := hm
  have hc : μ[h.error n i | (h.afterNoiseAction n).comap id] =ᵐ[μ] 0 := by
    simpa only [MeasurableSpace.comap_id] using hcenter n hn i
  have hs := Part2.AdjacentEncoderSG.conditional_mgf
    (mH := h.afterNoiseAction n) μ id (h.error n i) (r n i) Δ hΔ hg he (hr n hn i)
    (hrange n hn i) (hcell n hn i) hc t
  have heq : Δ ^ 2 * t ^ 2 / 8 = (Δ / 2) ^ 2 * t ^ 2 / 2 := by ring
  simpa only [MeasurableSpace.comap_id, heq] using hs.2

/-- Supply the two encoder fields of finite `SGLaws` from the adjacent-grid
protocol. The action law and physical-noise laws remain separate inputs. -/
def laws_of_adjacent
    (o : DecisionMaps ι) (d : ExpertData ι E)
    (h : SGInputs ℱ θ R M D T) (σ Δ : ℝ) (hΔ : 0 ≤ Δ)
    (r : ℕ → ι → Ω → ℝ)
    (hr : ∀ n<T, ∀ i, Measurable[h.afterNoiseAction n] (r n i))
    (hrange : ∀ n<T, ∀ i ω, r n i ω ∈ Set.Icc 0 1)
    (hcell : ∀ n<T, ∀ i ω,
      h.error n i ω ∈ Set.Icc (-Δ * r n i ω) (Δ * (1 - r n i ω)))
    (hcenter : ∀ n<T, ∀ i, μ[h.error n i | h.afterNoiseAction n] =ᵐ[μ] 0)
    (hsample : ∀ n<T, ∀ i,
      μ[PairConfidence.actionIndicator (h.action n) i | h.encoded n] =ᵐ[μ] h.actualP o d n i)
    (hnoiseExp : ∀ n<T, ∀ i t, Integrable (fun ω => Real.exp (t * h.noise n ω i)) μ)
    (hnoiseMGF : ∀ n<T, ∀ i t,
      μ[fun ω => Real.exp (t * h.noise n ω i) | h.pre n] ≤ᵐ[μ]
        fun _ => Real.exp (σ ^ 2 * t ^ 2 / 2)) : SGLaws o d h μ σ (Δ / 2) where
  strong_categorical := hsample
  noise_exp_integrable := hnoiseExp
  noise_conditional_mgf := hnoiseMGF
  encoder_conditional_mgf := adjacent_encoder_conditional_mgf h Δ hΔ r hr hrange hcell hcenter
  encoder_centered n hn i := by
    have hpre : h.pre n ≤ m₀ := (h.pre_le_next n hn).trans (ℱ.le _)
    have hA : Measurable (h.action n) := (h.action_measurable n hn).mono (ℱ.le _) le_rfl
    have hN : Measurable (h.noise n) := (h.noise_measurable n hn).mono (ℱ.le _) le_rfl
    have hm : h.afterNoiseAction n ≤ m₀ :=
      sup_le (sup_le hpre hA.comap_le) hN.comap_le
    have ht := condExp_condExp_of_le (μ := μ) (f := h.error n i)
      (show h.afterAction n ≤ h.afterNoiseAction n from le_sup_left) hm
    exact ht.symm.trans ((condExp_congr_ae (hcenter n hn i)).trans (by
      simp only [condExp_zero]
      exact Filter.Eventually.of_forall fun _ => rfl))

end Part2.CNDHorizon
