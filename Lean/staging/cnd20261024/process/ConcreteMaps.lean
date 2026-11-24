import staging.cnd20261024.process.InformationBridge
import CNDCausalChoice
import ExactGreedyMeasurable
import OriginalRadiusBridge

/-! Total Borel extension of the actual canonical decisions. The extension
outside CND coefficients is used only to define the recursive map; the
actual trajectory is subsequently proved to stay in the original domain. -/
noncomputable section
open Set MeasureTheory Finset
open scoped BigOperators
namespace Part2.CNDProcess

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem isClosed_isCND : IsClosed {r : Mat ι | CND.IsCND r} := by
  unfold CND.IsCND CND.ConditionallyNegative
  simp only [setOf_and, setOf_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_eq (by fun_prop) (by fun_prop)
  · apply IsClosed.inter
    · apply isClosed_iInter
      intro i
      exact isClosed_eq (by fun_prop) continuous_const
    · apply isClosed_iInter
      intro x
      apply isClosed_iInter
      intro _
      exact isClosed_le (by unfold CND.quadratic; fun_prop) continuous_const

def extendedProx (W : ℝ) (hW : 0 ≤ W) (x : ProxInput ι) : Vec ι := by
  classical
  exact if hr : CND.IsCND x.2.1 then
    CNDCausalChoice.canonicalProx ι ⟨((x.1, x.2.1), (x.2.2, W)), hr, hW⟩
  else fun _ ↦ (Fintype.card ι : ℝ)⁻¹

theorem measurable_extendedProx (W : ℝ) (hW : 0 ≤ W) :
    Measurable (extendedProx (ι := ι) W hW) := by
  classical
  have hs : MeasurableSet {x : ProxInput ι | CND.IsCND x.2.1} :=
    isClosed_isCND.measurableSet.preimage (measurable_fst.comp measurable_snd)
  have hm : Measurable (fun x : {x : ProxInput ι | CND.IsCND x.2.1} ↦
      (⟨((x.val.1, x.val.2.1), (x.val.2.2, W)), x.property, hW⟩ : CNDCausalChoice.ProxData ι)) :=
    (show Measurable (fun x : {x : ProxInput ι | CND.IsCND x.2.1} ↦
      ((x.val.1, x.val.2.1), (x.val.2.2, W))) by fun_prop).subtype_mk
  exact Measurable.dite
    ((CNDCausalChoice.measurable_canonicalProx ι).comp hm) measurable_const hs

theorem extendedProx_simplex (W : ℝ) (hW : 0 ≤ W) (x : ProxInput ι) :
    extendedProx W hW x ∈ CND.simplex := by
  classical
  unfold extendedProx
  split_ifs with hr
  · have hm := (CNDMinimumNormMeasurable.minimumNorm_spec
      (stdSimplex ℝ ι) (isCompact_stdSimplex ι) (CNDCausalChoice.simplex_nonempty ι)
      _ ((CNDCausalChoice.continuous_proxObjective ι).comp₂ continuous_const continuous_id)
      (CNDCausalChoice.convex_proxObjective ι
        ⟨((x.1, x.2.1), (x.2.2, W)), hr, hW⟩)).1.1
    exact hm
  · constructor
    · intro i; positivity
    · simp [Fintype.card_ne_zero]

theorem extendedProx_eq_canonical (W : ℝ) (hW : 0 ≤ W) (x : ProxInput ι)
    (hr : CND.IsCND x.2.1) :
    extendedProx W hW x =
      CNDCausalChoice.canonicalProx ι ⟨((x.1, x.2.1), (x.2.2, W)), hr, hW⟩ := by
  classical
  simp [extendedProx, hr]

theorem extendedProx_minimizes (W : ℝ) (hW : 0 ≤ W) (x : ProxInput ι)
    (hr : CND.IsCND x.2.1) :
    IsMinOn (CNDMatrixProx.objective x.1 x.2.1 x.2.2 W) (stdSimplex ℝ ι)
      (extendedProx W hW x) := by
  rw [extendedProx_eq_canonical W hW x hr]
  exact (CNDMinimumNormMeasurable.minimumNorm_spec
    (stdSimplex ℝ ι) (isCompact_stdSimplex ι) (CNDCausalChoice.simplex_nonempty ι)
    _ ((CNDCausalChoice.continuous_proxObjective ι).comp₂ continuous_const continuous_id)
    (CNDCausalChoice.convex_proxObjective ι
      ⟨((x.1, x.2.1), (x.2.2, W)), hr, hW⟩)).1.2

def concreteMaps {K : ℕ} [Nonempty (Fin K)] (H L R W : ℝ)
    (hR : 0 ≤ R) (hW : 0 ≤ W) : DecisionMaps (Fin K) where
  confidence := StatisticalMaps.actualConfidence H L R hR
  radius := StatisticalMaps.rawRadius H L R
  prox := extendedProx W hW
  transport := ExactGreedyMeasurable.actualTransport W univ_nonempty
  confidence_measurable := StatisticalMaps.measurable_actualConfidence H L R hR
  radius_measurable := StatisticalMaps.measurable_rawRadius H L R
  prox_measurable := measurable_extendedProx W hW
  transport_measurable := ExactGreedyMeasurable.measurable_actualTransport W univ_nonempty
  prox_simplex := extendedProx_simplex W hW

variable {K : ℕ} [Nonempty (Fin K)] {E Ω : Type*} [Fintype E] [DecidableEq E]
  [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}

theorem concrete_radius_isCND (H L R W : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hR : 0 ≤ R) (hW : 0 ≤ W) (d : ExpertData (Fin K) E) (hd : d.R = R)
    (f : Feedback (ι := Fin K) ℱ) (n : ℕ) (ω : Ω) :
    CND.IsCND (radius (concreteMaps H L R W hR hW) d
      (run (concreteMaps H L R W hR hW) d f n ω)) := by
  by_cases hz : d.R = 0
  · simp [radius, hz, CND.IsCND, CND.ConditionallyNegative, CND.quadratic]
  · rw [radius, if_neg hz]
    change CND.IsCND (StatisticalMaps.rawRadius H L R _)
    rw [computed_radius_eq_actual _ _ _ hz]
    exact CNDSaturation.actualSaturatedRadius_isCND _
      (fun t ↦ runProbability_simplex _ d f t ω) n H L R hH hL hR

theorem concrete_probability_eq_canonical (H L R W : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hR : 0 ≤ R) (hW : 0 ≤ W) (d : ExpertData (Fin K) E) (hd : d.R = R)
    (f : Feedback (ι := Fin K) ℱ) (n : ℕ) (ω : Ω) :
    let o := concreteMaps (K := K) H L R W hR hW
    let s := run o d f n ω
    (fun i ↦ runProbability o d f n i ω) =
      CNDCausalChoice.canonicalProx (Fin K)
        ⟨((confidence o d s, radius o d s), (suggestion d n s, W)),
          concrete_radius_isCND H L R W hH hL hR hW d hd f n ω, hW⟩ := by
  dsimp only
  exact extendedProx_eq_canonical W hW _
    (concrete_radius_isCND H L R W hH hL hR hW d hd f n ω)

end Part2.CNDProcess
end
