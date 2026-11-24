import CNDMinimumNormMeasurable

/-! Concrete Borel interface for the canonical CND matrix proximal choice. -/

noncomputable section

namespace Part2.CNDCausalChoice

open Set Filter Topology
open CNDMatrixProx CNDMinimumNormMeasurable

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev RawProxData := ((ι → ℝ) × (ι → ι → ℝ)) × ((ι → ℝ) × ℝ)

def ValidProxData (d : RawProxData ι) : Prop :=
  CND.IsCND d.1.2 ∧ 0 ≤ d.2.2

abbrev ProxData := {d : RawProxData ι // ValidProxData ι d}

def proxObjective (z : ProxData ι × (ι → ℝ)) : ℝ :=
  objective z.1.val.1.1 z.1.val.1.2 z.1.val.2.1 z.1.val.2.2 z.2

theorem continuous_proxObjective : Continuous (proxObjective ι) := by
  unfold proxObjective objective CND.potential CND.quadratic TVProx.l1
  fun_prop

theorem convex_proxObjective (d : ProxData ι) :
    ConvexOn ℝ (stdSimplex ℝ ι) (fun p => proxObjective ι (d, p)) :=
  convex_objective d.val.1.1 d.val.1.2 d.val.2.1 d.val.2.2 d.property.1 d.property.2

theorem simplex_nonempty : (stdSimplex ℝ ι).Nonempty :=
  ⟨Pi.single (Classical.choice (inferInstance : Nonempty ι)) 1, single_mem_stdSimplex ℝ _⟩

def canonicalProx (d : ProxData ι) : ι → ℝ :=
  minimumNorm (stdSimplex ℝ ι) (isCompact_stdSimplex ι) (simplex_nonempty ι)
      (fun p => proxObjective ι (d, p))
      ((continuous_proxObjective ι).comp₂ continuous_const continuous_id) (convex_proxObjective ι d)

set_option maxHeartbeats 1000000 in
theorem canonicalProx_eq_frozen (d : ProxData ι) (hq : d.val.2.1 ∈ stdSimplex ℝ ι) :
    canonicalProx ι d = minimumNormProx d.val.1.1 d.val.1.2 d.val.2.1 d.val.2.2
      d.property.1 d.property.2 hq := by
  have hs := minimumNorm_spec (stdSimplex ℝ ι) (isCompact_stdSimplex ι) (simplex_nonempty ι)
    (fun p => proxObjective ι (d, p))
    ((continuous_proxObjective ι).comp₂ continuous_const continuous_id) (convex_proxObjective ι d)
  apply (Classical.choose_spec (exists_unique_minimumNorm_minimizer
    d.val.1.1 d.val.1.2 d.val.2.1 d.val.2.2 d.property.1 d.property.2 hq)).2
  exact hs

/-- The actual frozen canonical proximal map, including degenerate primary
minima and W=0, is Borel on its finite coefficient domain. -/
theorem measurable_canonicalProx : Measurable (canonicalProx ι) := by
  exact measurable_minimumNorm (stdSimplex ℝ ι) (isCompact_stdSimplex ι) (simplex_nonempty ι)
    (proxObjective ι) (continuous_proxObjective ι) (convex_proxObjective ι)

/-- A measurable coefficient record from the past gives a measurable decision. -/
theorem measurable_canonicalProx_history {Ω : Type*} [MeasurableSpace Ω]
    (d : Ω → ProxData ι) (hd : Measurable d) :
    Measurable (fun ω => canonicalProx ι (d ω)) :=
  (measurable_canonicalProx ι).comp hd

end Part2.CNDCausalChoice
