import staging.cnd20261024.net.UniformDirections

noncomputable section
set_option maxHeartbeats 1200000
open Finset
namespace Part2.CNDNet
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- SG14's deterministic all-direction extension with its original 4/16 constants.
The net exists here; no covering assumption or bounded-observation hypothesis is an input.
The finite-direction statistical inequality remains the interface to the SG probability module. -/
theorem exists_SG_paper_net_extension (T : ℕ) (hT : 1 ≤ T) (hK : 2 ≤ Fintype.card ι) :
    ∃ s : Finset (ZeroSum ι), (∀ b ∈ s, oscillation b.val = 1) ∧
      (s.card : ℝ) ≤ paperNetCard ι T ∧
      ∀ (p : ℕ → ι → ℝ), (∀ t, p t ∈ CND.simplex) →
      ∀ n ≤ T, ∀ H L : ℝ, 0 ≤ H → 1 ≤ L → ∀ Z : ι → ℝ,
      (∀ b ∈ s, |∑ i, b.val i * Z i| ≤
        4 * H * Real.sqrt L * informationEnergy p n b.val + 8 * H * L) →
      ∀ u : ι → ℝ, (∑ i, u i) = 0 →
        |∑ i, u i * Z i| ≤
          4 * H * Real.sqrt (L * CND.quadratic (CNDPhysical.information p n) u) +
            16 * H * L * oscillation u := by
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
  have hf : ∀ b ∈ s, ‖F b‖ ≤ (4 * H * Real.sqrt L) * e b + 8 * H * L := hfinite
  have hL0 : 0 ≤ L := by linarith
  have hA0 : 0 ≤ 4 * H * Real.sqrt L := by positivity
  have hB0 : 0 ≤ 8 * H * L := by positivity
  have hh := extend_all s hε.le (by linarith) hA0 hB0
    (Real.sqrt_nonneg _) hs' hnet' e he F hf (⟨u, hu⟩ : ZeroSum ι)
  have herr := extension_error_bound hε.le hε16 hA0 hB0 (Real.sqrt_nonneg _) hεC
  have hsqrtL : Real.sqrt L ≤ L := by
    nlinarith [Real.sq_sqrt hL0, Real.sqrt_nonneg L]
  have herr' : 4 * H * Real.sqrt L * C * paperEpsilon ι T +
      paperEpsilon ι T * ((4 * H * Real.sqrt L * C + 8 * H * L) /
        (1 - paperEpsilon ι T)) ≤ 8 * H * L := by
    dsimp [C] at *
    nlinarith
  have henergyroot : Real.sqrt (L * CND.quadratic (CNDPhysical.information p n) u) =
      Real.sqrt L * informationEnergy p n u := by
    rw [← energy_actual_information p hp n u, Real.sqrt_mul hL0,
      Real.sqrt_sq (apply_nonneg _ _)]
  rw [henergyroot]
  change |∑ i, u i * Z i| ≤ _ at hh
  change _ ≤ 4 * H * Real.sqrt L * informationEnergy p n u +
    (8 * H * L + 4 * H * Real.sqrt L * C * paperEpsilon ι T +
      paperEpsilon ι T * ((4 * H * Real.sqrt L * C + 8 * H * L) /
      (1 - paperEpsilon ι T))) * oscillation u at hh
  nlinarith [mul_nonneg (sub_nonneg.mpr herr') (oscillation_nonneg u)]

end Part2.CNDNet
