import staging.cnd20261024.probability.SGRestrictedProcess

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SGRestricted
section Tail
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀} {X q : ℕ → Ω → ℝ} {a cap : ℝ}

/-- Original-space restricted Chernoff maximal theorem, including zero
variance, after the separately derived conditional direction MGF. -/
theorem maximal_of_conditional_mgf (ha : 0 ≤ a) (hcap : 0 < cap)
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hqm : ∀ n, StronglyMeasurable[ℱ n] (q n)) (hq0 : ∀ n ω, 0 ≤ q n ω)
    (hXi : ∀ n s, Integrable (fun ω => Real.exp (s * X n ω)) μ)
    (hmgf : ∀ t : ℝ, 0 ≤ t → t ≤ cap → ∀ n,
      μ[fun ω => Real.exp (t * X n ω) | ℱ n] ≤ᵐ[μ] fun ω => Real.exp (a * t ^ 2 * q n ω))
    (N : ℕ) {v L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ N,
      2 * Real.sqrt (a * v * L) + L / cap ≤ Bernstein.sumProcess X n ω ∧
      Bernstein.sumProcess q n ω ≤ v} ≤ Real.exp (-L) := by
  let t := L / (Real.sqrt (a * v * L) + L / cap)
  obtain ⟨ht, htcap, hopt⟩ := restricted_parameter ha hv hL hcap
  have hsm := supermartingale_of_conditional_mgf ha hXm hqm hq0 hXi (hmgf t ht htcap)
  let s := 2 * Real.sqrt (a * v * L) + L / cap
  have hville := Part2.CNDProbability.finite_ville_exp hsm
    (fun _ _ => Real.exp_nonneg _) process_zero N (t * s - a * t ^ 2 * v)
  have hsub : {ω | ∃ n ≤ N, s ≤ Bernstein.sumProcess X n ω ∧ Bernstein.sumProcess q n ω ≤ v} ⊆
      {ω | ∃ n ≤ N, Real.exp (t * s - a * t ^ 2 * v) ≤ process X q a t n ω} := by
    rintro ω ⟨n, hn, hs, hq⟩
    refine ⟨n, hn, Real.exp_le_exp.mpr ?_⟩
    have hx := mul_le_mul_of_nonneg_left hs ht
    have hv := mul_le_mul_of_nonneg_left hq (mul_nonneg ha (sq_nonneg t))
    change t * s - a * t ^ 2 * v ≤ t * Bernstein.sumProcess X n ω - a * t ^ 2 * Bernstein.sumProcess q n ω
    linarith
  exact (measureReal_mono hsub).trans (hville.trans (Real.exp_le_exp.mpr (by dsimp [s]; linarith [hopt])))

end Tail
end Part2.CNDProbability.SGRestricted
