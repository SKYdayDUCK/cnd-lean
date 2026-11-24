import staging.cnd20261024.probability.PinnedOptionalStopping
import Part2.Bernstein

/-! Finite-horizon Ville inequality on the original measure.
The upstream optional-stopping file is byte-identical to the locked mathlib source.
No tail probability or supermartingale property is a field of a new model. -/

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators

namespace Part2.CNDProbability

section Ville
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀} {Z : ℕ → Ω → ℝ}

/-- Ville's inequality for an arbitrary nonnegative supermartingale, including
time zero, with no union over the horizon. -/
theorem finite_ville (hZ : Supermartingale Z ℱ μ)
    (hZ0 : ∀ n ω, 0 ≤ Z n ω) (hinit : Z 0 = fun _ => 1)
    (N : ℕ) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | ∃ n ≤ N, a ≤ Z n ω} ≤ 1 / a := by
  let τ : Ω → ℕ := hitting Z (Set.Ici a) 0 N
  have hτ : IsStoppingTime ℱ τ := hitting_isStoppingTime hZ.adapted measurableSet_Ici
  have hτN : ∀ ω, τ ω ≤ N := hitting_le
  have hint : Integrable (stoppedValue Z τ) μ := integrable_stoppedValue ℕ hτ hZ.integrable hτN
  have hexp := hZ.neg.expected_stoppedValue_mono
    (isStoppingTime_const ℱ 0) hτ (fun ω => Nat.zero_le (τ ω)) hτN
  have hmean : (∫ ω, stoppedValue Z τ ω ∂μ) ≤ 1 := by
    change (∫ ω, -Z 0 ω ∂μ) ≤ ∫ ω, -(stoppedValue Z τ ω) ∂μ at hexp
    rw [hinit] at hexp
    simp only [integral_neg, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hexp
    linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => hZ0 (τ ω) ω) hint a
  have hsub : {ω | ∃ n ≤ N, a ≤ Z n ω} ⊆ {ω | a ≤ stoppedValue Z τ ω} := by
    rintro ω ⟨n, hn, hz⟩
    exact stoppedValue_hitting_mem ⟨n, ⟨Nat.zero_le n, hn⟩, hz⟩
  have htail : μ.real {ω | a ≤ stoppedValue Z τ ω} ≤ 1 / a := by
    apply (le_div_iff₀ ha).2
    simpa only [mul_comm] using hmarkov.trans hmean
  exact (measureReal_mono hsub).trans htail

/-- Exponential form of the same maximal inequality. -/
theorem finite_ville_exp (hZ : Supermartingale Z ℱ μ)
    (hZ0 : ∀ n ω, 0 ≤ Z n ω) (hinit : Z 0 = fun _ => 1) (N : ℕ) (L : ℝ) :
    μ.real {ω | ∃ n ≤ N, Real.exp L ≤ Z n ω} ≤ Real.exp (-L) := by
  simpa only [Real.exp_neg, one_div] using
    finite_ville hZ hZ0 hinit N (Real.exp_pos L)

/-- A maximal Bernstein boundary on the original space. Its raw hypotheses
are centering, amplitude, and predictable conditional second moments. -/
theorem exponential_maximal
    {X V : ℕ → Ω → ℝ} {c t : ℝ}
    (h : Bernstein.BoundedIncrements ℱ μ X V c)
    (ht : 0 ≤ t) (hsmall : t * c ≤ 3 / 2) (N : ℕ) (s v : ℝ) :
    μ.real {ω | ∃ n ≤ N, s ≤ Bernstein.sumProcess X n ω ∧
      Bernstein.sumProcess V n ω ≤ v} ≤ Real.exp (t ^ 2 * v - t * s) := by
  have hbound := finite_ville_exp (Bernstein.exponential_supermartingale h ht hsmall)
    (fun n ω => (Bernstein.exponentialProcess_pos t n ω).le)
    (Bernstein.exponentialProcess_zero t) N (t * s - t ^ 2 * v)
  have hsub : {ω | ∃ n ≤ N, s ≤ Bernstein.sumProcess X n ω ∧
      Bernstein.sumProcess V n ω ≤ v} ⊆
      {ω | ∃ n ≤ N, Real.exp (t * s - t ^ 2 * v) ≤
        Bernstein.exponentialProcess X V t n ω} := by
    rintro ω ⟨n, hn, hs, hv⟩
    refine ⟨n, hn, Real.exp_le_exp.mpr ?_⟩
    have hx := mul_le_mul_of_nonneg_left hs ht
    have hy := mul_le_mul_of_nonneg_left hv (sq_nonneg t)
    change t * s - t ^ 2 * v ≤ t * Bernstein.sumProcess X n ω - t ^ 2 * Bernstein.sumProcess V n ω
    linarith
  exact (measureReal_mono hsub).trans (by convert hbound using 1 <;> congr 1 <;> ring)

theorem bernstein_maximal
    {X V : ℕ → Ω → ℝ} {c : ℝ}
    (h : Bernstein.BoundedIncrements ℱ μ X V c) (hc : 0 < c)
    (N : ℕ) {v L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ N,
      2 * Real.sqrt (v * L) + (2 * c / 3) * L ≤ Bernstein.sumProcess X n ω ∧
      Bernstein.sumProcess V n ω ≤ v} ≤ Real.exp (-L) := by
  obtain ⟨ht, hsmall, hopt⟩ := Bernstein.bernstein_parameter hc hv hL
  exact (exponential_maximal h ht hsmall N
    (2 * Real.sqrt (v * L) + (2 * c / 3) * L) v).trans (Real.exp_le_exp.mpr hopt)

end Ville
end Part2.CNDProbability
