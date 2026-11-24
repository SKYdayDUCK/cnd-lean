import staging.cnd20261024.probability.SharpBernstein

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SharpBernstein

lemma bernstein_parameter {c v L : ℝ} (hc : 0 < c) (hv : 0 ≤ v) (hL : 0 < L) :
    let t := L / (Real.sqrt (v * L / 2) + (2 * c / 3) * L)
    0 ≤ t ∧ t * c < 3 ∧
      coefficient c t * v - t * (Real.sqrt (2 * v * L) + (2 * c / 3) * L) ≤ -L := by
  let a := Real.sqrt (v * L / 2)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = v * L / 2 := Real.sq_sqrt (by positivity)
  have hd : 0 < a + (2 * c / 3) * L := by positivity
  let t := L / (a + (2 * c / 3) * L)
  change 0 ≤ t ∧ t * c < 3 ∧
    coefficient c t * v - t * (Real.sqrt (2 * v * L) + (2 * c / 3) * L) ≤ -L
  have ht : 0 ≤ t := div_nonneg hL.le hd.le
  have hprod : t * (a + (2 * c / 3) * L) = L := div_mul_cancel₀ L hd.ne'
  have hsmall : t * c ≤ 3 / 2 := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hcoefden : 0 < 2 * (1 - t * c / 3) := by linarith
  have hta : 0 ≤ t * a := mul_nonneg ht ha
  have hstep : t * a ≤ L * (1 - t * c / 3) := by nlinarith [mul_nonneg ht hc.le]
  have hsq : (t * a) ^ 2 ≤ (t * a) * (L * (1 - t * c / 3)) :=
    by simpa only [pow_two] using mul_le_mul_of_nonneg_left hstep hta
  have hid : (t * a) ^ 2 = (t ^ 2 * v) * L / 2 := by rw [mul_pow, ha2]; ring
  have hvar : coefficient c t * v ≤ t * a := by
    rw [coefficient, div_mul_eq_mul_div]
    apply (div_le_iff₀ hcoefden).2
    nlinarith [hsq, hid]
  have hsqrt : Real.sqrt (2 * v * L) = 2 * a := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    nlinarith [ha2]
  refine ⟨ht, by linarith, ?_⟩
  rw [hsqrt]
  nlinarith [hprod]

section Probability
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {X V : ℕ → Ω → ℝ} {c : ℝ}

/-- Maximal exponential inequality with Bernstein's sharp quadratic
coefficient. No conditioning on the variance event is performed. -/
theorem exponential_maximal (h : Bernstein.BoundedIncrements ℱ μ X V c)
    {t : ℝ} (ht : 0 ≤ t) (hsmall : t * c < 3) (N : ℕ) (s v : ℝ) :
    μ.real {ω | ∃ n ≤ N, s ≤ Bernstein.sumProcess X n ω ∧
      Bernstein.sumProcess V n ω ≤ v} ≤ Real.exp (coefficient c t * v - t * s) := by
  have hbound := Part2.CNDProbability.finite_ville_exp (exponential_supermartingale h ht hsmall)
    (fun n ω => (exponentialProcess_pos t n ω).le)
    (exponentialProcess_zero t) N (t * s - coefficient c t * v)
  have hsub : {ω | ∃ n ≤ N, s ≤ Bernstein.sumProcess X n ω ∧
      Bernstein.sumProcess V n ω ≤ v} ⊆
      {ω | ∃ n ≤ N, Real.exp (t * s - coefficient c t * v) ≤ exponentialProcess X V c t n ω} := by
    rintro ω ⟨n, hn, hs, hv⟩
    refine ⟨n, hn, Real.exp_le_exp.mpr ?_⟩
    have hx := mul_le_mul_of_nonneg_left hs ht
    have hy := mul_le_mul_of_nonneg_left hv (coefficient_nonneg hsmall)
    change t * s - coefficient c t * v ≤ t * Bernstein.sumProcess X n ω - coefficient c t * Bernstein.sumProcess V n ω
    linarith
  exact (measureReal_mono hsub).trans (by convert hbound using 1 <;> congr 1 <;> ring)

/-- The exact sqrt(2vL)+2cL/3 threshold used in CND-MAIN §5, including v=0. -/
theorem bernstein_maximal (h : Bernstein.BoundedIncrements ℱ μ X V c) (hc : 0 < c)
    (N : ℕ) {v L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ N,
      Real.sqrt (2 * v * L) + (2 * c / 3) * L ≤ Bernstein.sumProcess X n ω ∧
      Bernstein.sumProcess V n ω ≤ v} ≤ Real.exp (-L) := by
  obtain ⟨ht, hsmall, hopt⟩ := bernstein_parameter hc hv hL
  exact (exponential_maximal h ht hsmall N
    (Real.sqrt (2 * v * L) + (2 * c / 3) * L) v).trans (Real.exp_le_exp.mpr hopt)

theorem bernstein_two_sided (h : Bernstein.BoundedIncrements ℱ μ X V c) (hc : 0 < c)
    (N : ℕ) {v L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ N,
      Real.sqrt (2 * v * L) + (2 * c / 3) * L ≤ |Bernstein.sumProcess X n ω| ∧
      Bernstein.sumProcess V n ω ≤ v} ≤ 2 * Real.exp (-L) := by
  let s := Real.sqrt (2 * v * L) + (2 * c / 3) * L
  let Epos := {ω | ∃ n ≤ N, s ≤ Bernstein.sumProcess X n ω ∧ Bernstein.sumProcess V n ω ≤ v}
  let Eneg := {ω | ∃ n ≤ N, s ≤ -Bernstein.sumProcess X n ω ∧ Bernstein.sumProcess V n ω ≤ v}
  have hpos : μ.real Epos ≤ Real.exp (-L) := bernstein_maximal h hc N hv hL
  have hneg : μ.real Eneg ≤ Real.exp (-L) := by
    simpa only [Eneg, Bernstein.sumProcess_neg] using bernstein_maximal h.neg hc N hv hL
  have hsub : {ω | ∃ n ≤ N, s ≤ |Bernstein.sumProcess X n ω| ∧ Bernstein.sumProcess V n ω ≤ v} ⊆ Epos ∪ Eneg := by
    rintro ω ⟨n, hn, hs, hv⟩
    by_cases hz : 0 ≤ Bernstein.sumProcess X n ω
    · exact Or.inl ⟨n, hn, by simpa only [abs_of_nonneg hz] using hs, hv⟩
    · exact Or.inr ⟨n, hn, by simpa only [abs_of_neg (lt_of_not_ge hz)] using hs, hv⟩
  exact (measureReal_mono hsub).trans ((measureReal_union_le Epos Eneg).trans (by linarith))

end Probability
end Part2.CNDProbability.SharpBernstein
