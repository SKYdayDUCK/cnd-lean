import staging.cnd20261024.probability.SGRestrictedTail

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SGRestricted
section Uniform
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀} {X q : ℕ → Ω → ℝ} {a cap : ℝ}

theorem two_sided_of_conditional_mgf (ha : 0 ≤ a) (hcap : 0 < cap)
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hqm : ∀ n, StronglyMeasurable[ℱ n] (q n)) (hq0 : ∀ n ω, 0 ≤ q n ω)
    (hXi : ∀ n s, Integrable (fun ω => Real.exp (s * X n ω)) μ)
    (hmgf : ∀ t : ℝ, |t| ≤ cap → ∀ n,
      μ[fun ω => Real.exp (t * X n ω) | ℱ n] ≤ᵐ[μ] fun ω => Real.exp (a * t ^ 2 * q n ω))
    (N : ℕ) {v L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ N,
      2 * Real.sqrt (a * v * L) + L / cap ≤ |Bernstein.sumProcess X n ω| ∧
      Bernstein.sumProcess q n ω ≤ v} ≤ 2 * Real.exp (-L) := by
  let s := 2 * Real.sqrt (a * v * L) + L / cap
  let Epos := {ω | ∃ n ≤ N, s ≤ Bernstein.sumProcess X n ω ∧ Bernstein.sumProcess q n ω ≤ v}
  let Eneg := {ω | ∃ n ≤ N, s ≤ -Bernstein.sumProcess X n ω ∧ Bernstein.sumProcess q n ω ≤ v}
  have hpos : μ.real Epos ≤ Real.exp (-L) := maximal_of_conditional_mgf ha hcap hXm hqm hq0 hXi
    (fun t ht0 htcap n => hmgf t (by simpa only [abs_of_nonneg ht0] using htcap) n) N hv hL
  have hneg : μ.real Eneg ≤ Real.exp (-L) := by
    have hi : ∀ n t, Integrable (fun ω => Real.exp (t * (-X n ω))) μ := by
      intro n t
      simpa only [mul_neg, neg_mul] using hXi n (-t)
    have hm : ∀ t : ℝ, 0 ≤ t → t ≤ cap → ∀ n,
        μ[fun ω => Real.exp (t * (-X n ω)) | ℱ n] ≤ᵐ[μ] fun ω => Real.exp (a * t ^ 2 * q n ω) := by
      intro t ht0 htcap n
      simpa only [mul_neg, neg_mul, neg_sq] using hmgf (-t) (by simpa only [abs_neg, abs_of_nonneg ht0] using htcap) n
    simpa only [Eneg, s, Bernstein.sumProcess_neg] using
      maximal_of_conditional_mgf (X := fun n ω => -X n ω) ha hcap
        (fun n => (hXm n).neg) hqm hq0 hi hm N hv hL
  have hsub : {ω | ∃ n ≤ N, s ≤ |Bernstein.sumProcess X n ω| ∧ Bernstein.sumProcess q n ω ≤ v} ⊆ Epos ∪ Eneg := by
    rintro ω ⟨n, hn, hs, hv⟩
    by_cases hz : 0 ≤ Bernstein.sumProcess X n ω
    · exact Or.inl ⟨n, hn, by simpa only [abs_of_nonneg hz] using hs, hv⟩
    · exact Or.inr ⟨n, hn, by simpa only [abs_of_neg (lt_of_not_ge hz)] using hs, hv⟩
  exact (measureReal_mono hsub).trans ((measureReal_union_le Epos Eneg).trans (by linarith))

theorem uniform_of_conditional_mgf (ha : 0 ≤ a) (hcap : 0 < cap)
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hqm : ∀ n, StronglyMeasurable[ℱ n] (q n))
    (hq : ∀ n ω, 0 ≤ q n ω ∧ q n ω ≤ 1)
    (hXi : ∀ n s, Integrable (fun ω => Real.exp (s * X n ω)) μ)
    (hmgf : ∀ t : ℝ, |t| ≤ cap → ∀ n,
      μ[fun ω => Real.exp (t * X n ω) | ℱ n] ≤ᵐ[μ] fun ω => Real.exp (a * t ^ 2 * q n ω))
    (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ T,
      2 * Real.sqrt (a * (1 + Bernstein.sumProcess q n ω) * L) + L / cap ≤ |Bernstein.sumProcess X n ω|} ≤
      2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-L) := by
  let E : ℕ → Set Ω := fun j => {ω | ∃ n ≤ T,
    2 * Real.sqrt (a * ((j : ℝ) + 1) * L) + L / cap ≤ |Bernstein.sumProcess X n ω| ∧ Bernstein.sumProcess q n ω ≤ (j : ℝ) + 1}
  have hsub : {ω | ∃ n ≤ T,
      2 * Real.sqrt (a * (1 + Bernstein.sumProcess q n ω) * L) + L / cap ≤ |Bernstein.sumProcess X n ω|} ⊆
      ⋃ j ∈ Finset.range (T + 1), E j := by
    rintro ω ⟨n, hn, hs⟩
    have hq0 : 0 ≤ Bernstein.sumProcess q n ω := Finset.sum_nonneg fun i _ => (hq i ω).1
    have hqT : Bernstein.sumProcess q n ω ≤ (T : ℝ) := by
      calc
        _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hq i ω).2
        _ = (n : ℝ) := by simp
        _ ≤ _ := by exact_mod_cast hn
    let j := ⌊Bernstein.sumProcess q n ω⌋₊
    have hjT : j ≤ T := Nat.floor_le_of_le hqT
    have hjlo : (j : ℝ) ≤ Bernstein.sumProcess q n ω := Nat.floor_le hq0
    have hjhi : Bernstein.sumProcess q n ω ≤ (j : ℝ) + 1 := (Nat.lt_floor_add_one _).le
    simp only [Set.mem_iUnion, E, Set.mem_setOf_eq]
    refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjT), n, hn, ?_, hjhi⟩
    have hsqrt : Real.sqrt (a * ((j : ℝ) + 1) * L) ≤ Real.sqrt (a * (1 + Bernstein.sumProcess q n ω) * L) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha) hL.le)
    linarith
  calc
    _ ≤ μ.real (⋃ j ∈ Finset.range (T + 1), E j) := measureReal_mono hsub
    _ ≤ ∑ j ∈ Finset.range (T + 1), μ.real (E j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (T + 1), (2 * Real.exp (-L)) := by
      apply Finset.sum_le_sum
      intro j _
      exact two_sided_of_conditional_mgf ha hcap hXm hqm (fun n ω => (hq n ω).1) hXi hmgf T (by positivity) hL
    _ = _ := by simp; ring

end Uniform
end Part2.CNDProbability.SGRestricted
