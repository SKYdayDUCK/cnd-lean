import staging.cnd20261024.probability.SharpTail
import staging.cnd20261024.probability.ModelBridge

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SharpBernstein
section Uniform
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {X V : ℕ → Ω → ℝ} {c : ℝ}

/-- Integer variance peeling after the maximal inequality. Unlike a fixed-time
union, this pays one factor T+1, and still covers every n≤T. -/
theorem bernstein_uniform (h : Bernstein.BoundedIncrements ℱ μ X V c) (hc : 0 < c)
    (hV1 : ∀ i ω, V i ω ≤ 1) (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ T,
      Real.sqrt (2 * (1 + Bernstein.sumProcess V n ω) * L) + (2 * c / 3) * L ≤
        |Bernstein.sumProcess X n ω|} ≤ 2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-L) := by
  let E : ℕ → Set Ω := fun j => {ω | ∃ n ≤ T,
    Real.sqrt (2 * ((j : ℝ) + 1) * L) + (2 * c / 3) * L ≤ |Bernstein.sumProcess X n ω| ∧
      Bernstein.sumProcess V n ω ≤ (j : ℝ) + 1}
  have hsub : {ω | ∃ n ≤ T,
      Real.sqrt (2 * (1 + Bernstein.sumProcess V n ω) * L) + (2 * c / 3) * L ≤
        |Bernstein.sumProcess X n ω|} ⊆ ⋃ j ∈ Finset.range (T + 1), E j := by
    rintro ω ⟨n, hn, htail⟩
    have hV0 : 0 ≤ Bernstein.sumProcess V n ω := Finset.sum_nonneg fun i _ => h.variance_nonneg i ω
    have hVT : Bernstein.sumProcess V n ω ≤ (T : ℝ) := by
      calc
        _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hV1 i ω
        _ = (n : ℝ) := by simp
        _ ≤ _ := by exact_mod_cast hn
    let j := ⌊Bernstein.sumProcess V n ω⌋₊
    have hjT : j ≤ T := Nat.floor_le_of_le hVT
    have hjlo : (j : ℝ) ≤ Bernstein.sumProcess V n ω := Nat.floor_le hV0
    have hjhi : Bernstein.sumProcess V n ω ≤ (j : ℝ) + 1 := (Nat.lt_floor_add_one _).le
    simp only [Set.mem_iUnion, E, Set.mem_setOf_eq]
    refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjT), n, hn, ?_, hjhi⟩
    have hsqrt : Real.sqrt (2 * ((j : ℝ) + 1) * L) ≤ Real.sqrt (2 * (1 + Bernstein.sumProcess V n ω) * L) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (by linarith) hL.le)
    linarith
  calc
    _ ≤ μ.real (⋃ j ∈ Finset.range (T + 1), E j) := measureReal_mono hsub
    _ ≤ ∑ j ∈ Finset.range (T + 1), μ.real (E j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (T + 1), (2 * Real.exp (-L)) :=
      Finset.sum_le_sum fun j _ => bernstein_two_sided h hc T (by positivity) hL
    _ = _ := by simp; ring

theorem paper_uniform {H : ℝ} (hH : 0 < H) {q : ℕ → Ω → ℝ}
    (h : Bernstein.BoundedIncrements ℱ μ X (fun i ω => H ^ 2 * q i ω) (2 * H))
    (hq : ∀ i ω, q i ω ≤ 1) (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ n ≤ T,
      H * Real.sqrt (2 * (1 + Bernstein.sumProcess q n ω) * L) + (4 / 3) * H * L ≤
        |Bernstein.sumProcess X n ω|} ≤ 2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-L) := by
  have hnorm := h.const_mul (a := H⁻¹) (inv_nonneg.mpr hH.le)
  have hc : H⁻¹ * (2 * H) = 2 := by field_simp
  have hv : (fun i ω => (H⁻¹) ^ 2 * (H ^ 2 * q i ω)) = q := by funext i ω; field_simp
  rw [hc, hv] at hnorm
  have hU := bernstein_uniform hnorm (by norm_num : (0 : ℝ) < 2) hq T hL
  have hsub : {ω | ∃ n ≤ T,
      H * Real.sqrt (2 * (1 + Bernstein.sumProcess q n ω) * L) + (4 / 3) * H * L ≤ |Bernstein.sumProcess X n ω|} ⊆
      {ω | ∃ n ≤ T,
        Real.sqrt (2 * (1 + Bernstein.sumProcess q n ω) * L) + (2 * (2 : ℝ) / 3) * L ≤
          |Bernstein.sumProcess (fun i ω => H⁻¹ * X i ω) n ω|} := by
    rintro ω ⟨n, hn, hr⟩
    refine ⟨n, hn, ?_⟩
    rw [Bernstein.sumProcess_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hH)]
    have hscaled := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hH.le)
    have heq : H⁻¹ * (H * Real.sqrt (2 * (1 + Bernstein.sumProcess q n ω) * L) + (4 / 3) * H * L) =
        Real.sqrt (2 * (1 + Bernstein.sumProcess q n ω) * L) + (2 * (2 : ℝ) / 3) * L := by field_simp; ring
    rwa [heq] at hscaled
  exact (measureReal_mono hsub).trans hU

end Uniform
end Part2.CNDProbability.SharpBernstein

namespace Part2.CNDProbability.M1Model
section Family
variable {Ω ι α : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype α]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}

/-- Simultaneously all times and any finite direction family. Applied to an
osc-unit epsilon-net, this is CND's statistical event before deterministic
net extension. The directions are deterministic; they can be dependent as
processes because the same original action is used for all of them. -/
theorem finite_direction_family (h : M1Model ℱ μ θ R M D) (b : α → ι → ℝ)
    (hb : ∀ a i j, |b a i - b a j| ≤ 1) (hH : 0 < R + M + D)
    (T : ℕ) {L : ℝ} (hL : 0 < L) :
    μ.real {ω | ∃ a, ∃ n ≤ T,
      (R + M + D) * Real.sqrt (2 * (1 + Bernstein.sumProcess (Directional.information h.statistics (b a)) n ω) * L) +
        (4 / 3) * (R + M + D) * L ≤ |Bernstein.sumProcess (Directional.increment h.statistics (b a)) n ω|} ≤
      (Fintype.card α : ℝ) * (2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-L)) := by
  have hset : {ω | ∃ a, ∃ n ≤ T,
      (R + M + D) * Real.sqrt (2 * (1 + Bernstein.sumProcess (Directional.information h.statistics (b a)) n ω) * L) +
        (4 / 3) * (R + M + D) * L ≤ |Bernstein.sumProcess (Directional.increment h.statistics (b a)) n ω|} =
      ⋃ a, {ω | ∃ n ≤ T,
        (R + M + D) * Real.sqrt (2 * (1 + Bernstein.sumProcess (Directional.information h.statistics (b a)) n ω) * L) +
          (4 / 3) * (R + M + D) * L ≤ |Bernstein.sumProcess (Directional.increment h.statistics (b a)) n ω|} := by ext ω; simp
  rw [hset]
  calc
    _ ≤ ∑ a, μ.real {ω | ∃ n ≤ T,
        (R + M + D) * Real.sqrt (2 * (1 + Bernstein.sumProcess (Directional.information h.statistics (b a)) n ω) * L) +
          (4 / 3) * (R + M + D) * L ≤ |Bernstein.sumProcess (Directional.increment h.statistics (b a)) n ω|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : α, (2 * ((T + 1 : ℕ) : ℝ) * Real.exp (-L)) := by
      apply Finset.sum_le_sum
      intro a _
      exact SharpBernstein.paper_uniform hH (h.direction_data (b a) (hb a))
        (fun n ω => (Directional.information_bounds h.statistics (b a) (hb a) n ω).2) T hL
    _ = _ := by simp

end Family
end Part2.CNDProbability.M1Model
