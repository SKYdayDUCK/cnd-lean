import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Nat.Find

/-! Exact volumetric epsilon nets. The centers belong to the set being covered. -/
noncomputable section
open Metric Set Module MeasureTheory
open scoped ENNReal Topology Function

namespace Part2.CNDNet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The disjoint half-radius balls give the exact usual volume bound. -/
theorem separated_card_bound (s : Finset E) {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (1 + 2 / ε) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := ε / 2
  let ρ : ℝ := 1 + ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  set A := ⋃ x ∈ s, ball (x : E) δ with hA
  have hd : Set.Pairwise (s : Set E) (Disjoint on fun x => ball (x : E) δ) := by
    rintro x hx y hy hxy
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have := hsep x hx y hy hxy
    dsimp [δ]
    linarith
  have hsub : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    have := hs x hx
    dsimp [ρ, δ]
    linarith
  have hi : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [hA, measure_biUnion_finset hd fun x _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsub
      _ = _ := by simp only [μ.addHaar_ball_of_pos _ hρ]
  have hj : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_right (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hi
  have hk : (s.card : ℝ) * δ ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hj
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using this
  have heq : ρ / δ = 1 + 2 / ε := by
    dsimp [ρ, δ]
    field_simp
    <;> ring
  rw [← heq, div_pow]
  exact (le_div_iff₀ (pow_pos hδ _)).2 hk

/-- Every subset of a finite-dimensional unit ball admits a net with centers in that subset,
with no rounding loss in the real cardinality bound. In particular this applies to the sphere. -/
theorem exists_subset_net (S : Set E) (hS : ∀ x ∈ S, ‖x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ S) ∧
      (s.card : ℝ) ≤ (1 + 2 / ε) ^ finrank ℝ E ∧
      ∀ x ∈ S, ∃ y ∈ s, ‖x - y‖ ≤ ε := by
  classical
  let B : ℝ := (1 + 2 / ε) ^ finrank ℝ E
  let P : ℕ → Prop := fun n => ∃ s : Finset E, s.card = n ∧
    (∀ x ∈ s, x ∈ S) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ ‖x - y‖)
  have hzero : P 0 := ⟨∅, by simp⟩
  obtain ⟨s, hcard, hs, hsep⟩ :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le ⌈B⌉₊) hzero
  have hbound : (s.card : ℝ) ≤ B := separated_card_bound s hε (fun x hx => hS x (hs x hx)) hsep
  refine ⟨s, hs, hbound, ?_⟩
  intro x hx
  by_contra! hfar
  have hxnot : x ∉ s := by
    intro hxs
    have := hfar x hxs
    simp only [sub_self, norm_zero] at this
    linarith
  have hins : ∀ a ∈ insert x s, ∀ b ∈ insert x s, a ≠ b → ε ≤ ‖a - b‖ := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | haS
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (hab rfl).elim
      · exact (hfar b hb).le
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · rw [norm_sub_rev]
        exact (hfar a haS).le
      · exact hsep a haS b hbS hab
  have his : ∀ a ∈ insert x s, a ∈ S := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hx
    · exact hs a ha
  have hib : ((insert x s).card : ℝ) ≤ B :=
    separated_card_bound _ hε (fun a ha => hS a (his a ha)) hins
  have hinat : (insert x s).card ≤ ⌈B⌉₊ := by
    exact_mod_cast hib.trans (Nat.le_ceil B)
  have hip : P (s.card + 1) := ⟨insert x s, Finset.card_insert_of_notMem hxnot, his, hins⟩
  have hle := Nat.le_findGreatest (P := P) (by simpa [Finset.card_insert_of_notMem hxnot] using hinat) hip
  omega

theorem exists_sphere_net {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ = 1) ∧
      (s.card : ℝ) ≤ (1 + 2 / ε) ^ finrank ℝ E ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ ≤ ε := by
  simpa using exists_subset_net {x : E | ‖x‖ = 1} (fun x hx => hx.le) hε

end Part2.CNDNet
