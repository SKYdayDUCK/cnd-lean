import staging.cnd20261024.net.FiniteNet
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Module

namespace Part2.CNDNet

variable {ι : Type*} [Fintype ι]

/-- Pairwise-difference definition of max-minus-min oscillation. -/
def oscillation (x : ι → ℝ) : ℝ := ‖fun ij : ι × ι => x ij.1 - x ij.2‖

def sumLinear : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := Finset.sum_add_distrib
  map_smul' c x := by simp [Finset.mul_sum]

abbrev ZeroSum (ι : Type*) [Fintype ι] := ↥(LinearMap.ker (sumLinear (ι := ι)))

def differenceMap : ZeroSum ι →ₗ[ℝ] (ι × ι → ℝ) where
  toFun x ij := x.val ij.1 - x.val ij.2
  map_add' x y := by ext ij; simp; ring
  map_smul' c x := by ext ij; simp; ring

theorem differenceMap_injective [Nonempty ι] :
    Function.Injective (differenceMap (ι := ι)) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  have he : ∀ j, x.val j - y.val j = x.val i - y.val i := by
    intro j
    have := congrFun hxy (j, i)
    change x.val j - x.val i = y.val j - y.val i at this
    linarith
  have hz : ∑ j, (x.val j - y.val j) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hx : ∑ j, x.val j = 0 := x.property
    have hy : ∑ j, y.val j = 0 := y.property
    rw [hx, hy, sub_self]
  simp_rw [he] at hz
  simp only [Finset.sum_const, nsmul_eq_mul] at hz
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc)

theorem zeroSum_finrank [Nonempty ι] :
    finrank ℝ (ZeroSum ι) = Fintype.card ι - 1 := by
  have hn : (sumLinear (ι := ι)) ≠ 0 := by
    intro hz
    have hh := LinearMap.congr_fun hz (fun _ : ι => (1 : ℝ))
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact hc (by simpa [sumLinear] using hh)
  have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  simp only [Module.finrank_pi, Module.finrank_self, mul_one] at hh
  change finrank ℝ (ZeroSum ι) + 1 = Fintype.card ι at hh
  omega

/-- Exact sphere net in the zero-sum oscillation norm; dimension is K-1. -/
theorem exists_oscillation_net [Nonempty ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (ZeroSum ι),
      (∀ b ∈ s, oscillation b.val = 1) ∧
      (s.card : ℝ) ≤ (1 + 2 / ε) ^ (Fintype.card ι - 1) ∧
      ∀ a : ZeroSum ι, oscillation a.val = 1 →
        ∃ b ∈ s, oscillation (a.val - b.val) ≤ ε := by
  letI : NormedAddCommGroup (ZeroSum ι) :=
    NormedAddCommGroup.induced _ _ (differenceMap (ι := ι)).toAddMonoidHom
      differenceMap_injective
  letI : SeminormedAddCommGroup (ZeroSum ι) :=
    (inferInstance : NormedAddCommGroup (ZeroSum ι)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ (ZeroSum ι) := NormedSpace.induced ℝ _ _ (differenceMap (ι := ι))
  have hh := exists_sphere_net (E := ZeroSum ι) hε
  simpa only [zeroSum_finrank, oscillation, differenceMap] using hh

/-- The original CND-MAIN/SG14 choice, with the paper's exact cardinality. -/
theorem exists_paper_net [Nonempty ι] (T : ℕ) :
    ∃ s : Finset (ZeroSum ι),
      (∀ b ∈ s, oscillation b.val = 1) ∧
      (s.card : ℝ) ≤ (1 + 8 * (Fintype.card ι : ℝ) * (T + 1)) ^
        (Fintype.card ι - 1) ∧
      ∀ a : ZeroSum ι, oscillation a.val = 1 →
        ∃ b ∈ s, oscillation (a.val - b.val) ≤
          1 / (4 * (Fintype.card ι : ℝ) * (T + 1)) := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hε : 0 < 1 / (4 * (Fintype.card ι : ℝ) * (T + 1)) := by positivity
  have hh := exists_oscillation_net (ι := ι) hε
  have heq : (1 : ℝ) + 2 / (1 / (4 * (Fintype.card ι : ℝ) * (T + 1))) =
      1 + 8 * (Fintype.card ι : ℝ) * (T + 1) := by field_simp; ring
  simpa only [heq] using hh

end Part2.CNDNet
