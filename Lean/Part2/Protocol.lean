import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Real-arithmetic protocol components only. No claim about floating point,
PRNGs, clipped Gumbel sampling, INF projection, or stochastic regret. -/

noncomputable section

namespace Part2.Protocol

open scoped BigOperators

def physical (queue rtt processing : ℝ) : ℝ := queue + rtt + processing
def taxed (queue rtt processing tax : ℝ) : ℝ := physical queue rtt processing + tax
def residual (observed base : ℝ) : ℝ := observed - base

theorem physical_tax_separation (queue rtt processing tax : ℝ) :
    taxed queue rtt processing tax - physical queue rtt processing = tax := by
  unfold taxed
  ring

theorem physical_recovered_from_taxed (queue rtt processing tax : ℝ) :
    taxed queue rtt processing tax - tax = physical queue rtt processing := by
  unfold taxed
  ring

theorem residual_no_double_counting (observed base : ℝ) :
    base + residual observed base = observed := by
  unfold residual
  ring

theorem physical_residual_components (queue rtt processing base : ℝ) :
    residual (physical queue rtt processing) base =
      (queue - base) + rtt + processing := by
  unfold residual physical
  ring

theorem taxed_residual_components (queue rtt processing tax base : ℝ) :
    residual (taxed queue rtt processing tax) base =
      (queue - base) + rtt + processing + tax := by
  unfold residual taxed physical
  ring

/-- Adding an already present component a second time changes the target by it. -/
theorem extra_component_is_double_counted (observed base extra : ℝ) :
    base + (residual observed base + extra) = observed + extra := by
  unfold residual
  ring

def hybrid {α : Type*} [DecidableEq α] (base : α → ℝ)
    (chosen : α) (observed denominator : ℝ) (j : α) : ℝ :=
  base j + if j = chosen then residual observed (base chosen) / denominator else 0

theorem hybrid_unselected {α : Type*} [DecidableEq α] (base : α → ℝ)
    (chosen j : α) (observed denominator : ℝ) (h : j ≠ chosen) :
    hybrid base chosen observed denominator j = base j := by
  simp [hybrid, h]

theorem hybrid_selected {α : Type*} [DecidableEq α] (base : α → ℝ)
    (chosen : α) (observed denominator : ℝ) :
    hybrid base chosen observed denominator chosen =
      base chosen + (observed - base chosen) / denominator := by
  simp [hybrid, residual]

theorem ix_residual_bound (ρ probability γ bound : ℝ)
    (hρ : 0 ≤ ρ) (hR : ρ ≤ bound) (hp : 0 ≤ probability) (hγ : 0 < γ) :
    0 ≤ ρ / (probability + γ) ∧ ρ / (probability + γ) ≤ bound / γ := by
  have hden : 0 < probability + γ := by linarith
  constructor
  · exact div_nonneg hρ (le_of_lt hden)
  · apply (div_le_div_iff₀ hden hγ).mpr
    have hR0 : 0 ≤ bound := le_trans hρ hR
    nlinarith [mul_nonneg hR0 hp]

/-- The IX damping remainder is essential in the physical-loss identity. -/
theorem ix_reconstruction (ρ probability γ : ℝ) (hden : probability + γ ≠ 0) :
    probability * (ρ / (probability + γ)) +
      γ * ρ / (probability + γ) = ρ := by
  field_simp [hden]
  <;> ring

/-- Reconstruction is before importance weighting, not the selected hybrid value. -/
theorem weighted_selected_reconstruction (observed base denominator : ℝ)
    (hden : denominator ≠ 0) :
    base + denominator * (residual observed base / denominator) = observed := by
  unfold residual
  field_simp [hden]
  <;> ring

/-- A target-wide common shift cancels pointwise in regret. -/
theorem common_shift_cancels (actual comparator shift : ℝ) :
    (actual + shift) - (comparator + shift) = actual - comparator := by ring

/-- Error assumptions are supplied by the chosen quantizer, not proved here. -/
theorem residual_error_bound (queue base privatePart error : ℝ)
    (herr : |queue - base| ≤ error) :
    |residual (queue + privatePart) base - privatePart| ≤ error := by
  convert herr using 1 <;> congr 1 <;> unfold residual <;> ring

theorem residual_range (queue base privatePart error bound : ℝ)
    (herr : |queue - base| ≤ error)
    (hprivate : error ≤ privatePart) (hupper : privatePart ≤ bound) :
    0 ≤ residual (queue + privatePart) base ∧
      residual (queue + privatePart) base ≤ bound + error := by
  obtain ⟨hl, hu⟩ := abs_le.mp herr
  unfold residual
  constructor <;> linarith

theorem shifted_residual_range (queue base privatePart error bound : ℝ)
    (herr : |queue - base| ≤ error)
    (hprivate : 0 ≤ privatePart) (hupper : privatePart ≤ bound) :
    0 ≤ residual (queue + privatePart) base + error ∧
      residual (queue + privatePart) base + error ≤ bound + 2 * error := by
  obtain ⟨hl, hu⟩ := abs_le.mp herr
  unfold residual
  constructor <;> linarith

/-- The two codewords must use the same decoding function/seed. -/
theorem paired_counterfactual_identity {α β : Type*} [DecidableEq α]
    (background : α → ℕ) (decode : α → ℕ → β) (chosen j : α) :
    (if j = chosen then
      decode j (background j + if chosen = j then 1 else 0)
    else decode j (background j + (if chosen = j then 1 else 0) + 1)) =
      decode j (background j + 1) := by
  by_cases h : j = chosen
  · subst j
    simp
  · have h' : chosen ≠ j := Ne.symm h
    simp [h, h']

section Floor

variable {α : Type*} [Fintype α]

def floorExcess (p : α → ℝ) (ε : ℝ) (j : α) : ℝ := max (ε - p j) 0
def floorMass (p : α → ℝ) (ε : ℝ) : ℝ := ∑ j, floorExcess p ε j
def floorProbability (p : α → ℝ) (ε : ℝ) (j : α) : ℝ :=
  (p j + floorExcess p ε j) / (1 + floorMass p ε)

theorem floor_excess_nonneg (p : α → ℝ) (ε : ℝ) (j : α) :
    0 ≤ floorExcess p ε j := le_max_right _ _

theorem floor_mass_nonneg (p : α → ℝ) (ε : ℝ) : 0 ≤ floorMass p ε := by
  exact Finset.sum_nonneg fun j _ => floor_excess_nonneg p ε j

theorem floor_denominator_pos (p : α → ℝ) (ε : ℝ) :
    0 < 1 + floorMass p ε := by
  have := floor_mass_nonneg p ε
  linarith

theorem floor_numerator (p : α → ℝ) (ε : ℝ) (j : α) :
    p j + floorExcess p ε j = max (p j) ε := by
  unfold floorExcess
  by_cases h : ε ≤ p j
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left h]
    ring
  · have h' : p j ≤ ε := le_of_not_ge h
    rw [max_eq_left (sub_nonneg.mpr h'), max_eq_right h']
    ring

theorem floor_mass_le (p : α → ℝ) (ε : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hε : 0 ≤ ε) :
    floorMass p ε ≤ (Fintype.card α : ℝ) * ε := by
  calc
    floorMass p ε ≤ ∑ _j : α, ε := by
      apply Finset.sum_le_sum
      intro j _
      exact max_le (by linarith [hp j]) hε
    _ = (Fintype.card α : ℝ) * ε := by simp

theorem floor_probability_sum (p : α → ℝ) (ε : ℝ)
    (hsum : ∑ j, p j = 1) : ∑ j, floorProbability p ε j = 1 := by
  simp only [floorProbability, ← Finset.sum_div, Finset.sum_add_distrib, hsum]
  exact div_self (ne_of_gt (floor_denominator_pos p ε))

theorem floor_probability_lower (p : α → ℝ) (ε : ℝ) (j : α) :
    ε / (1 + floorMass p ε) ≤ floorProbability p ε j := by
  apply (div_le_div_iff_of_pos_right (floor_denominator_pos p ε)).mpr
  rw [floor_numerator]
  exact le_max_right _ _

theorem internal_le_normalized (p : α → ℝ) (ε : ℝ) (j : α) :
    p j ≤ (1 + floorMass p ε) * floorProbability p ε j := by
  unfold floorProbability
  have hd := ne_of_gt (floor_denominator_pos p ε)
  rw [mul_div_cancel₀ _ hd]
  linarith [floor_excess_nonneg p ε j]

theorem weighted_interval (w x : α → ℝ) (W : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ W) :
    0 ≤ ∑ j, w j * x j ∧
      (∑ j, w j * x j) ≤ (∑ j, w j) * W := by
  constructor
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hx j).1
  · rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j).2 (hw j)

/-- T7.2 for an interval of width W, with its sharper d/(1+d) factor.
No probabilistic sampling assertion is part of this deterministic lemma. -/
theorem floor_expectation_perturbation (p x : α → ℝ) (ε low W : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (hx : ∀ j, low ≤ x j ∧ x j ≤ low + W) :
    |∑ j, (floorProbability p ε j - p j) * x j| ≤
      floorMass p ε / (1 + floorMass p ε) * W := by
  let y : α → ℝ := fun j => x j - low
  have hy : ∀ j, 0 ≤ y j ∧ y j ≤ W := by
    intro j
    dsimp [y]
    constructor <;> linarith [(hx j).1, (hx j).2]
  obtain ⟨hP0, hPW⟩ := weighted_interval p y W hp hy
  obtain ⟨hE0, hEW⟩ := weighted_interval (floorExcess p ε) y W
    (floor_excess_nonneg p ε) hy
  rw [hsum, one_mul] at hPW
  change (∑ j, floorExcess p ε j * y j) ≤ floorMass p ε * W at hEW
  have hd := floor_mass_nonneg p ε
  have hZ := floor_denominator_pos p ε
  have hidentity : (∑ j, (floorProbability p ε j - p j) * x j) =
      ((∑ j, floorExcess p ε j * y j) -
        floorMass p ε * (∑ j, p j * y j)) / (1 + floorMass p ε) := by
    have hnorm := floor_probability_sum p ε hsum
    have hcenter : (∑ j, (floorProbability p ε j - p j) * x j) =
        ∑ j, (floorProbability p ε j - p j) * y j := by
      dsimp [y]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
        hnorm, hsum]
      ring
    rw [hcenter]
    simp only [floorProbability, sub_mul, add_div, add_mul, div_mul_eq_mul_div,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
    field_simp [ne_of_gt hZ]
    <;> ring
  rw [hidentity, abs_div, abs_of_pos hZ]
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hZ).mpr
  apply abs_le.mpr
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hPW hd]
  · nlinarith [mul_nonneg hd hP0]

/-- The coarse KεW version used in T7-S and in the T7-HP update correction. -/
theorem floor_expectation_perturbation_coarse (p x : α → ℝ) (ε low W : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) (hε : 0 ≤ ε) (hW : 0 ≤ W)
    (hx : ∀ j, low ≤ x j ∧ x j ≤ low + W) :
    |∑ j, (floorProbability p ε j - p j) * x j| ≤
      (Fintype.card α : ℝ) * ε * W := by
  have hd := floor_mass_nonneg p ε
  have hZ := floor_denominator_pos p ε
  have hratio : floorMass p ε / (1 + floorMass p ε) ≤ floorMass p ε := by
    apply (div_le_iff₀ hZ).mpr
    nlinarith [sq_nonneg (floorMass p ε)]
  exact (floor_expectation_perturbation p x ε low W hp hsum hx).trans
    (mul_le_mul_of_nonneg_right (hratio.trans (floor_mass_le p ε hp hε)) hW)

/-- T7-HP's deterministic floor term retains the 1/γ scale. The denominator
vector is supplied separately: this is no assertion that code samples from it. -/
theorem floor_hybrid_perturbation [DecidableEq α]
    (p base sampleProbability : α → ℝ) (chosen : α)
    (observed ε low B R γ : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) (hε : 0 ≤ ε)
    (hb : ∀ j, low ≤ base j ∧ base j ≤ low + B)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hγ : 0 < γ)
    (hsample : 0 ≤ sampleProbability chosen)
    (hρ : 0 ≤ residual observed (base chosen))
    (hρR : residual observed (base chosen) ≤ R) :
    |∑ j, (floorProbability p ε j - p j) *
      hybrid base chosen observed (sampleProbability chosen + γ) j| ≤
        (Fintype.card α : ℝ) * ε * (B + R / γ) := by
  obtain ⟨hterm0, htermR⟩ := ix_residual_bound
    (residual observed (base chosen)) (sampleProbability chosen) γ R hρ hρR hsample hγ
  have hRγ : 0 ≤ R / γ := div_nonneg hR (le_of_lt hγ)
  apply floor_expectation_perturbation_coarse p _ ε low (B + R / γ)
    hp hsum hε (add_nonneg hB hRγ)
  intro j
  by_cases hj : j = chosen
  · subst j
    rw [hybrid_selected]
    simp only [residual] at hterm0 htermR
    constructor <;> linarith [(hb chosen).1, (hb chosen).2]
  · rw [hybrid_unselected base chosen j observed (sampleProbability chosen + γ) hj]
    constructor <;> linarith [(hb j).1, (hb j).2]

end Floor

end Part2.Protocol
