import Part2.CND
import Part2.Protocol
import Part2.PhysicalQuantization
import Part2.PairConfidence
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
Original CND-PHYS protocol and finite geometry.  Primitive conditional kernels
are stated at their actual information layers, never replaced by global
independence.  The square-root/Schoenberg closure, direction-net probability
theorem and complete regret statement are not assumed or asserted here.
-/

noncomputable section

namespace Part2.CNDPhysical

open MeasureTheory Filter
open scoped BigOperators ProbabilityTheory Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cappedQueue_range (A F μ n lam : ℝ) (hA : 0 ≤ A) (hF : 0 ≤ F) :
    0 ≤ Part2.PhysicalQuantization.cappedQueue A F μ n lam ∧
    Part2.PhysicalQuantization.cappedQueue A F μ n lam ≤ F := by
  unfold Part2.PhysicalQuantization.cappedQueue
  split_ifs with h
  · exact ⟨le_min (div_nonneg hA (sub_pos.mpr h).le) hF, min_le_right _ _⟩
  · exact ⟨hF, le_refl _⟩

/-- This is the original atomic current/+1 protocol with one fixed seed per pair. -/
theorem atomic_paired_reconstruction (A F : ℝ) (μ lam : ι → ℝ)
    (background : ι → ℕ) (Q : ι → ℝ → ℝ) (chosen j : ι) :
    (if j = chosen then
      Q j (Part2.PhysicalQuantization.cappedQueue A F (μ j)
        (background j + if chosen = j then 1 else 0) (lam j))
    else Q j (Part2.PhysicalQuantization.cappedQueue A F (μ j)
        (background j + (if chosen = j then 1 else 0) + 1) (lam j))) =
      Q j (Part2.PhysicalQuantization.cappedQueue A F (μ j) (background j + 1) (lam j)) := by
  by_cases h : j = chosen
  · subst j
    simp
  · have h' : chosen ≠ j := Ne.symm h
    simp [h, h']

def roundBit (r u : ℝ) : ℝ := if u ≤ r then 1 else 0
def cellInput (lower Δ r : ℝ) : ℝ := lower + Δ * r
def cellRound (lower Δ r u : ℝ) : ℝ := lower + Δ * roundBit r u
def cellError (Δ r u : ℝ) : ℝ := Δ * (roundBit r u - r)

theorem cell_round_error (lower Δ r u : ℝ) :
    cellRound lower Δ r u - cellInput lower Δ r = cellError Δ r u := by
  unfold cellRound cellInput cellError
  ring

theorem cell_round_range (lower Δ r u : ℝ) (hΔ : 0 ≤ Δ) :
    lower ≤ cellRound lower Δ r u ∧ cellRound lower Δ r u ≤ lower + Δ := by
  unfold cellRound roundBit
  split_ifs <;> constructor <;> linarith

theorem cell_error_bound (Δ r u : ℝ) (hΔ : 0 ≤ Δ) (hr : 0 ≤ r ∧ r ≤ 1) :
    |cellError Δ r u| ≤ Δ := by
  unfold cellError roundBit
  split_ifs <;> rw [abs_le] <;> constructor <;>
    nlinarith [mul_nonneg hΔ hr.1, mul_nonneg hΔ (sub_nonneg.mpr hr.2)]

/-- Uniform seeds can be represented on (0,1], with exact deterministic endpoints. -/
theorem cell_endpoints (lower Δ u : ℝ) (hu : 0 < u ∧ u ≤ 1) :
    cellRound lower Δ 0 u = lower ∧ cellRound lower Δ 1 u = lower + Δ := by
  simp [cellRound, roundBit, not_le.mpr hu.1, hu.2]

theorem physical_residual (lower Δ r u θ z : ℝ) :
    (cellInput lower Δ r + θ + z) - cellRound lower Δ r u =
      θ + z - cellError Δ r u := by
  unfold cellInput cellRound cellError
  ring

def covariance (p : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (if i = j then p i else 0) - p i * p j

def coordinateMean (p x : ι → ℝ) : ℝ := ∑ i, p i * x i

theorem quadratic_eq_dot (B : Matrix ι ι ℝ) (x : ι → ℝ) :
    Part2.CND.quadratic B x = star x ⬝ᵥ (B *ᵥ x) := by
  simp only [Part2.CND.quadratic, dotProduct, Matrix.mulVec, star_trivial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem covariance_quadratic (p x : ι → ℝ) :
    Part2.CND.quadratic (covariance p) x =
      (∑ i, p i * (x i) ^ 2) - (coordinateMean p x) ^ 2 := by
  have hdiag : (∑ i, ∑ j, x i * x j * (if i = j then p i else 0)) =
      ∑ i, p i * (x i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_ite, eq_comm, pow_two]
    ring
  have hcross : (∑ i, ∑ j, x i * x j * (p i * p j)) =
      (coordinateMean p x) ^ 2 := by
    have hterm (i j : ι) : x i * x j * (p i * p j) = (p i * x i) * (p j * x j) := by
      ring
    simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
    simp only [coordinateMean, pow_two]
  unfold Part2.CND.quadratic covariance
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hdiag, hcross]

theorem covariance_variance (p x : ι → ℝ) (hs : (∑ i, p i) = 1) :
    Part2.CND.quadratic (covariance p) x =
      ∑ i, p i * (x i - coordinateMean p x) ^ 2 := by
  rw [covariance_quadratic]
  have hterm (i : ι) : p i * (x i - coordinateMean p x) ^ 2 =
      p i * (x i) ^ 2 - 2 * coordinateMean p x * (p i * x i) +
        (coordinateMean p x) ^ 2 * p i := by ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hs]
  unfold coordinateMean
  ring

theorem covariance_posSemidef (p : ι → ℝ) (hp : p ∈ Part2.CND.simplex) :
    (covariance p).PosSemidef := by
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, covariance]
    by_cases h : i = j
    · subst j
      rfl
    · simp [h, Ne.symm h]
      ring
  · intro x
    rw [← quadratic_eq_dot, covariance_variance p x hp.2]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp.1 i) (sq_nonneg _))

/-- Full-space regularization; on contrasts this is the original P+sum(C). -/
def information (p : ℕ → ι → ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  1 + ∑ t ∈ Finset.range n, covariance (p t)

theorem information_posDef (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) : (information p n).PosDef := by
  induction n with
  | zero => simpa [information] using (Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef)
  | succ n ih =>
      simpa [information, Finset.sum_range_succ, add_assoc] using
        ih.add_posSemidef (covariance_posSemidef (p n) (hp n))

def resistance (p : ℕ → ι → ℝ) (n : ℕ) : ι → ι → ℝ :=
  Part2.CND.gramDistance (@Inv.inv (Matrix ι ι ℝ) Matrix.inv (information p n))

/-- CND is proved for the computed inverse, rather than assumed as a radius premise. -/
theorem actual_resistance_isCND (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) :
    Part2.CND.IsCND (resistance p n) := by
  have hB := (information_posDef p hp n).inv.posSemidef
  apply Part2.CND.gramDistance_isCND
  · intro i j
    have hsym := congr_fun (congr_fun hB.isHermitian i) j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using hsym.symm
  · intro x
    rw [quadratic_eq_dot]
    exact hB.2 x

theorem actual_resistance_potential_convex (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (θ : ι → ℝ) :
    ConvexOn ℝ Part2.CND.simplex (Part2.CND.potential θ (resistance p n)) :=
  Part2.CND.potential_convexOn_simplex θ (resistance p n) (actual_resistance_isCND p hp n)

def c0 : ℝ := 1 - Real.exp (-1)

theorem c0_pos : 0 < c0 := by
  have h : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  unfold c0
  linarith

theorem saturation_normalized (x : ℝ) (hx : 0 ≤ x) :
    c0 * min 1 x ≤ 1 - Real.exp (-x) ∧
      1 - Real.exp (-x) ≤ min 1 x := by
  constructor
  · by_cases h1 : x ≤ 1
    · have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
        (show 0 ≤ 1 - x by linarith) hx (show (1 - x) + x = 1 by ring)
      simp only [smul_eq_mul, mul_zero, zero_add, mul_neg, mul_one, Real.exp_zero] at hc
      rw [min_eq_right h1]
      unfold c0
      nlinarith
    · have hge : 1 ≤ x := le_of_lt (lt_of_not_ge h1)
      have he : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      rw [min_eq_left hge]
      unfold c0
      linarith
  · apply le_min
    · linarith [Real.exp_pos (-x)]
    · have he := Real.add_one_le_exp (-x)
      linarith

def saturatedRadius (R ρ : ℝ) : ℝ := (2 * R / c0) * (1 - Real.exp (-(ρ / R)))

/-- The exact c0 factor and both min bounds of the actual saturation formula. -/
theorem saturatedRadius_bounds (R ρ : ℝ) (hR : 0 < R) (hρ : 0 ≤ ρ) :
    min (2 * R) (2 * ρ) ≤ saturatedRadius R ρ ∧
      saturatedRadius R ρ ≤ min (2 * R / c0) (2 * ρ / c0) := by
  have hx : 0 ≤ ρ / R := div_nonneg hρ hR.le
  obtain ⟨hl, hu⟩ := saturation_normalized (ρ / R) hx
  have hf : 0 < 2 * R / c0 := div_pos (by linarith) c0_pos
  have hl' := mul_le_mul_of_nonneg_left hl hf.le
  have hu' := mul_le_mul_of_nonneg_left hu hf.le
  have hc : c0 ≠ 0 := ne_of_gt c0_pos
  have hR0 : R ≠ 0 := ne_of_gt hR
  by_cases h : ρ ≤ R
  · have hratio : ρ / R ≤ 1 := (div_le_one hR).2 h
    rw [min_eq_right hratio] at hl' hu'
    rw [min_eq_right (by linarith : 2 * ρ ≤ 2 * R)]
    constructor
    · convert hl' using 1 <;> (try simp only [saturatedRadius]) <;> field_simp [hc, hR0] <;> ring
    · apply le_min
      · have he := (saturation_normalized (ρ / R) hx).2.trans (min_le_left _ _)
        simpa only [saturatedRadius, mul_one] using mul_le_mul_of_nonneg_left he hf.le
      · convert hu' using 1 <;> (try simp only [saturatedRadius]) <;> field_simp [hc, hR0] <;> ring
  · have hge : R ≤ ρ := le_of_lt (lt_of_not_ge h)
    have hratio : 1 ≤ ρ / R := (le_div_iff₀ hR).2 (by simpa using hge)
    rw [min_eq_left hratio] at hl' hu'
    rw [min_eq_left (by linarith : 2 * R ≤ 2 * ρ)]
    constructor
    · convert hl' using 1 <;> (try simp only [saturatedRadius]) <;> field_simp [hc, hR0] <;> ring
    · apply le_min
      · simpa [saturatedRadius] using hu'
      · have hscale : 2 * R / c0 ≤ 2 * ρ / c0 :=
          div_le_div_of_nonneg_right (by linarith) c0_pos.le
        have hupper : saturatedRadius R ρ ≤ 2 * R / c0 := by
          simpa [saturatedRadius] using hu'
        exact hupper.trans hscale

def contrast (i j : ι) (k : ι) : ℝ :=
  (if k = i then 1 else 0) - (if k = j then 1 else 0)

theorem contrast_sum (i j : ι) : (∑ k, contrast i j k) = 0 := by
  simp [contrast, Finset.sum_sub_distrib]

theorem gramDistance_energy (B : Matrix ι ι ℝ) (hsym : ∀ i j, B i j = B j i) (i j : ι) :
    Part2.CND.gramDistance B i j = star (contrast i j) ⬝ᵥ (B *ᵥ contrast i j) := by
  have hmul (k : ι) : (B *ᵥ contrast i j) k = B k i - B k j := by
    simp [Matrix.mulVec, dotProduct, contrast, mul_sub, mul_ite, Finset.sum_sub_distrib]
  simp only [dotProduct, star_trivial]
  simp_rw [hmul]
  simp only [contrast, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold Part2.CND.gramDistance
  rw [hsym j i]
  ring

theorem actual_resistance_nonneg (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (i j : ι) : 0 ≤ resistance p n i j := by
  have hB := (information_posDef p hp n).inv.posSemidef
  have hsym : ∀ i j, (@Inv.inv (Matrix ι ι ℝ) Matrix.inv (information p n)) i j =
      (@Inv.inv (Matrix ι ι ℝ) Matrix.inv (information p n)) j i := by
    intro i j
    have h := congr_fun (congr_fun hB.isHermitian i) j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
  unfold resistance
  rw [gramDistance_energy _ hsym i j]
  exact hB.2 (contrast i j)

def inverseInformation (p : ℕ → ι → ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  @Inv.inv (Matrix ι ι ℝ) Matrix.inv (information p n)

theorem covariance_mul_ones (p : ι → ℝ) (hp : p ∈ Part2.CND.simplex) :
    covariance p *ᵥ (fun _ => 1) = fun _ => 1 - (1 : ℝ) := by
  funext i
  simp [Matrix.mulVec, dotProduct, covariance, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hp.2]

theorem information_mul_ones (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) :
    information p n *ᵥ (fun _ => 1) = fun _ => (1 : ℝ) := by
  induction n with
  | zero => simp [information]
  | succ n ih =>
      have heq : information p (n + 1) = information p n + covariance (p n) := by
        simp [information, Finset.sum_range_succ, add_assoc]
      rw [heq, Matrix.add_mulVec, ih, covariance_mul_ones (p n) (hp n)]
      funext i
      simp

theorem inverseInformation_mul (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) :
    inverseInformation p n * information p n = 1 ∧
      information p n * inverseInformation p n = 1 := by
  have hdet : IsUnit (information p n).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (information_posDef p hp n).det_pos)
  exact ⟨Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet⟩

theorem inverseInformation_mul_ones (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) :
    inverseInformation p n *ᵥ (fun _ => 1) = fun _ => (1 : ℝ) := by
  have h := congrArg (fun B : Matrix ι ι ℝ => B *ᵥ (fun _ => (1 : ℝ)))
    (inverseInformation_mul p hp n).1
  dsimp only at h
  rw [← Matrix.mulVec_mulVec, information_mul_ones p hp n, Matrix.one_mulVec] at h
  exact h

theorem inverseInformation_preserves_zero_sum (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (x : ι → ℝ)
    (hx : (∑ i, x i) = 0) : (∑ i, (inverseInformation p n *ᵥ x) i) = 0 := by
  have hB := (information_posDef p hp n).inv.posSemidef
  have hsym (i j : ι) : inverseInformation p n i j = inverseInformation p n j i := by
    have h := congr_fun (congr_fun hB.isHermitian i) j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
  have hcol (j : ι) : (∑ i, inverseInformation p n i j) = 1 := by
    calc
      _ = ∑ i, inverseInformation p n j i := Finset.sum_congr rfl (fun i _ => hsym i j)
      _ = 1 := by
        simpa [Matrix.mulVec, dotProduct] using congr_fun (inverseInformation_mul_ones p hp n) j
  change (∑ i, ∑ j, inverseInformation p n i j * x j) = 0
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcol, one_mul]
  exact hx

/-- Exactly the original Pi+sum(C), written by its action on a vector. -/
def tangentInformation (p : ℕ → ι → ℝ) (n : ℕ) (x : ι → ℝ) (i : ι) : ℝ :=
  x i - (∑ j, x j) / (Fintype.card ι : ℝ) +
    ((∑ t ∈ Finset.range n, covariance (p t)) *ᵥ x) i

theorem tangentInformation_on_zero_sum (p : ℕ → ι → ℝ) (n : ℕ) (x : ι → ℝ)
    (hx : (∑ i, x i) = 0) : tangentInformation p n x = information p n *ᵥ x := by
  funext i
  simp [tangentInformation, hx, information, Matrix.add_mulVec]

/-- Identification bridge: the computed full inverse gives the unique solution
of the original Laplacian equation on the zero-sum tangent space. -/
theorem inverse_tangent_direction (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (b : ι → ℝ)
    (hb : (∑ i, b i) = 0) :
    (∑ i, (inverseInformation p n *ᵥ b) i) = 0 ∧
      tangentInformation p n (inverseInformation p n *ᵥ b) = b ∧
      (∀ x : ι → ℝ, (∑ i, x i) = 0 → tangentInformation p n x = b →
        x = inverseInformation p n *ᵥ b) := by
  have hu := inverseInformation_preserves_zero_sum p hp n b hb
  refine ⟨hu, ?_, ?_⟩
  · rw [tangentInformation_on_zero_sum p n _ hu, Matrix.mulVec_mulVec,
      (inverseInformation_mul p hp n).2, Matrix.one_mulVec]
  · intro x hx heq
    rw [tangentInformation_on_zero_sum p n x hx] at heq
    calc
      x = inverseInformation p n *ᵥ (information p n *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, (inverseInformation_mul p hp n).1, Matrix.one_mulVec]
      _ = inverseInformation p n *ᵥ b := congrArg (fun y => inverseInformation p n *ᵥ y) heq

theorem actual_resistance_contrast_equation (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (i j : ι) :
    let u := inverseInformation p n *ᵥ contrast i j
    (∑ k, u k) = 0 ∧ tangentInformation p n u = contrast i j ∧
      resistance p n i j = contrast i j ⬝ᵥ u := by
  have hdir := inverse_tangent_direction p hp n (contrast i j) (contrast_sum i j)
  refine ⟨hdir.1, hdir.2.1, ?_⟩
  have hB := (information_posDef p hp n).inv.posSemidef
  have hsym (i j : ι) : inverseInformation p n i j = inverseInformation p n j i := by
    have h := congr_fun (congr_fun hB.isHermitian i) j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
  simpa only [star_trivial] using gramDistance_energy (inverseInformation p n) hsym i j

def pairRadius (p : ℕ → ι → ℝ) (n : ℕ) (H L R : ℝ) (i j : ι) : ℝ :=
  2 * H * Real.sqrt (L * resistance p n i j) +
    (4 * H * L + R * Fintype.card ι) * resistance p n i j

def actualSaturatedRadius (p : ℕ → ι → ℝ) (n : ℕ) (H L R : ℝ) (i j : ι) : ℝ :=
  saturatedRadius R (pairRadius p n H L R i j)

theorem pairRadius_nonneg (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex)
    (n : ℕ) (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) (i j : ι) :
    0 ≤ pairRadius p n H L R i j := by
  unfold pairRadius
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hH) (Real.sqrt_nonneg _))
    (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hH) hL)
      (mul_nonneg hR (Nat.cast_nonneg _))) (actual_resistance_nonneg p hp n i j))

/-- Pointwise bounds for the actual constructed rho and saturated radius.
The Schoenberg assertion that this saturated matrix is CND remains separate. -/
theorem actual_saturated_radius_geometry (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (H L R : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) :
    (∀ i j, actualSaturatedRadius p n H L R i j = actualSaturatedRadius p n H L R j i) ∧
    (∀ i, actualSaturatedRadius p n H L R i i = 0) ∧
    (∀ i j, min (2 * R) (2 * pairRadius p n H L R i j) ≤
      actualSaturatedRadius p n H L R i j ∧
      actualSaturatedRadius p n H L R i j ≤
        min (2 * R / c0) (2 * pairRadius p n H L R i j / c0)) := by
  have hd := actual_resistance_isCND p hp n
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    unfold actualSaturatedRadius pairRadius
    rw [hd.1 i j]
  · intro i
    simp [actualSaturatedRadius, pairRadius, hd.2.1 i, saturatedRadius]
  · intro i j
    exact saturatedRadius_bounds R _ hR (pairRadius_nonneg p hp n H L R hH hL hR.le i j)

/-- The deterministic finite variance reduction used in P8. -/
theorem weighted_second_moment_bound (p a Y : ι → ℝ) (hp : p ∈ Part2.CND.simplex)
    (H : ℝ) (hH : 0 ≤ H) (hY : ∀ i, |Y i| ≤ H) :
    (∑ i, p i * (a i - coordinateMean p a) ^ 2 * (Y i) ^ 2) ≤
      H ^ 2 * Part2.CND.quadratic (covariance p) a := by
  rw [covariance_variance p a hp.2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hsq : (Y i) ^ 2 ≤ H ^ 2 := by
    have hbounds := abs_le.mp (hY i)
    nlinarith [mul_nonneg (show 0 ≤ H - Y i by linarith)
      (show 0 ≤ H + Y i by linarith)]
  have hmul := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (hp.1 i) (sq_nonneg (a i - coordinateMean p a)))
  nlinarith [hmul]

theorem probability_bounds (p : ι → ℝ) (hp : p ∈ Part2.CND.simplex) (i : ι) :
    0 ≤ p i ∧ p i ≤ 1 := by
  refine ⟨hp.1 i, ?_⟩
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)

theorem feature_bound (p : ι → ℝ) (hp : p ∈ Part2.CND.simplex) (a i : ι) :
    |(if a = i then 1 else 0) - p i| ≤ 1 := by
  obtain ⟨hl, hu⟩ := probability_bounds p hp i
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem direction_feature_bound (p a : ι → ℝ) (hp : p ∈ Part2.CND.simplex)
    (hspan : ∀ i j, a i - a j ≤ 1) (k : ι) :
    |a k - coordinateMean p a| ≤ 1 := by
  have hlo : (∑ j, p j * (-1)) ≤ ∑ j, p j * (a k - a j) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (by linarith [hspan j k]) (hp.1 j)
  have hhi : (∑ j, p j * (a k - a j)) ≤ ∑ j, p j * 1 := by
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hspan k j) (hp.1 j))
  have hid : (∑ j, p j * (a k - a j)) = a k - coordinateMean p a := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul,
      coordinateMean]
  rw [hid] at hlo hhi
  rw [← Finset.sum_mul, hp.2] at hlo hhi
  rw [abs_le]
  constructor <;> linarith

theorem physical_residual_bound (R M Δ θ z r U : ℝ)
    (hΔ : 0 ≤ Δ) (hθ : 0 ≤ θ ∧ θ ≤ R) (hz : 0 ≤ z ∧ z ≤ M)
    (hr : 0 ≤ r ∧ r ≤ 1) : |θ + z - cellError Δ r U| ≤ R + M + Δ := by
  calc
    _ ≤ |θ + z| + |cellError Δ r U| := abs_sub _ _
    _ ≤ R + M + Δ := by
      rw [abs_of_nonneg (by linarith [hθ.1, hz.1])]
      linarith [cell_error_bound Δ r U hΔ hr, hθ.2, hz.2]

/-- P8's pointwise 2H increment bound from the actual physical residual.
No conditional variance or direction-net probability event is assumed. -/
theorem physical_direction_increment_bound (p a θ r U : ι → ℝ) (z R M Δ : ℝ)
    (hp : p ∈ Part2.CND.simplex) (hspan : ∀ i j, a i - a j ≤ 1)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ R) (hz : 0 ≤ z ∧ z ≤ M)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) (hΔ : 0 ≤ Δ) (k : ι) :
    |(a k - coordinateMean p a) * (θ k + z - cellError Δ (r k) (U k)) -
      (∑ j, p j * (a j - coordinateMean p a) * θ j)| ≤ 2 * (R + M + Δ) := by
  have hY := physical_residual_bound R M Δ (θ k) z (r k) (U k) hΔ (hθ k) hz (hr k)
  have hfeat := direction_feature_bound p a hp hspan k
  have hprod : |(a k - coordinateMean p a) * (θ k + z - cellError Δ (r k) (U k))| ≤
      R + M + Δ := by
    rw [abs_mul]
    exact (mul_le_mul hfeat hY (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hmean : |∑ j, p j * (a j - coordinateMean p a) * θ j| ≤ R := by
    calc
      _ ≤ ∑ j, |p j * (a j - coordinateMean p a) * θ j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, p j * R := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul, abs_of_nonneg (hp.1 j), abs_of_nonneg (hθ j).1]
        have hm := mul_le_mul_of_nonneg_left (direction_feature_bound p a hp hspan j) (hp.1 j)
        have ht := mul_le_mul hm (hθ j).2 (hθ j).1 (by simpa using hp.1 j)
        simpa only [mul_one] using ht
      _ = R := by rw [← Finset.sum_mul, hp.2, one_mul]
  have hM : 0 ≤ M := (hz.1.trans hz.2)
  calc
    _ ≤ |(a k - coordinateMean p a) * (θ k + z - cellError Δ (r k) (U k))| +
        |∑ j, p j * (a j - coordinateMean p a) * θ j| := abs_sub _ _
    _ ≤ 2 * (R + M + Δ) := by linarith

theorem categorical_orthogonality (p θ : ι → ℝ) (z : ℝ)
    (hs : (∑ a, p a) = 1) (i : ι) :
    (∑ a, p a * (((if a = i then 1 else 0) - p i) * (θ a + z))) =
      p i * (θ i - coordinateMean p θ) := by
  have hterm (a : ι) :
      p a * (((if a = i then 1 else 0) - p i) * (θ a + z)) =
        (if a = i then p a * (θ a + z) else 0) -
          p i * (p a * θ a) - (p i * z) * p a := by
    split_ifs <;> ring
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hs]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold coordinateMean
  ring

section Conditional

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem roundBit_measurable {r U : Ω → ℝ} (hr : Measurable r) (hU : Measurable U) :
    Measurable (fun ω => roundBit (r ω) (U ω)) :=
  measurable_const.ite (measurableSet_le hU hr) measurable_const

/-- The input is the fresh conditional uniform CDF at the cell fraction, not
the desired error-centering equality and not a global independence assertion. -/
theorem conditional_cell_error_zero {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    (r U : Ω → ℝ) (Δ : ℝ) (hrm : StronglyMeasurable[m] r)
    (hri : Integrable r μ) (hIi : Integrable (fun ω => roundBit (r ω) (U ω)) μ)
    (hCDF : μ[fun ω => roundBit (r ω) (U ω) | m] =ᵐ[μ] r) :
    μ[fun ω => cellError Δ (r ω) (U ω) | m] =ᵐ[μ] fun _ => 0 := by
  have hsub := condExp_sub hIi hri m
  have hmul := condExp_smul (μ := μ) Δ (fun ω => roundBit (r ω) (U ω) - r ω) m
  have hr := condExp_of_stronglyMeasurable hm hrm hri
  filter_upwards [hsub, hmul, hCDF] with ω hs hm' hCDF
  change (μ[fun ω => Δ * (roundBit (r ω) (U ω) - r ω) | m]) ω = 0
  change (μ[fun ω => Δ * (roundBit (r ω) (U ω) - r ω) | m]) ω =
    Δ * (μ[fun ω => roundBit (r ω) (U ω) - r ω | m]) ω at hm'
  change (μ[fun ω => roundBit (r ω) (U ω) - r ω | m]) ω =
    (μ[fun ω => roundBit (r ω) (U ω) | m]) ω - (μ[r | m]) ω at hs
  rw [hm', hs, hCDF, hr]
  ring

def score (p : ι → Ω → ℝ) (θ : ι → ℝ) (z : Ω → ℝ)
    (e : ι → Ω → ℝ) (A : Ω → ι) (i : ι) (ω : Ω) : ℝ :=
  (Part2.PairConfidence.actionIndicator A i ω - p i ω) *
    (θ (A ω) + z ω - e (A ω) ω)

def covarianceTheta (p : ι → Ω → ℝ) (θ : ι → ℝ) (i : ι) (ω : Ω) : ℝ :=
  p i ω * (θ i - ∑ a, p a ω * θ a)

/-- Conditional orthogonality on the original space, using two different
information layers. Integrability premises are explicit technical obligations. -/
theorem conditional_orthogonal_center {G Ainfo : MeasurableSpace Ω}
    (hGA : G ≤ Ainfo) (hA0 : Ainfo ≤ m₀)
    (A : Ω → ι) [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hAm : Measurable[Ainfo] A) (p : ι → Ω → ℝ) (θ : ι → ℝ) (z : Ω → ℝ)
    (e : ι → Ω → ℝ) (i : ι)
    (hpm : ∀ a, StronglyMeasurable[G] (p a)) (hzm : StronglyMeasurable[G] z)
    (hs : ∀ ω, (∑ a, p a ω) = 1)
    (hlaw : ∀ a, μ[Part2.PairConfidence.actionIndicator A a | G] =ᵐ[μ] p a)
    (he0 : ∀ a, μ[e a | Ainfo] =ᵐ[μ] fun _ => 0)
    (hei : ∀ a, Integrable (e a) μ)
    (hfi : ∀ a, Integrable (fun ω =>
      ((if a = i then 1 else 0) - p i ω) * (θ a + z ω)) μ)
    (hEi : Integrable (fun ω =>
      (Part2.PairConfidence.actionIndicator A i ω - p i ω) * e (A ω) ω) μ) :
    μ[score p θ z e A i | G] =ᵐ[μ] covarianceTheta p θ i := by
  letI : MeasurableSpace Ω := m₀
  let f : ι → Ω → ℝ := fun a ω =>
    ((if a = i then 1 else 0) - p i ω) * (θ a + z ω)
  have hfm (a : ι) : StronglyMeasurable[G] (f a) :=
    (stronglyMeasurable_const.sub (hpm i)).mul (stronglyMeasurable_const.add hzm)
  have hAmeas : Measurable A := hAm.mono hA0 le_rfl
  have hsel := Part2.PairConfidence.conditional_selected (μ := μ) hAmeas hlaw f hfm hfi
  have hseli : Integrable (fun ω => f (A ω) ω) μ :=
    Part2.PairConfidence.selected_integrable hAmeas hfi
  have heSelected := Part2.PairConfidence.conditional_selected_zero hA0 hAm e hei he0
  have heSelectedi : Integrable (fun ω => e (A ω) ω) μ :=
    Part2.PairConfidence.selected_integrable hAmeas hei
  have hcoef : StronglyMeasurable[Ainfo]
      (fun ω => Part2.PairConfidence.actionIndicator A i ω - p i ω) :=
    (Part2.PairConfidence.actionIndicator_measurable hAm i).stronglyMeasurable.sub
      ((hpm i).mono hGA)
  have hpull := condExp_mul_of_stronglyMeasurable_left hcoef hEi heSelectedi
  have herrorA : μ[fun ω =>
      (Part2.PairConfidence.actionIndicator A i ω - p i ω) * e (A ω) ω | Ainfo] =ᵐ[μ]
      fun _ => 0 := by
    filter_upwards [hpull, heSelected] with ω hp he
    change (μ[fun ω =>
      (Part2.PairConfidence.actionIndicator A i ω - p i ω) * e (A ω) ω | Ainfo]) ω = 0
    change (μ[fun ω =>
      (Part2.PairConfidence.actionIndicator A i ω - p i ω) * e (A ω) ω | Ainfo]) ω =
      (Part2.PairConfidence.actionIndicator A i ω - p i ω) *
        (μ[fun ω => e (A ω) ω | Ainfo]) ω at hp
    rw [hp, he, mul_zero]
  have herrorG := Part2.PairConfidence.conditional_zero_down hGA hA0 herrorA
  have hsub := condExp_sub hseli hEi G
  have heq : score p θ z e A i =
      (fun ω => f (A ω) ω) - (fun ω =>
        (Part2.PairConfidence.actionIndicator A i ω - p i ω) * e (A ω) ω) := by
    funext ω
    dsimp [score, f, Part2.PairConfidence.actionIndicator]
    ring
  rw [heq]
  filter_upwards [hsub, hsel, herrorG] with ω hsub hsel he
  change (μ[(fun ω => f (A ω) ω) - (fun ω =>
      (Part2.PairConfidence.actionIndicator A i ω - p i ω) * e (A ω) ω) | G]) ω =
    covarianceTheta p θ i ω
  change (μ[(fun ω => f (A ω) ω) - (fun ω =>
      (Part2.PairConfidence.actionIndicator A i ω - p i ω) * e (A ω) ω) | G]) ω =
    (μ[fun ω => f (A ω) ω | G]) ω - (μ[fun ω =>
      (Part2.PairConfidence.actionIndicator A i ω - p i ω) * e (A ω) ω | G]) ω at hsub
  rw [hsub, hsel, he, sub_zero]
  exact categorical_orthogonality (fun a => p a ω) θ (z ω) (hs ω) i

theorem covarianceTheta_stronglyMeasurable {G : MeasurableSpace Ω}
    (p : ι → Ω → ℝ) (θ : ι → ℝ) (i : ι)
    (hpm : ∀ a, StronglyMeasurable[G] (p a)) :
    StronglyMeasurable[G] (covarianceTheta p θ i) := by
  letI : MeasurableSpace Ω := G
  exact ((hpm i).measurable.mul (measurable_const.sub
    (Finset.measurable_fun_sum _ (fun a _ => (hpm a).measurable.mul measurable_const)))).stronglyMeasurable

theorem centered_past {Past G : MeasurableSpace Ω} (hPG : Past ≤ G) (hG0 : G ≤ m₀)
    (f c : Ω → ℝ) (hfi : Integrable f μ) (hcm : StronglyMeasurable[Past] c)
    (hmean : μ[f | G] =ᵐ[μ] c) :
    μ[fun ω => f ω - c ω | Past] =ᵐ[μ] fun _ => 0 := by
  letI : MeasurableSpace Ω := m₀
  have hci : Integrable c μ := integrable_condExp.congr hmean
  have hsub := condExp_sub hfi hci G
  have hc := condExp_of_stronglyMeasurable hG0 (hcm.mono hPG) hci
  have hz : μ[fun ω => f ω - c ω | G] =ᵐ[μ] fun _ => 0 := by
    filter_upwards [hsub, hmean] with ω hs hm
    change (μ[fun ω => f ω - c ω | G]) ω = 0
    change (μ[fun ω => f ω - c ω | G]) ω = (μ[f | G]) ω - (μ[c | G]) ω at hs
    rw [hs, hm, hc]
    ring
  exact Part2.PairConfidence.conditional_zero_down hPG hG0 hz

/-- Bounded physical cell rounding closes P7 from the actual conditional
uniform-CDF and categorical kernels. All integrability is derived from bounds. -/
theorem physical_conditional_center {G Ainfo : MeasurableSpace Ω}
    (hGA : G ≤ Ainfo) (hA0 : Ainfo ≤ m₀)
    (A : Ω → ι) [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hAm : Measurable[Ainfo] A) (p : ι → Ω → ℝ) (θ : ι → ℝ) (z : Ω → ℝ)
    (r U : ι → Ω → ℝ) (R M Δ : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) (hΔ : 0 ≤ Δ)
    (hpm : ∀ a, StronglyMeasurable[G] (p a)) (hzm : StronglyMeasurable[G] z)
    (hrm : ∀ a, StronglyMeasurable[G] (r a)) (hUm : ∀ a, Measurable[m₀] (U a))
    (hp : ∀ ω, (fun a => p a ω) ∈ Part2.CND.simplex)
    (hθ : ∀ a, 0 ≤ θ a ∧ θ a ≤ R) (hz : ∀ ω, 0 ≤ z ω ∧ z ω ≤ M)
    (hr : ∀ a ω, 0 ≤ r a ω ∧ r a ω ≤ 1)
    (hlaw : ∀ a, μ[Part2.PairConfidence.actionIndicator A a | G] =ᵐ[μ] p a)
    (hCDF : ∀ a, μ[fun ω => roundBit (r a ω) (U a ω) | Ainfo] =ᵐ[μ] r a)
    (i : ι) :
    let e : ι → Ω → ℝ := fun a ω => cellError Δ (r a ω) (U a ω)
    Integrable (score p θ z e A i) μ ∧
      μ[score p θ z e A i | G] =ᵐ[μ] covarianceTheta p θ i ∧
      ∀ Past : MeasurableSpace Ω, Past ≤ G → (∀ a, StronglyMeasurable[Past] (p a)) →
        μ[fun ω => score p θ z e A i ω - covarianceTheta p θ i ω | Past] =ᵐ[μ]
          fun _ => 0 := by
  letI : MeasurableSpace Ω := m₀
  let e : ι → Ω → ℝ := fun a ω => cellError Δ (r a ω) (U a ω)
  have hG0 : G ≤ m₀ := hGA.trans hA0
  have hAmeas : Measurable A := hAm.mono hA0 le_rfl
  have hbitm (a : ι) : Measurable (fun ω => roundBit (r a ω) (U a ω)) :=
    roundBit_measurable ((hrm a).mono hG0).measurable (hUm a)
  have hri (a : ι) : Integrable (r a) μ :=
    Part2.PairConfidence.bounded_integrable ((hrm a).mono hG0).measurable
      (fun ω => by rw [abs_of_nonneg (hr a ω).1]; exact (hr a ω).2)
  have hIi (a : ι) : Integrable (fun ω => roundBit (r a ω) (U a ω)) μ :=
    Part2.PairConfidence.bounded_integrable (B := (1 : ℝ)) (hbitm a)
      (fun ω => by unfold roundBit; split_ifs <;> norm_num)
  have hem (a : ι) : Measurable (e a) :=
    measurable_const.mul ((hbitm a).sub ((hrm a).mono hG0).measurable)
  have hei (a : ι) : Integrable (e a) μ :=
    Part2.PairConfidence.bounded_integrable (hem a)
      (fun ω => cell_error_bound Δ (r a ω) (U a ω) hΔ (hr a ω))
  have he0 (a : ι) : μ[e a | Ainfo] =ᵐ[μ] fun _ => 0 :=
    conditional_cell_error_zero hA0 (r a) (U a) Δ ((hrm a).mono hGA)
      (hri a) (hIi a) (hCDF a)
  have hfBound (a : ι) (ω : Ω) :
      |((if a = i then 1 else 0) - p i ω) * (θ a + z ω)| ≤ R + M := by
    have h1 := feature_bound (fun a => p a ω) (hp ω) a i
    have h2 : |θ a + z ω| ≤ R + M := by
      rw [abs_of_nonneg (by linarith [(hθ a).1, (hz ω).1])]
      linarith [(hθ a).2, (hz ω).2]
    rw [abs_mul]
    exact (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hfi (a : ι) : Integrable (fun ω =>
      ((if a = i then 1 else 0) - p i ω) * (θ a + z ω)) μ := by
    have hfm : StronglyMeasurable[G] (fun ω =>
        ((if a = i then 1 else 0) - p i ω) * (θ a + z ω)) :=
      (stronglyMeasurable_const.sub (hpm i)).mul (stronglyMeasurable_const.add hzm)
    exact Part2.PairConfidence.bounded_integrable (hfm.mono hG0).measurable (hfBound a)
  have hcoefm : Measurable (fun ω => Part2.PairConfidence.actionIndicator A i ω - p i ω) :=
    (Part2.PairConfidence.actionIndicator_measurable hAmeas i).sub ((hpm i).mono hG0).measurable
  have hselectedm := Part2.PairConfidence.selected_measurable hAmeas hem
  have hEi : Integrable (fun ω =>
      (Part2.PairConfidence.actionIndicator A i ω - p i ω) * e (A ω) ω) μ := by
    apply Part2.PairConfidence.bounded_integrable (hcoefm.mul hselectedm)
    intro ω
    have hc : |Part2.PairConfidence.actionIndicator A i ω - p i ω| ≤ 1 :=
      feature_bound (fun a => p a ω) (hp ω) (A ω) i
    have he : |e (A ω) ω| ≤ Δ := cell_error_bound Δ _ _ hΔ (hr (A ω) ω)
    rw [abs_mul]
    exact (mul_le_mul hc he (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hcenter := conditional_orthogonal_center hGA hA0 A hAm p θ z e i hpm hzm
    (fun ω => (hp ω).2) hlaw he0 hei hfi hEi
  have hselectedi := Part2.PairConfidence.selected_integrable hAmeas hfi
  have hscorei : Integrable (score p θ z e A i) μ := by
    convert hselectedi.sub hEi using 1
    funext ω
    dsimp [score, Part2.PairConfidence.actionIndicator]
    ring
  refine ⟨hscorei, hcenter, ?_⟩
  intro Past hPG hpPast
  exact centered_past (m₀ := m₀) (μ := μ) hPG hG0 _ _ hscorei
    (covarianceTheta_stronglyMeasurable (m₀ := m₀) (G := Past) p θ i hpPast) hcenter

end Conditional

end Part2.CNDPhysical

/-! Exhaustive axiom queries: all public theorem declarations in this staging module. -/
#print axioms Part2.CNDPhysical.cappedQueue_range
#print axioms Part2.CNDPhysical.atomic_paired_reconstruction
#print axioms Part2.CNDPhysical.cell_round_error
#print axioms Part2.CNDPhysical.cell_round_range
#print axioms Part2.CNDPhysical.cell_error_bound
#print axioms Part2.CNDPhysical.cell_endpoints
#print axioms Part2.CNDPhysical.physical_residual
#print axioms Part2.CNDPhysical.quadratic_eq_dot
#print axioms Part2.CNDPhysical.covariance_quadratic
#print axioms Part2.CNDPhysical.covariance_variance
#print axioms Part2.CNDPhysical.covariance_posSemidef
#print axioms Part2.CNDPhysical.information_posDef
#print axioms Part2.CNDPhysical.actual_resistance_isCND
#print axioms Part2.CNDPhysical.actual_resistance_potential_convex
#print axioms Part2.CNDPhysical.c0_pos
#print axioms Part2.CNDPhysical.saturation_normalized
#print axioms Part2.CNDPhysical.saturatedRadius_bounds
#print axioms Part2.CNDPhysical.contrast_sum
#print axioms Part2.CNDPhysical.gramDistance_energy
#print axioms Part2.CNDPhysical.actual_resistance_nonneg
#print axioms Part2.CNDPhysical.covariance_mul_ones
#print axioms Part2.CNDPhysical.information_mul_ones
#print axioms Part2.CNDPhysical.inverseInformation_mul
#print axioms Part2.CNDPhysical.inverseInformation_mul_ones
#print axioms Part2.CNDPhysical.inverseInformation_preserves_zero_sum
#print axioms Part2.CNDPhysical.tangentInformation_on_zero_sum
#print axioms Part2.CNDPhysical.inverse_tangent_direction
#print axioms Part2.CNDPhysical.actual_resistance_contrast_equation
#print axioms Part2.CNDPhysical.pairRadius_nonneg
#print axioms Part2.CNDPhysical.actual_saturated_radius_geometry
#print axioms Part2.CNDPhysical.weighted_second_moment_bound
#print axioms Part2.CNDPhysical.probability_bounds
#print axioms Part2.CNDPhysical.feature_bound
#print axioms Part2.CNDPhysical.direction_feature_bound
#print axioms Part2.CNDPhysical.physical_residual_bound
#print axioms Part2.CNDPhysical.physical_direction_increment_bound
#print axioms Part2.CNDPhysical.categorical_orthogonality
#print axioms Part2.CNDPhysical.roundBit_measurable
#print axioms Part2.CNDPhysical.conditional_cell_error_zero
#print axioms Part2.CNDPhysical.conditional_orthogonal_center
#print axioms Part2.CNDPhysical.covarianceTheta_stronglyMeasurable
#print axioms Part2.CNDPhysical.centered_past
#print axioms Part2.CNDPhysical.physical_conditional_center
